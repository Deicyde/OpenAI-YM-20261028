import YM.UVExtension.Lamppost.Loom
import YM.Push.ABSOLUTE_SUMS.Basic

/-! # Probe tests retaining the support currency. Include unused slot
      and real linear "finger" versions for linear price migration.
      Real-to-complex normalization loses numeric factors here. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Filter Metric Topology Set BoundedContinuousFunction Complex
open RG Push.AbsoluteSums
open scoped BigOperators ContDiff Classical
variable {A B : Type*}
universe u
structure Meter (A B : Type*) where
    test : A→Type u
    cost : B→A→ℝ
    nonneg : ∀ i j,0 ≤ cost i j
    awake : ∀ i:A,∃ j,0 < cost j i
namespace Meter
variable (M : Meter A B)
abbrev Slot:= (i:A)→ M.test i→ℝ
abbrev CSlot:= (i:A)→ M.test i→ℂ
structure MeasureP {E : Type*} [Norm E] (f:(i:A)→ M.test i→ E) (d : ℝ) : Prop where
    afloat : ∃ b:A→ℝ, (∀ i, 0 ≤ b i∧∀ x,‖f i x‖≤ b i) ∧ ∀ i:B,SumBudget (fun j=> M.cost i j*b j) d

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def padding {E:Type*} [Zero E] (f:(i:A)→ M.test i→ E) (t:(i:A)→Option (M.test i)) (i:A) := Option.elim' 0 (f i) (t i)
structure Finger where
    root : B
    frames : Finset A
    engage : (i:A)→Option (M.test i)
    cash : A→ℝ
    coin (i) : |cash i| ≤1

def Finger.effect (w:M.Finger) (f:M.Slot) := ∑ i∈w.frames,M.cost w.root i * w.cash i * padding M f w.engage i

def Finger.issue (w:M.Finger) (f:M.CSlot) : ℂ := ∑ i∈w.frames,(M.cost w.root i:ℂ) * (w.cash i:ℂ) * padding M f w.engage i

private def pick (i : A) (m : M.test i) (j : A) : Option (M.test j) := if h:i=j then some (h ▸ m) else none

def single (i : A) (m : M.test i) (b:B) : M.Finger:= ⟨b,{i},pick M i m,fun _=>1, fun _=> abs_one.le⟩
lemma sel (i:A) (m:M.test i) (b:B) (f:M.Slot): Finger.effect M (single M i m b) f=M.cost b i*f i m:= by simp [Finger.effect,single,pick,padding]

lemma fare {f:M.Slot} {d : ℝ} (h:M.MeasureP f d) (t:M.Finger) : ‖Finger.effect M t f‖ ≤ d := by
  obtain ⟨b,hf,hb⟩:=h.afloat
  apply (norm_sum_le ..).trans; refine le_trans (Finset.sum_le_sum (g:=fun i=> M.cost t.root i*b i) (fun i _=>?_)) (budget_sum (hb _) _)
  have hp : ‖padding M f t.engage i‖≤ b i := by unfold padding; cases t.engage i; simpa using (hf i).1; exact (hf _).2 _
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (M.nonneg ..)]; exact mul_le_mul (mul_le_of_le_one_right (M.nonneg ..) (t.coin i)) hp (norm_nonneg _) (M.nonneg ..)
lemma spare {f:M.CSlot} {d : ℝ} (h:M.MeasureP f d) (t:M.Finger) : ‖Finger.issue M t f‖ ≤ d:= by
  obtain ⟨b,hf,hb⟩:=h.afloat
  apply (norm_sum_le ..).trans; refine le_trans (Finset.sum_le_sum (g:=fun i=> M.cost t.root i*b i) (fun i _=>?_)) (budget_sum (hb _) _)
  have hp : ‖padding M f t.engage i‖≤ b i := by unfold padding; cases t.engage i; simpa using (hf i).1; exact (hf _).2 _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (M.nonneg ..),Complex.norm_real]; exact mul_le_mul (mul_le_of_le_one_right (M.nonneg ..) (t.coin i)) hp (norm_nonneg _) (M.nonneg ..)
-- fixed anchor finite probes. real coefficients choose signs. 
lemma effect_finite (f:M.Slot) (d : ℝ) (h:∀ x,‖Finger.effect M x f‖≤d) (w:(i:A)→ Option (M.test i)) (S:Finset A) (x:B) : ∑ i∈ S,M.cost x i * ‖padding M f w i‖≤ d:= by
  let t i := if 0≤padding M f w i then (1:ℝ) else (-1:ℝ)
  let P:M.Finger:= ⟨x,S,w,t,fun _=> by unfold t; split <;> simp⟩; have hh := h P
  have he : ∀ i,M.cost x i*‖padding M f w i‖= M.cost x i*t i* padding M f w i := by
    intro i; unfold t; split; next hp=> rw [Real.norm_of_nonneg hp,mul_one]
    next hp=> rw [Real.norm_of_nonpos (le_of_not_ge hp)]; ring
  apply le_trans (Real.le_norm_self _); simp_rw [he]; exact hh

-- simultaneous sup / weighted sum
lemma perches (f:(i:A)→ M.test i→ E)(d:ℝ)(h:∀ w S x, ∑ i∈ S,M.cost x i*‖padding M f w i‖≤d): M.MeasureP f d:=by
  let g i(t: Option (M.test i)):= ‖Option.elim' 0 (f i) t‖
  have he i (b:B) (v):M.cost b i*g i v ≤d:= by
    specialize h (Function.update (fun j=>none) i v) {i} b; simpa only [Finset.sum_singleton,padding,Function.update_self] using! h
  have hh i:BddAbove (range (g i)):=by obtain ⟨j,hj⟩:=M.awake i; exact ⟨d/M.cost j i,forall_mem_range.mpr (fun v=> (le_div_iff₀ hj).mpr ((mul_comm ..).trans_le (he i j v)))⟩
  let c i:=sSup (range (g i)); have hp i v:g i v ≤ c i:= le_csSup (hh i) (mem_range_self _)
  have hg i:0≤ c i:= le_trans (b:=g i none) (norm_nonneg _) (hp i none)
  refine ⟨c,fun i=> ⟨hg i,fun k=> hp i (some k)⟩,fun i=> budget_of_sum (fun j=>mul_nonneg (M.nonneg ..) (hg _)) ?_⟩
  -- vary finitely many w's, uniform sup separate
  intro S
  have hV(a:A): ∃ z:ℕ→Option (M.test a), Tendsto (fun i=> g a (z i)) atTop (𝓝 (c a)):=by
    have hc: c a ∈ closure (range (g a)):= csSup_mem_closure (Set.range_nonempty _) (hh a)
    obtain ⟨f,hf,h⟩:= mem_closure_iff_seq_limit.mp hc; choose z hz using hf
    exact ⟨z,h.congr' (Eventually.of_forall fun i=>(hz i).symm)⟩
  choose z hV using hV
  have H n:∑ j∈S,M.cost i j*g j (z j n)≤d:= h (fun j=> z j n) _ _
  exact le_of_tendsto (tendsto_finset_sum _ fun j hj=>(hV j).const_mul (M.cost i j)) (Eventually.of_forall H)

lemma clips_real (f:M.Slot)(d:ℝ)(h:∀ x,‖Finger.effect M x f‖≤d): M.MeasureP f d:=M.perches _ d (M.effect_finite f d h)
lemma combines {K:Type*} {c:K→M.Slot} {b:K→ℝ} (s:Finset K) (q:M.Finger): Finger.effect M q (fun i j=>∑ k∈s,b k*c k i j)=∑ k∈s,b k*Finger.effect M q (c k):= by
  unfold Finger.effect
  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  unfold padding; cases q.engage i; simp only [Option.elim']; simp; dsimp only [Option.elim']; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> (by ring)

lemma c_clips (f:M.CSlot) (d:ℝ)(h:∀ x,‖Finger.issue M x f‖≤d): M.MeasureP f (d+d):=by
  let g i k:= (f i k).re; let b i k:=(f i k).im
  have hr q:Complex.re (Finger.issue M q f)=Finger.effect M q g:= by
    unfold Finger.effect Finger.issue; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold padding; cases q.engage i <;> simp [g]
  have hx q:Complex.im (Finger.issue M q f)=Finger.effect M q b:= by
    unfold Finger.effect Finger.issue; rw [Complex.im_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold padding; cases q.engage i <;> simp [b]
  obtain ⟨v,hv,hV⟩:= (M.clips_real g d (fun i=> by rw [← hr i]; exact (Complex.abs_re_le_norm _).trans (h i))).afloat
  obtain ⟨u,hu,hU⟩:= (M.clips_real b d (fun i=> by rw [← hx i]; exact (Complex.abs_im_le_norm _).trans (h i))).afloat
  refine ⟨fun i=> v i+u i,fun i=> ⟨add_nonneg (hv i).1 (hu i).1,fun j=>(Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add ((hv i).2 j) ((hu i).2 j))⟩,fun i=>?_⟩
  simpa only [mul_add] using! budget_plus (hV i) (hU i)

end Meter
end YM.UVExtension.Lamppost
