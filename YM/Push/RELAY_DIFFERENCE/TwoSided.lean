import YM.Next.EXTRACTION.Tails
import YM.Work.B06

/-!
# Quantitative reorientation of left-derivative estimates

At a sign-reversing copy, negative links may require RIGHT derivatives;
naive equivariance of the orders & bounds is not available. On many
iterations naive differentiations of field-dependent Ad can also be
very expensive -- may want an extra power of support price. Here obtain
a reorientation estimate via commuting the derivatives FIRST. Only for
germs with the actual `BudgetPoint.Regular` smoothness near each healthy
point, evaluation before indicators. Factors explicitly in the
bounds consuming these lemmas (no extra derivative or support orders!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.TwoSided
open Function Set Filter MeasureTheory Wilson RG Lattice Cells Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}

abbrev Move (G : Gauge) (n : Side) := Directions G n × Directions G n

def l (x : Directions G n) : Move G n := (x,0)
def r (x : Directions G n) : Move G n := (0,x)
def vary (U : Config G n) (k : Move G n) : Config G n := fun e => G.lieExp (k.1 e)*U e*G.lieExp (k.2 e)

lemma vary_zero (U : Config G n) : vary U 0=U := by ext1 i; simp [vary]
lemma vary_l (U : Config G n) (x : Directions G n) (t : ℝ) : vary U (t • l x)=increment U (t • x) := by
  ext1 i; simp only [vary,l,Prod.smul_fst,Prod.smul_snd, smul_zero,Pi.zero_apply,G.mat_lieExp_zero,mul_one]; rfl

def op (p : Config G n → ℂ) (x : Move G n) (U : Config G n) : ℂ := deriv (fun t : ℝ => p (vary U (t • x))) 0

def mult (f : Config G n → ℂ) : List (Move G n) → Config G n → ℂ
  | [] => f
  | x :: p => op (mult f p) x

lemma lefts (f : Config G n → ℂ) (p : List (Directions G n)) : mult f (p.map l)=leftDerivs f p := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [List.map_cons,mult, ih]; unfold op; simp_rw [vary_l]; rfl

/-- Chart programming for smoothness with nearby points where the flags
may change. -/
def Based (U : Config G n) (f : Config G n → ℂ) (k : ℕ) :=
    ContDiffAt ℝ (k : WithTop ℕ∞) (f ∘ increment U) 0

variable {U : Config G n} {f : Config G n → ℂ} {k d : ℕ}

lemma Based.less (H : Based U f k) (he : d ≤ k) : Based U f d :=
  ContDiffAt.of_le H (Nat.cast_le.mpr he)

section Germ
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Composition allowed with k-smooth matrix paths. -/
theorem Based.from (h : Based U f k) {F : X → Config G n} {o : X} (ho : F o=U) (hh : ContinuousAt F o)
    (hr : ∀ i, ContDiffAt ℝ (k : WithTop ℕ∞) (fun x => G.mat (F x i)) o) : ContDiffAt ℝ k (f ∘ F) o := by
  let q (x : X) : Directions G n := fun i => G.plog (G.mat (F x i * (U i)⁻¹))
  have hq : q o=0 := by funext i; simp only [q,ho,mul_inv_cancel]; simp
  have hp : ContDiffAt ℝ k q o := by
    refine contDiffAt_pi.mpr fun i => ?_
    have hd : ContDiffAt ℝ k (fun x => G.mat (F x i *(U i)⁻¹)) o := (hr i).mul contDiffAt_const
    have ht : G.mat (F o i*(U i)⁻¹) = 1 := by simp [ho]
    exact ((ht.symm ▸ G.plog_diff).of_le le_top).comp (f:=fun x => G.mat (F x i*(U i)⁻¹)) o hd
  have hF (i) : ∀ᶠ x in 𝓝 o,F x i=increment U (q x) i := by
    let p (x) := F x i*(U i)⁻¹
    have hx : Tendsto p (𝓝 o) (𝓝 1) := by
      rw [← show p o=1 by simp [p,ho]]
      exact (((continuous_apply i).continuousAt.comp hh).mul continuousAt_const : ContinuousAt p o)
    filter_upwards [hx.eventually G.plog_right] with x hh
    change F x i = G.lieExp (G.plog (G.mat (p x))) * U i
    rw [hh]; unfold p; group
  have h : ContDiffAt ℝ k (f ∘ increment U) (q o) := hq.symm ▸ h
  apply ContDiffAt.congr_of_eventuallyEq (h.comp o hp)
  filter_upwards [eventually_all.mpr hF] with x hx using congr_arg f (funext (hx ·))
end Germ

@[fun_prop] lemma continuous_vary : Continuous (fun p : Config G n × Move G n => vary p.1 p.2) := by
  unfold vary; fun_prop

lemma cont_both (h : Based U f k) : ContDiffAt ℝ k (f ∘ vary U) 0 :=
  h.from (vary_zero U) ((continuous_vary.comp (continuous_const.prodMk continuous_id)).continuousAt)
    (fun i => by simp only [vary,G.mat_mul]; exact
        (((G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_fst)).mul contDiff_const).mul (G.exp_jet.comp
          ((contDiff_apply ℝ G.Color i).comp contDiff_snd))).contDiffAt.of_le le_top)

private lemma cont_after (A : Move G n) (h : Based U f k) : ContDiffAt ℝ k
    (fun x : ℝ × Directions G n => f (increment (vary U (x.1 • A)) x.2)) 0 := by
  refine Based.from (F:=fun x : ℝ × Directions G n => increment (vary U (x.1 • A)) x.2) h ?_ ?_ (fun i => ?_)
  · rw [show ((0:ℝ × Directions G n).1)=0 from rfl,zero_smul,vary_zero]; ext1 i; simp [increment]
  · unfold increment vary; fun_prop
  simp only [increment,vary,Prod.smul_fst,Prod.smul_snd,G.mat_mul,Pi.smul_apply]
  exact (((G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_snd)).mul
      (((G.exp_jet.comp (contDiff_fst.smul contDiff_const)).mul contDiff_const).mul
        (G.exp_jet.comp (contDiff_fst.smul contDiff_const)))).contDiffAt).of_le le_top

/-- Local licenses for repeated commuting/reorientation. -/
lemma Based.moves (A : Move G n) (H : Based U f k) : ∀ᶠ x : ℝ in 𝓝 0,Based (vary U (x • A)) f k := by
  have he : Tendsto (fun x : ℝ => (x, (0:Directions G n))) (𝓝 0) (𝓝 0) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [he.eventually ((cont_after A H).eventually (by simp))] with i hi
  exact hi.comp 0 (f:=fun x => (i,x)) (by fun_prop)

/-- Near in the other order. -/
lemma Based.part (A : Move G n) (h : Based U f (k+1)) : Based U (op f A) k := by
  let V (v : Directions G n) (s : ℝ) := f (vary (increment U v) (s • A))
  have hu : ContDiffAt ℝ (↑(k+1:ℕ)) (uncurry V) 0 := by
    refine Based.from (F:=fun x : Directions G n × ℝ => vary (increment U x.1) (x.2 • A)) h ?_ ?_ (fun i => ?_)
    · rw [show (0:Directions G n × ℝ).2=0 from rfl,zero_smul,vary_zero]; ext1 i; simp [increment]
    · unfold vary increment; fun_prop
    simp only [increment, vary,G.mat_mul, Prod.smul_fst,Prod.smul_snd, Pi.smul_apply]
    have ht : ContDiff ℝ ω (fun x : Directions G n × ℝ => G.mat (vary (increment U x.1) (x.2 • A) i)) :=
      (((G.exp_jet.comp (contDiff_snd.smul contDiff_const)).mul
        ((G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_fst)).mul contDiff_const)).mul
        (G.exp_jet.comp (contDiff_snd.smul contDiff_const)))
    exact ht.contDiffAt.of_le le_top
  change ContDiffAt ℝ k (fun x => fderiv ℝ (V x) 0 1) 0
  exact (hu.fderiv (f:=V) (g:=fun _ => 0) (m:=↑k) contDiffAt_const (by push_cast; rfl)).clm_apply
    (g:=fun _ => (1:ℝ)) contDiffAt_const

lemma Based.series (q : List (Move G n)) (h : Based U f (k+q.length)) : Based U (mult f q) k := by
  induction q generalizing k with
  | nil => exact h
  | cons a q ih => exact (ih (k:=k+1) (by simpa [add_comm,add_left_comm,add_assoc] using h)).part _

lemma Based.approach (h : Based U f 1) (x : Move G n) :
    HasDerivAt (fun t : ℝ => f (vary U (t • x))) (fderiv ℝ (f ∘ vary U) 0 x) 0 := by
  have hv : DifferentiableAt ℝ (f ∘ vary U) 0 := (cont_both h).differentiableAt (by simp)
  let u (t : ℝ) := t • x
  have he : HasDerivAt u x 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0:ℝ)).smul_const x
  have hx : u 0=0 := zero_smul ..
  have ht := (show HasFDerivAt (f ∘ vary U) (fderiv ℝ (f ∘ vary U) 0) (u 0) from hx.symm ▸ hv.hasFDerivAt).comp_hasDerivAt 0 he
  exact ht
lemma Based.split (h : Based U f 1) (A : Move G n) : op f A U=op f (l A.1) U+op f (r A.2) U := by
  unfold op; rw [(h.approach A).deriv,(h.approach (l _)).deriv,(h.approach (r _)).deriv,←map_add,show l A.1 + r A.2=A from Prod.ext (add_zero _) (zero_add _)]

/-! ### Commute in either direction, BEFORE differentiating again -/

section Scalar
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private lemma twist (Y : X → ℂ) (u v : X) (h : ContDiffAt ℝ 2 Y 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Y (t • u+s • v)) 0) 0 =
    (fderiv ℝ (fderiv ℝ Y) 0 u) v := by
  let w (t : ℝ) := t • u
  let q (t : ℝ) := fderiv ℝ Y (w t)
  have he : (fun t : ℝ => deriv (fun s : ℝ => Y (w t+s • v)) 0) =ᶠ[𝓝 0] fun t => q t v := by
    have hu : Tendsto w (𝓝 0) (𝓝 0) := by
      rw [← show w 0=0 from zero_smul ..]; exact (show Continuous w by unfold w; fun_prop).tendsto _
    filter_upwards [hu.eventually (h.eventually (by norm_num))] with i hi
    let p (s : ℝ) := w i + s • v
    have hw : p 0=w i := by unfold p; simp
    have hv : HasDerivAt p v 0 := by
      simpa [p] using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add (w i)
    have hx := ((hw.symm ▸ hi).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hv
    have hz : q i = fderiv ℝ Y (p 0) := by rw [hw]
    rw [hz]; exact hx.deriv
  have hf : ContDiffAt ℝ 1 (fderiv ℝ Y) 0 := h.fderiv_right (by norm_num)
  have hx : HasDerivAt w u 0 := by simpa [w] using (hasDerivAt_id' (0:ℝ)).smul_const u
  have hy : w 0=0 := zero_smul ..
  have ht : HasFDerivAt (fderiv ℝ Y) (fderiv ℝ (fderiv ℝ Y) 0) (w 0) := hy.symm ▸ (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hv := (ht.comp_hasDerivAt 0 hx).clm_apply (hasDerivAt_const 0 v)
  exact he.deriv_eq.trans (by simpa using hv.deriv)
end Scalar

lemma vary_pair (A B : Directions G n) (t s : ℝ) :
    vary (vary U (t • l A)) (s • r B) = vary U (t • l A+s • r B) ∧
    vary (vary U (s • r B)) (t • l A) = vary U (s • r B+t • l A) := by
  constructor <;> ext1 i <;> simp [vary,l,r,mul_assoc]

lemma Based.commutes (h : Based U f 2) (A B : Directions G n) : op (op f (r B)) (l A) U=op (op f (l A)) (r B) U := by
  have hv : ContDiffAt ℝ 2 (f ∘ vary U) 0 := by simpa using cont_both h
  unfold op
  simp_rw [(vary_pair A B ..).1,(vary_pair A B ..).2]
  have ha := twist (f ∘ vary U) (l A) (r B) hv
  have hb := twist (f ∘ vary U) (r B) (l A) hv
  exact ha.trans ((hv.isSymmSndFDerivAt (by simp) _ _).trans hb.symm)

def recolor (U : Config G n) (A : Directions G n) : Directions G n := fun i => G.adjoint (U i) (A i)

/-- Convert ONLY at the point (doesn't cost field-variation of the Ad). -/
lemma exchange (U : Config G n) (p : Directions G n) : op f (r p) U=op f (l (recolor U p)) U := by
  have ht (t : ℝ) : vary U (t • r p) = vary U (t • l (recolor U p)) := by
    funext i
    simp only [l,r,recolor,vary,Prod.smul_fst,Prod.smul_snd,smul_zero, Pi.zero_apply,G.mat_lieExp_zero,
      one_mul, mul_one, Pi.smul_apply]
    rw [← map_smul]
    apply G.mat_injective
    simp only [G.mat_mul,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]
    simp only [Gauge.conjugate,mul_assoc,G.mat_star_mul,mul_one]
  unfold op; simp_rw [ht]
end YM.Push.RelayDifference.TwoSided
