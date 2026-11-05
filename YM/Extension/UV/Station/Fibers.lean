import YM.Extension.UV.Station.Stencil
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Lattice RG Precision Wilson Function Filter
open scoped Topology BigOperators Classical

deriving instance Countable for Step
deriving instance Fintype for Step
private noncomputable def s0 : Step:=⟨0,false⟩
deriving instance Countable for Slot
-- if Step not finite derive manually
abbrev Pattern (k:ℕ) := Fin k → Slot
lemma many_slots : Infinite Slot:= Infinite.of_injective (fun i:ℕ=>Slot.mk (List.replicate i s0) ⟨(0,1),by decide⟩) (by intro i j h; simpa using congr_arg (fun x : Slot=> x.walk.length) h)
noncomputable def slots (k:ℕ) [NeZero k]: ℕ ≃ Pattern k:=by
  letI := many_slots
  haveI : Infinite (Pattern k):= Infinite.of_injective (fun s:Slot=> fun _:Fin k=>s) (by intro i j h; exact congr_fun h 0)
  exact YM.Stationary.enumerate _

def fiber {κ H:Type*} [NormedAddCommGroup H] [CompleteSpace H] (a:ℕ→κ) (f:ℕ→H) (t:κ) := ∑' i:a⁻¹' {t}, f (i:ℕ)
lemma fiber_tsum {κ H:Type*} [NormedAddCommGroup H] [CompleteSpace H] (a:ℕ→κ) {f:ℕ→H} (h:Summable f): HasSum (fiber a f) (∑' i,f i) := h.hasSum.tsum_fiberwise a

lemma budget_minor {κ:Type*} {f g:κ→ℝ} {C:ℝ} (hf:∀ i,0≤f i) (hb:∀ i, f i ≤ g i) (h:SumBudget g C): SumBudget f C:=by
   have hx:=Summable.of_nonneg_of_le hf hb h.2.1; exact ⟨hf,hx,(hx.tsum_le_tsum hb h.2.1).trans h.2.2⟩
lemma fiber_budget {κ:Type*} (a:ℕ→κ) {f:ℕ→ℝ}{w:κ→ℝ}{C:ℝ} (hw:∀ t,0≤w t) (h:SumBudget (fun i=> |f i| * w (a i)) C): SumBudget (fun i=> |fiber a f i| *w i) C:=by
   let t (i:ℕ):=|f i| * w (a i)
   apply budget_minor (fun i=>mul_nonneg (abs_nonneg _) (hw _)) _ (g:=fiber a t)
   · exact ⟨fun u=> tsum_nonneg fun _=> h.1 _,(fiber_tsum a h.2.1).summable,(fiber_tsum a (f:=t) h.2.1).tsum_eq.trans_le h.2.2⟩ -- order
   intro u
   have he : |fiber a f u| *w u = |fiber a (fun i=>f i*w u) u| := by simp only [fiber]; rw [tsum_mul_right, abs_mul,abs_of_nonneg (hw u)]
   -- norm_tsum_le_tsum_norm
   have hi (u:κ) : Summable fun j:a⁻¹' {u}=>t (j:ℕ) := Summable.comp_injective h.2.1 Subtype.coe_injective
   apply he.le.trans
   let p:=fun j:a⁻¹' {u}=> f j*w u
   have he j : ‖p j‖ = t j:= by simp only [p,t,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hw _)]; exact (congr_arg (fun z=>|f ↑j| *w z) (show a (j:ℕ)=u from j.2)).symm
   exact (norm_tsum_le_tsum_norm (show Summable (fun j=>‖p j‖) by exact (hi u).congr (fun j=>(he j).symm))).trans_eq (tsum_congr he)
lemma budget_sum {κ J : Type*} [Fintype J] (f:κ→J→ℝ) {a:J→ℝ} (hr:∀ j, SumBudget (fun i=>f i j) (a j)): SumBudget (fun i=>∑ j, f i j) (∑ j,a j):=by
   refine ⟨fun _=>Finset.sum_nonneg (fun j _=> (hr j).1 _),summable_sum fun j _=> (hr j).2.1,?_⟩
   rw [Summable.tsum_finsetSum (fun j _=> (hr j).2.1)]
   exact Finset.sum_le_sum fun j _=> (hr j).2.2

variable {k:ℕ} {G:Gauge}
def pat_len (s:Pattern k):=∑ i,(s i).length
def pat_coeff (a:ℕ→Atom G k) (s:Pattern k) (b : Fin k → G.ColorIndex) :=fiber (fun i=>(a i).leg) (fun i=> (a i).coeff b) s
variable [NeZero k]
def reatom (a:ℕ→Atom G k):ℕ→Atom G k :=fun i=> ⟨slots k i,pat_coeff a (slots k i)⟩
lemma reatom_wall (a:ℕ→Atom G k) {C σ:ℝ} (h:SumBudget (fun i=> (a i).budget σ) C): SumBudget (fun i=> (reatom a i).budget σ) C:=by
 let Q:= Fin k→G.ColorIndex
 let g b i:= |(a i).coeff b| *Real.exp (σ*(a i).length)
 have he: (fun i=> ∑ b:Q,g b i)=fun i=> (a i).budget σ:= by funext i; rw [Atom.budget, Atom.magnitude,← Finset.sum_mul]
 have hl i b: g b i ≤ (a i).budget σ:= by unfold Atom.budget Atom.magnitude; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _=>abs_nonneg ((a i).coeff j)) (Finset.mem_univ b)) (Real.exp_nonneg _)
 have ht b:= budget_minor (fun i=> show 0≤g b i from by unfold g; positivity) (fun i=>hl _ b) h
 let t : Q → ℝ := fun b=>∑' i,g b i
 have hx b: SumBudget (g b) (t b):= ⟨(ht b).1,(ht b).2.1,le_rfl⟩
 -- fiber reorganization
 let L (s:Pattern k) (b:Q):= |pat_coeff a s b| * Real.exp (σ*pat_len s)
 have hv b : SumBudget (L · b) (t b):=fiber_budget (fun i=> (a i).leg) (w:=fun s=>Real.exp (σ*pat_len s)) (by exact fun _=>Real.exp_nonneg _) (hx b)
 have H0:=YM.Stationary.budget_copy (slots k) (budget_sum L hv)
 have hi: (∑ b : Q,t b) ≤ C:= by unfold t; rw [← Summable.tsum_finsetSum fun b _=> (ht b).2.1, he]; exact h.2.2
 have hd : (fun i=> (reatom a i).budget σ)=(fun s=>∑ b,L s b) ∘ (slots k):=by
    funext i; simp only [Atom.budget,Atom.magnitude,Finset.sum_mul]; try rfl
 rw [hd]; exact ⟨H0.1,H0.2.1,H0.2.2.trans hi⟩

section atoms
variable (a:ℕ→Atom G k) {u v : ℝ} (hu:0≤u) (h:SumBudget (fun i=>(a i).budget u) v)
include h hu
omit [NeZero k] in
lemma coeff_price b: SumBudget (fun i=> |(a i).coeff b|) v:=by
   refine budget_minor (fun _=>abs_nonneg _) (fun i=>?_ ) h
   unfold Atom.budget
   exact (Finset.single_le_sum (fun b _=> abs_nonneg ((a i).coeff b)) (Finset.mem_univ b)).trans (le_mul_of_one_le_right (by exact Finset.sum_nonneg fun _ _=>abs_nonneg _) (Real.one_le_exp (mul_nonneg hu (Nat.cast_nonneg _))))
omit h hu [NeZero k] in
lemma fiber_summable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H] {t:ℕ→H} (ht:Summable t) (s:Pattern k): Summable fun j:{i // (a i).leg=s}=> t j:= ht.comp_injective Subtype.coe_injective
omit [NeZero k] in
lemma unmasked_series {n} (U:Config G n) (x): Summable fun i=>(a i).unmasked U x:=by
   have H:=h.2.1.mul_right (2^k)
   apply H.of_norm_bounded
   exact fun i=> show |(a i).unmasked U x| ≤ _ from (Atom.unmasked_bound ..).trans (by unfold Atom.budget; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by unfold Atom.magnitude; exact Finset.sum_nonneg fun _ _=>abs_nonneg _) (Real.one_le_exp (by positivity))) (by positivity))
lemma poly_series i (U:Fin k→G.Color) : Summable (fun j:{j// (a j).leg=slots k i}=> (a j).poly U) := by
   unfold Atom.poly; exact summable_sum fun b _=> fiber_summable a ((coeff_price a hu h b).2.1.of_norm.mul_right (∏ i,U i (b i))) (slots k i)

lemma reatom_poly i w: (reatom a i).poly w = ∑' j:{j//(a j).leg=slots k i}, (a j).poly w := by
   dsimp only [reatom,pat_coeff,Atom.poly,fiber]
   rw [Summable.tsum_finsetSum (fun b _=> fiber_summable a ((coeff_price a hu h b).2.1.of_norm.mul_right (∏ i,w i (b i))) _)]
   refine Finset.sum_congr rfl fun b _=>?_
   rw [tsum_mul_right]
   rfl
lemma reatom_unmasked {n} (U:Config G n) (x) i : (reatom a i).unmasked U x = ∑' j:{j//(a j).leg=slots k i}, (a j).unmasked U x:=by
   rw [Atom.unmasked,reatom_poly a hu h]
   refine tsum_congr fun j=> ?_
   unfold Atom.unmasked
   exact congr_arg _ (funext fun s=> by rw [j.2]; rfl)
lemma reatom_invariant (hi:∀ i,(a i).Invariant) i : (reatom a i).Invariant := by
   intro k x; simp_rw [reatom_poly a hu h]; apply tsum_congr; intro i; apply hi
lemma reatom_uncut {n} (U:Config G n): uncut (reatom a) U=uncut a U := by
   apply Finset.sum_congr rfl; intro x _
   have he := (fiber_tsum (fun i=>(a i).leg) (unmasked_series a hu h U x)).tsum_eq
   refine Eq.trans ?_ (((slots k).tsum_eq (fiber (fun i=>(a i).leg) (fun i=>(a i).unmasked U x))).trans he)
   exact tsum_congr (fun i=>by exact reatom_unmasked a hu h U x i)
end atoms
end YM.Extension.UV.StationaryData
