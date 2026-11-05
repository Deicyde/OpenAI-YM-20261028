import YM.Further.CURVED_GAUSSIAN_JETS.Jets

/-!
# Paying an ordered left jet under ∫ / ∑'

Real column version, Bochner. Needs an actual neighborhood of all the
estimates; finite V halo switching identities therefore not automatic!
One majorant at each order around that point, not dominance on difference
quotients assumed. ok-set only in integration VARIABLE (e.g. u>0), same
for every V and thrown away only under the integral, never by weakening
a physical hard indicator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Lattice Wilson RG Precision Multi.Puff
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {n : Side} {G : Gauge}
-- As in Next.Foundations.TestBounds, now used in mixed left words
private theorem shift (U : Config G n) (A : Directions G n) (s t : ℝ) :
    increment (increment U (t • A)) (s • A)=increment U ((s+t) • A) := by
  funext i; apply G.mat_injective
  simp only [increment,G.mat_mul,Pi.smul_apply,G.mat_lieExp,map_smul,add_smul,map_add,←mul_assoc]
  congr 1
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm
lemma at_shift (U : Config G n) (A : Directions G n) {g : Config G n → ℝ} {x t : ℝ}
    (h : HasDerivAt (fun s : ℝ => g (increment (increment U (t • A)) (s • A))) x 0) :
    HasDerivAt (fun s : ℝ=> g (increment U (s • A))) x t := by
  rw [←add_neg_cancel t] at h
  simpa only [shift,neg_add_cancel_right] using h.comp_add_const t (-t)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → Config G n → ℝ} {D : Set X}
    {Q : Directions G n → Prop} {U : Config G n} {k : ℕ} {M : ℕ → X → ℝ}
structure Terms (μ : Measure X) (D : Set X) (Q : Directions G n → Prop) (f : X → Config G n → ℝ) (k : ℕ) (M : ℕ → X → ℝ) (V : Config G n) : Prop where
  meas (l : Word G n) : l.length≤k → (∀ i∈l,Q i) → AEStronglyMeasurable (fun x => leftDerivs (f x) l V) μ
  major (l : Word G n) : l.length≤k → (∀ i∈l,Q i) → ∀ x∈D, ‖leftDerivs (f x) l V‖ ≤ M l.length x
  live (l : Word G n) : l.length<k → (∀ i∈l,Q i) → ∀ d : Directions G n, Q d → ∀ x∈D, HasDerivAt (fun t : ℝ=> leftDerivs (f x) l (increment V (t • d))) (leftDerivs (f x) (d::l) V) 0

def total (μ : Measure X) (f : X → Config G n → ℝ) (V : Config G n) := ∫ x, f x V ∂μ
variable (he : ∀ᵐ x ∂μ, x∈D) (hm : ∀ i≤k,Integrable (M i) μ)
    (h : ∀ᶠ V in 𝓝 U, Terms μ D Q f k M V)
include he hm
lemma Terms.integrable (hv : Terms μ D Q f k M U) {l : Word G n} (hl : l.length≤k) (hd : ∀ i∈l,Q i) :
    Integrable (fun x => leftDerivs (f x) l U) μ := (hm _ hl).mono' (hv.meas _ hl hd) (he.mono (hv.major _ hl hd))
include h
lemma line_deriv {l : Word G n} (hl : l.length<k) (hd : ∀ i∈l,Q i) {d : Directions G n} (hq : Q d) :
    HasDerivAt (fun t : ℝ => ∫ x, leftDerivs (f x) l (increment U (t • d)) ∂μ) (∫ x, leftDerivs (f x) (d::l) U ∂μ) 0 := by
  let F' (t : ℝ) x := leftDerivs (f x) (d::l) (increment U (t • d))
  let s := {t : ℝ | Terms μ D Q f k M (increment U (t • d))}
  have hs : s ∈ 𝓝 (0:ℝ) := (Multi.Puff.swing U d).eventually h
  have hh (t : ℝ) (ht : t∈s) : Terms .. := ht
  have hx : ∀ i∈d::l,Q i := by simpa [hq]
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F':=F') hs
    (((Multi.Puff.swing U d).eventually h).mono fun t ht => ht.meas _ hl.le hd)
    (show Integrable _ μ from by simpa [inc_zero] using h.self_of_nhds.integrable he hm hl.le hd)
    (show AEStronglyMeasurable (F' 0) μ from by simpa [F',inc_zero] using h.self_of_nhds.meas (d::l) hl hx)
    (he.mono fun x hx'=> fun t ht=> (hh t ht).major (d::l) hl hx x hx') (hm _ hl)
    (he.mono fun x hx'=> fun t ht=> at_shift U d ((hh t ht).live _ hl hd d hq x hx')) |>.2
  simpa only [F',zero_smul, inc_zero] using hi
lemma inside_total {l : Word G n} (hl : l.length≤k) (hd : ∀ i∈l,Q i) : leftDerivs (total μ f) l U = ∫ x, leftDerivs (f x) l U ∂μ := by
  induction l generalizing U with
  | nil => rfl
  | cons d l ih =>
    obtain ⟨hq,ht⟩ := List.forall_mem_cons.mp hd
    exact ((line_deriv he hm h hl ht hq).congr_of_eventuallyEq (((Multi.Puff.swing U d).eventually h.eventually_nhds).mono fun t hv => ih hv (Nat.le_of_succ_le hl) ht)).deriv
lemma live_total {l : Word G n} (hl : l.length<k) (hd : ∀ i∈l,Q i) {d : Directions G n} (hq : Q d) :
    HasDerivAt (fun t : ℝ => leftDerivs (total μ f) l (increment U (t • d))) (leftDerivs (total μ f) (d::l) U) 0 := by
  rw [inside_total he hm h (l:=d::l) hl (List.forall_mem_cons.mpr ⟨hq,hd⟩)]
  exact (line_deriv he hm h hl hd hq).congr_of_eventuallyEq (((Multi.Puff.swing U d).eventually h.eventually_nhds).mono fun t hv => inside_total he hm hv hl.le hd)
lemma paid_total {l : Word G n} (hl : l.length≤k) (hd : ∀ i∈l,Q i) : ‖leftDerivs (total μ f) l U‖ ≤ ∫ x, M l.length x ∂μ := by
  rw [inside_total he hm h hl hd]; exact (norm_integral_le_integral_norm _).trans (integral_mono_ae
      (h.self_of_nhds.integrable he hm hl hd).norm (hm _ hl) (he.mono (h.self_of_nhds.major _ hl hd)))
omit he hm h
section infinite
variable {f : ℕ → Config G n → ℝ} {M : ℕ → ℕ → ℝ} (hM : ∀ i≤k, Summable (M i))
    (hh : ∀ᶠ V in 𝓝 U,Terms Measure.count univ Q f k M V)
private lemma counting {f : ℕ → ℝ} (h : Integrable f Measure.count) : ∫ x, f x ∂Measure.count = ∑' x,f x := by
  simp [integral_countable h,Measure.real]
lemma left_on {f g : Config G n → ℝ} (h : f =ᶠ[𝓝 U] g) (l : Word G n) : leftDerivs f l U=leftDerivs g l U := by
  let A U := Matrix.of fun (_ _ : Unit) => f U
  let B U := Matrix.of fun (_ _ : Unit) => g U
  have he := jet_eq (l:=l) (A:=A) (B:=B) (h.mono fun v hv=>Matrix.ext fun i j => hv)
  exact congr_fun (congr_fun he ()) ()
include hM hh
lemma inside_infinite {l : Word G n} (hl : l.length≤k) (hd : ∀ i∈l,Q i) :
    leftDerivs (fun V => ∑' j,f j V) l U = ∑' j,leftDerivs (f j) l U ∧ Summable (fun j=>leftDerivs (f j) l U) ∧
      ∑' j, ‖leftDerivs (f j) l U‖ ≤ ∑' j, M l.length j := by
  have hm (i) (hi : i≤k) : Integrable (M i) Measure.count := integrable_count_iff.mpr (hM i hi).norm
  have he : ∀ᵐ j : ℕ ∂Measure.count, j∈(univ : Set ℕ) := Eventually.of_forall (fun _=>trivial)
  have hi := hh.self_of_nhds.integrable he hm hl hd
  have hs := integrable_count_iff.mp hi
  refine ⟨?_,hs.of_norm, hs.tsum_le_tsum (fun x=>hh.self_of_nhds.major l hl hd x trivial) (hM _ hl)⟩
  apply Eq.trans _ ((inside_total he hm hh hl hd).trans (counting hi))
  apply left_on; filter_upwards [hh] with V hv
  exact (counting (hv.integrable he hm (l:=[]) (by simp) (by simp))).symm
end infinite
end YM.Further.CurvedGaussianJets.Jets
