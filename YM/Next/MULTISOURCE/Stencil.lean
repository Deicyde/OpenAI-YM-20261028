import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Ac.Table
import YM.Analysis.SmoothJets
import YM.Bid.Fuels
import YM.Next.MULTISOURCE.Bulk



/-!
# Uniform stencil income from existing single-source history

Only tests section at its given finite orders. Sum basis presentations in
that price (don't conclude a regularity assertion on pointwise sums at
threshold equality). -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Maquette

open RG Wilson Lattice Function Filter Finset Source Labels 
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} (X : SectionData F)

def maxgrade (F : Frame G d) := Finset.univ.sup fun i => (F.grades i).2

private lemma basis_bound (i : F.Index) : ∃ y : ℝ, 1 ≤ y ∧
    ∀ U : CoverConfig G, ‖X.evaluate (Pi.single i 1) U‖ ≤ y := by
  let f := X.evaluate (Pi.single i 1)
  obtain ⟨T,ht⟩ := IsCompact.bddAbove (isCompact_range (show Continuous fun x => ‖f x‖ from
    (X.continuous_evaluate _).norm))
  exact ⟨max 1 T,le_max_left ..,fun x => (ht ⟨x,rfl⟩).trans (le_max_right ..)⟩

def upper := 1+∑ i, (basis_bound X i).choose
lemma purposes (i : F.Index) : 1 ≤ upper X ∧ ∀ {n} (o : Site n) U, ‖X.places (Pi.single i 1) o U‖ ≤ upper X := by
  have he (i : F.Index) := (basis_bound X i).choose_spec
  have hp (i : F.Index) := zero_le_one.trans (he i).1
  refine ⟨le_add_of_nonneg_right (sum_nonneg fun i _ => hp i),fun {n} o U => ?_⟩
  exact ((he i).2 _).trans (le_trans (single_le_sum (fun i _ => hp i) (mem_univ i))
    (le_add_of_nonneg_left zero_le_one))

private def valuate (o : Site n) : F.Coeff →ₗ[ℂ] (Config G n → ℂ) where
  toFun x := X.places x o
  map_add' a b := by funext U; exact congr_fun (X.eval_linear.map_add a b) _
  map_smul' a b := by funext U; exact congr_fun (X.eval_linear.map_smul a b) _

lemma portions (v : F.Coeff) (o : Site n) : X.places v o=∑ i,v i • X.places (Pi.single i 1) o := by
  change valuate X o v=∑ i, v i • valuate X o (Pi.single i 1)
  simp_rw [← map_smul, ← map_sum]
  apply congrArg; funext i
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  simp

lemma maximum (g : ℝ) (hg : 0<g) (P : BudgetPoint) (h : g ≤ P.threshold) (o : Site n)
    (z : F.Coeff) (U : Config G n) :
    ‖X.places (F.scaled (P.threshold)⁻¹ z) o U‖ ≤ upper X*(g⁻¹)^maxgrade F * F.coeffSize z := by
  let Q := F.scaled (P.threshold)⁻¹ z
  have he (i : F.Index) : ‖Q i‖ ≤ (g⁻¹)^maxgrade F*‖z i‖ := by
    unfold Q; rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by
      have := P.threshold_pos; positivity)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hh : 1 ≤ P.threshold⁻¹ := one_le_inv₀ P.threshold_pos |>.mpr P.threshold_le
    exact (pow_le_pow_right₀ hh (Finset.le_sup (f:=fun i => (F.grades i).2) (mem_univ i))).trans (
      pow_le_pow_left₀ (zero_le_one.trans hh) (inv_anti₀ hg h) _)
  rw [portions, Finset.sum_apply]
  refine (norm_sum_le ..).trans ?_
  unfold Frame.coeffSize; rw [Finset.mul_sum]; refine sum_le_sum fun i _ => ?_
  rw [Pi.smul_apply,norm_smul]
  refine (mul_le_mul_of_nonneg_left ((purposes X i).2 o U) (norm_nonneg _)).trans ?_
  rw [mul_comm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (he i) (zero_le_one.trans (purposes X i).1)

lemma saves (o : Site n) (P : BudgetPoint) (A r : ℝ) (x : F.Coeff) (hx : o ∈ X.footprint o) (hr : 0 ≤ r)
    (h : ∀ i : F.Index,
      P.Regular (X.footprint o) (X.places (Pi.single i 1) o) ∧ P.supBounds o (X.footprint o) (X.places (Pi.single i 1) o)
        (A*P.threshold^(F.grades i).2)) :
    Banked P r {o} (masked P.threshold (X.footprint o) (X.places (F.scaled (P.threshold)⁻¹ x) o))
      (burn P r (X.footprint o) * A * F.coeffSize x) := by
  let U := X.footprint o
  let c := F.scaled (P.threshold)⁻¹ x
  let f (i : F.Index) := X.places (Pi.single i 1) o
  have hh (i) : Banked P r {o} (c i • masked P.threshold U (f i))
      (burn P r (X.footprint o) * A * ‖x i‖) := by
    refine ((Banked.term (Finset.singleton_subset_iff.mpr hx) (r:=r) ((h i).2).1
      (h i).1 fun j hj => (mem_singleton.mp hj).symm ▸ (h i).2).scale (c i)).enlarge ?_
    unfold c; rw [Frame.scaled_apply, norm_mul, Complex.norm_real,Real.norm_of_nonneg (by
      have := P.threshold_pos; positivity)]
    apply le_of_eq; rw [inv_pow]; have h0 := P.threshold_pos; field_simp
  have he (U' : Config G n) : (∑ i, c i • masked P.threshold U (f i)) U'=
      masked P.threshold U (X.places c o) U' := by
    rw [Finset.sum_apply]; by_cases h' : Healthy P.threshold U U'
    · simp_rw [Pi.smul_apply, masked_eq _ _ _ _ h']
      rw [portions X c]; simp_rw [Finset.sum_apply, Pi.smul_apply]; rfl
    simp_rw [Pi.smul_apply, masked_ne _ _ _ _ h', smul_zero, sum_const_zero]
  unfold Frame.coeffSize; rw [Finset.mul_sum]; change Banked _ _ _ (masked P.threshold U (X.places c o)) _
  rw [← funext he]; exact Banked.sums _ _ _ (singleton_nonempty _) hr fun i _ => hh i

def room := X.stencil.sup fun x => Finset.univ.sup fun i => (x i).natAbs

lemma hoist (o : Site n) (B : ℕ) (h : room X ≤ B) : coverNumber B (X.footprint o) ≤ 1 := by
  have hx (i : Site n) (he : i∈X.footprint o) : separation o i ≤ B := by
    obtain ⟨y,hy,rfl⟩ := mem_image.mp he
    rw [separation_comm,separation, add_sub_cancel_right]
    exact Finset.sup_le fun i _ => (Corona.lap _ _).trans ((le_sup (f:=fun i => (y i).natAbs)
      (mem_univ i)).trans ((le_sup (s:=X.stencil) (f:=fun x => Finset.univ.sup fun i => (x i).natAbs) hy).trans h))
  refine le_trans (Corona.list_cost (D:={o}) B ⟨fun i hi => halo_spec.mpr ⟨o,mem_singleton_self _,hx i hi⟩,
    Corona.ship_halo _ ?_⟩) (le_of_eq (card_singleton o))
  intro i hi j hj; rw [mem_singleton.mp hi,mem_singleton.mp hj]
end YM.Multi.Maquette
