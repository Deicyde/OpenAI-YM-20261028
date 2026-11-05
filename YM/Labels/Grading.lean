import YM.Labels.Action

/-!
Bigrading through engineering bound, even after G-invariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Labels
open Function Set Submodule
open scoped BigOperators

variable {G : Gauge} {d : ℕ}

abbrev piece (m : ℕ × ℕ) : Pol G →ₗ[ℂ] Pol G :=
  MvPolynomial.weightedHomogeneousComponent bidegree m

def Grade (m : ℕ × ℕ) : Submodule ℂ (Label G d) :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ bidegree m).comap (localFields G d).subtype

theorem pure_grade (m : ℕ × ℕ) (v : Label G d) : v ∈ Grade m ↔ pureDegree v.val m.1 m.2 := Iff.rfl

theorem component_change (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (p : Pol G)
    (m : ℕ × ℕ) : changed e (piece m p) = piece m (changed e p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hp := MvPolynomial.isWeightedHomogeneous_monomial bidegree u a (m := Finsupp.weight bidegree u) rfl
    have hq : MvPolynomial.IsWeightedHomogeneous bidegree (changed e (MvPolynomial.monomial u a))
        (Finsupp.weight bidegree u) := pure_moved (fun i => (i+2,1)) e u a
    rcases eq_or_ne m (Finsupp.weight bidegree u) with hm|hm
    · subst m; rw [piece, hp.weightedHomogeneousComponent_same, hq.weightedHomogeneousComponent_same]
    · rw [piece, hp.weightedHomogeneousComponent_ne _ hm, map_zero,
        hq.weightedHomogeneousComponent_ne _ hm]
  | add u v hu hv => simp only [map_add,hu,hv]

theorem component_mem (m : ℕ × ℕ) (v : Label G d) : piece m v.val ∈ localFields G d := by
  constructor
  · have he := (MvPolynomial.mem_restrictSupport_iff ℂ).mp (show v.val ∈ limited G d from v.property.1)
    change piece m v.val ∈ limited G d
    apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
    intro a ha; classical
    change a ∈ (MvPolynomial.weightedHomogeneousComponent bidegree m v.val).support at ha
    rw [MvPolynomial.support_weightedHomogeneousComponent] at ha
    exact he (Finset.mem_filter.mp ha).1
  intro J u
  have H : changed (fun _ => Taylor.paint u) v.val = v.val := by
    apply eval_ext; intro A; rw [eval_changed]; exact v.property.2 A u
  change read (changedJet _ J) (piece m v.val) = read J (piece m v.val)
  rw [← eval_changed, component_change, H]

def gradePart (m : ℕ × ℕ) : Label G d →ₗ[ℂ] Label G d where
  toFun v := ⟨_,component_mem m v⟩
  map_add' u v := Subtype.ext ((piece m).map_add u.val v.val)
  map_smul' z v := Subtype.ext ((piece m).map_smul z v.val)

theorem gradePart_self (v : Label G d) (m) (h : v ∈ Grade m) : gradePart m v = v :=
  Subtype.ext (MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (show
    MvPolynomial.IsWeightedHomogeneous _ _ m from (pure_grade m v).1 h))

theorem gradePart_zero (v : Label G d) (m m') (hne : m ≠ m') (h : v ∈ Grade m') :
    gradePart m v = 0 := Subtype.ext (MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne m
      (show MvPolynomial.IsWeightedHomogeneous _ _ m' from (pure_grade m' v).1 h) hne)

theorem gradePart_mem (m) (v : Label G d) : gradePart m v ∈ Grade m :=
  MvPolynomial.weightedHomogeneousComponent_mem bidegree v.val m

theorem gradePart_bar (m) (v : Label G d) : gradePart m (realBar v) = realBar (gradePart m v) := by
  classical
  apply Subtype.ext
  change piece m (conjPol v.val) = conjPol (piece m v.val)
  ext b
  simp only [conjPol, MvPolynomial.coeff_map,piece,MvPolynomial.coeff_weightedHomogeneousComponent]; split <;> simp

theorem gradePart_turn (m) (s : Ortho) (v : Label G d) : gradePart m (tensor s v) = tensor s (gradePart m v) :=
  Subtype.ext (component_change _ _ _).symm

theorem weight_slot (v : Key G →₀ ℕ) :
    Finsupp.weight bidegree v = (height v, v.sum fun _ n => n) := by
  classical
  ext <;> simp [Finsupp.weight_apply,height,Finsupp.sum,bidegree, Prod.fst_sum, Prod.snd_sum]

theorem power_le (v : Key G →₀ ℕ) : (Finsupp.weight bidegree v).2 ≤ height v := by
  rw [weight_slot]; unfold height; rw [Finsupp.weight_apply]; unfold Finsupp.sum
  apply Finset.sum_le_sum
  intro i _
  exact le_mul_of_one_le_right (Nat.zero_le (v i)) (show 1 ≤ generation i by unfold generation; omega)

theorem decompose (v : Label G d) : ∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
    gradePart (i,j) v = v := by
  classical
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum]
  ext a
  by_cases ha : MvPolynomial.coeff a v.val = 0
  · simp [gradePart,piece,MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_sum, ha]
  · have hw := (MvPolynomial.mem_restrictSupport_iff ℂ).mp (show v.val ∈ limited G d from v.property.1)
      (MvPolynomial.mem_support_iff.mpr ha)
    let h := height a
    let t := a.sum fun _ n => n
    have hi : h < d+1 := Nat.lt_succ_of_le hw
    have hj : t < d+1 := by
      apply lt_of_le_of_lt _ hi
      have hx := power_le a; rw [weight_slot] at hx; exact hx
    simp [gradePart,piece,MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_sum, weight_slot, ite_and]
    change (if h ≤ d then if t ≤ d then _ else _ else _) = _
    rw [if_pos (by omega), if_pos (by omega)]


theorem scalar_grade {v : Label G d} (m) (h : v ∈ Grade (m,0)) :
    ∃ k : ℂ, v = k • unit G d := by
  classical
  let k := MvPolynomial.coeff 0 v.val
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change v.val = k • (1 : Pol G)
  ext a
  rcases eq_or_ne a 0 with ha|ha
  · subst a; simp [k]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_one, if_neg (Ne.symm ha), smul_zero]
  by_contra! H
  have he := (pure_grade _ v).1 h H
  rw [weight_slot] at he
  obtain ⟨i, hi⟩ : a.support.Nonempty := by simpa using ha
  have hv : 0 < a i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hl : a i ≤ a.sum fun _ n => n := Finset.single_le_sum (f := a) (by simp) hi
  have hg := congr_arg Prod.snd he
  dsimp at hg
  omega

end YM.Labels
