import YM.Next.FREE_KERNELS.Scripts

/-!
# Auxiliary analytic expressions for the columns

Everything centered on ONE output cube. `heel` retains the *current* scaled
principal singular term after taking input covariance from its entire history;
in general a different split from the one in `Train.pole_split`. Matching the
two may not use either as an analytic value at the pole.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {j t : ℕ}

namespace Flight

def span (P : Flight j t) := divisor P.land.mass

def portD (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) (a : Axis) :=
    P.wing.bulb k (aliasAt p l) a / blow P.wing.mass p l

def portR (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) :=
    (blow P.wing.mass p l)^2 * P.wing.bend k (aliasAt p l)

abbrev toe (P : Flight j t) (p : Momentum) := aliasAt p (0 : Site P.L)

def heel (k : ℝ) (P : Flight j t) (p : Momentum) (a : Axis) := yen (pullLine P.patch a) (toe P p) *
    P.wing.bulb k (toe P p) a

def above (k : ℝ) (P : Flight j t) (p : Momentum) (a : Axis) :=
    ∑ i∈Finset.univ.erase (0:Site P.L), yen (pullLine P.patch a) (aliasAt p i)*portD k P p i a

def tailings (k : ℝ) (P : Flight j t) (p : Momentum) (a : Axis) := above k P p a+(k:ℂ)⁻¹

def fore (k : ℝ) (P : Flight j t) (p : Momentum) := ∑ i, P.wing.bulb k (toe P p) i

def hills (k : ℝ) (P : Flight j t) (p : Momentum) := ∑ i ∈ Finset.univ.erase (0:Site P.L),
    yen (massFilter P.patch) (aliasAt p i)*(∑ a, portD k P p i a)

def abide (k : ℝ) (P : Flight j t) (p : Momentum) :=
    yen (massFilter P.patch) (toe P p)*fore k P p + span P p * hills k P p

variable (k : ℝ) (hk : 0 < k) (P : Flight j t)
lemma span_root (p : Momentum) : blow P.wing.mass p (0 : Site P.L)=P.span p := by rw [blow_zero]; rfl
lemma portD_match {p : Momentum} (hp : p∈realCube zone) (l : Site P.L) (he : l≠0 ∨ p≠0) (a) :
    portD k P p l a=scaleD P.L k P.wing (aliasAt p l) a := by
  obtain ⟨h1,h2⟩ := alias_regular hp l he
  unfold portD scaleD blow
  rw [Train.D_bulb k _ h1 h2]; simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring
include hk in
lemma portR_match {p : Momentum} (hp : p∈realCube zone) (l : Site P.L) (he : l≠0 ∨ p≠0) :
    portR k P p l=scaleR P.L k P.wing (aliasAt p l) := by
  obtain ⟨h1,h2⟩ := alias_regular hp l he
  unfold portR scaleR blow; rw [Train.recover_rho k hk _ h1 h2]; ring

lemma toe_regular {p : Momentum} (hp : p∈realCube zone) : toe P p∈realCube zone := alias_in_real zone_pos hp _ P.odd
lemma toe_bar (p : Momentum) : P.toe (-p)=-P.toe p := by simpa using alias_reverse p P.odd (0 : Site P.L)

lemma toe_feed {p : Momentum} (hp : p∈realCube zone) (he : p≠0) (a) :
    P.land.levelD k a p = heel k P p a / P.span p + tailings k P p a := by
  let L := P.L
  unfold land; rw [Train.D_feedback]
  have ht : slide P.patch a (P.wing.levelD k a) p = heel k P p a / P.span p + above k P p a := by
    let f (l : Site P.L) := yen (pullLine P.patch a) (aliasAt p l) * portD k P p l a
    calc
      _ = ∑ i, f i := by
        unfold slide shuttle; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
        unfold f; rw [portD_match k P hp _ (Or.inr he)]; unfold scaleD; ring!
      _ = f 0 + ∑ i∈Finset.univ.erase 0, f i := (Finset.add_sum_erase _ f (Finset.mem_univ _)).symm
      _ = _ := by unfold f above portD heel toe; rw [span_root P]; ring
  exact (congr_arg (·+(k:ℂ)⁻¹) ht).trans (by unfold tailings; ring)

lemma bulb_network {p : Momentum} (hp : p∈realCube zone) (he : p≠0) (a) :
    P.land.bulb k p a=heel k P p a+P.span p*tailings k P p a := by
  have hh := toe_feed k P hp he a
  rw [Train.D_bulb k _ hp he] at hh; have hm := divisor_ne P.land.mass hp he
  unfold span at *; field_simp at hh; rw [hh]

lemma record_abide {p : Momentum} (hp : p∈realCube zone) (he : p≠0) :
    P.abide k p=P.span p * P.tabE k p := by
  have hu l : total k P (aliasAt p l)=∑ i, portD k P p l i := by
    simp_rw [portD_match k P hp _ (Or.inr he)]; rfl
  let f := fun l : Site P.L => yen (massFilter P.patch) (aliasAt p l)*(∑ i, portD k P p l i)
  have hh : tabE k P p=f 0+ hills k P p := by
    unfold tabE; simp_rw [hu]; exact (Finset.add_sum_erase _ f (Finset.mem_univ _)).symm
  rw [hh]; unfold abide; rw [mul_add]
  have heq : P.span p*f 0 = yen (massFilter P.patch) (toe P p)*fore k P p := by
    unfold f fore portD; simp_rw [span_root]; rw [mul_left_comm, ← Finset.sum_div];
    unfold span toe; rw [mul_div_cancel₀ _ (divisor_ne P.land.mass hp he)]
  rw [heq]

lemma filter_silver {p : Momentum} (hp : physical p) : Silver (yen (massFilter P.patch) p) := by
  have he : star (massFilter P.patch p)=massFilter P.patch (-p) := by unfold massFilter; rw [star_pow, Train.area_conj,show star p=p from hp];
  unfold yen; rw [← he]; exact Silver.gram _

include hk
lemma hills_positive {p : Momentum} (hp : p∈realCube zone) : Silver (P.hills k p) := by
  refine Silver.sum _ _ fun i hi => ?_
  have hh := alias_regular hp i (Or.inl (Finset.mem_erase.mp hi).1)
  refine (P.filter_silver hh.1.1).mul (Silver.sum _ _ fun a ha => ?_)
  rw [portD_match k _ hp i (Or.inl (Finset.mem_erase.mp hi).1)]
  exact ((Silver.side _).pow _).inv.mul (Train.D_cost _ hk _ _ hh.1.1)



lemma abide_live {p : Momentum} (hp : p∈realCube zone) : P.abide k p≠0 := by
  by_cases he : p=0
  · rw [he]; simp [abide,fore,toe,alias_zero_eq,YM.Next.Free.narrow,span,yen,massFilter,Axis]
  rw [record_abide k P hp he]; exact mul_ne_zero (divisor_ne P.land.mass hp he) (P.tabE_puncture k hk hp he)
end Flight
end YM.Next.Free
