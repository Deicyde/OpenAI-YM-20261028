import YM.SectorNext.RECONNECTED_LOCALITY.Pier

set_option warningAsError false

/-!
# Schur passes 

Work directly with principal windows (possibly column-by-column different --
NO Dirichlet-Gram or deleting boundary rows, no translation assumption and in
fact the Σ geometry in the input Gram may break translation).

Assume only they
contain a big enough ball in the counting Radar used to price entries (not that
the window recipe is actually anchored there; symmetry uses separate locations!).

Volume toll for Schur at true counting addresses with rate decrease `Weather`.

Estimate and preserve *1/(1+u)* on the exponentially small residual too.

Finite threshold
condition for strict covariance even when the radius is comparable to the whole
box; measure statements downstream.

Active projection not needed for bounds:
record of A here can be full with identity padded on inactive coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {g : Radar I} {A D : Matrix I I ℝ} {W : I → Finset I} {δ k σ ν t u L B b : ℝ}

/-- Zero outside column's own window, $Π_u$ (zero column if center not
kept, never used under Eye). -/
def floe (W : I → Finset I) (A : Matrix I I ℝ) (u : ℝ) : Matrix I I ℝ := of fun i j =>
    if h : j ∈ W j then if he : i∈W j then (face (hotel (W j) A) u)⁻¹ ⟨i,he⟩ ⟨j,h⟩ else 0 else 0

def Eye (g : Radar I) (W : I→Finset I) (b : ℝ) := (∀ i,i∈W i) ∧ ∀ j i,i∉W j → b≤g.d i j

omit [Fintype I] in
lemma floe_self (h : Eye g W b) {i j : I} (hi : i∈W j) : floe W A u i j = (face (hotel (W j) A) u)⁻¹ ⟨i,hi⟩ ⟨j,h.1 j⟩ := by
  unfold floe; rw [of_apply,dif_pos (h.1 j),dif_pos hi]

omit [Fintype I] in
lemma floe_else {i j : I} (hi : i∉W j) : floe W A u i j=0 := by
  classical
  unfold floe; rw [of_apply]; split
  · rfl
  rfl



omit [Fintype I] in
lemma floe_unpin (h : Eye g W b) (j : I) :
    (fun i => floe W A u i j) =
      unpin (W j) (fun i => (face (hotel (W j) A) u)⁻¹ i ⟨j,h.1 j⟩) := by
  funext i; by_cases he : i∈W j
  · rw [floe_self h he,unpin,dif_pos he]
  rw [floe_else he,unpin,dif_neg he]

omit [Fintype I] in
lemma hotel_face (U : Finset I) : hotel U (face A u)=face (hotel U A) u := by
  ext i j
  simp only [hotel,submatrix_apply,face,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,one_apply]
  have he : i.val=j.val ↔ i=j := Subtype.ext_iff.symm
  simp only [he]





/-- Summation toll on COUNTING index NOT addresses. -/
def Weather (g : Radar I) (ν L : ℝ) := ∀ i,∑ j,ray g (-ν) i j ≤ L

omit [DecidableEq I] in
/-- Trade exponent for the physical counting toll (don't issue it freely just
because the torus is finite!) -/
lemma thaw (hk : 0≤k) (h : ∀ i j,bill g (t+ν) A i j≤k) (he : Weather g ν L) : Deck g A t (k*L) := by
  have hl i j : bill g t A i j ≤ k*ray g (-ν) i j := by
    have hh := mul_le_mul_of_nonneg_right (h i j) (ray_nonneg g (-ν) i j)
    rwa [bill,mul_assoc,←ray_add,add_neg_cancel_right] at hh
  constructor <;> intro i
  · exact (sum_le_sum (fun j _ => hl i j)).trans (by rw [←mul_sum]; gcongr; exact he i)
  have he' j := hl j i
  simp_rw [ray_symm (g:=g) (r:=-ν) _ i] at he'
  exact (sum_le_sum (fun j _ => he' j)).trans (by rw [←mul_sum]; gcongr; exact he i)

/-- Data about the *input* precision, actual counting coordinates in all cells
and charts. Fixed orders dependence can keep same prices across u. ν used at
1x Schur, 2x before off-window extraction, 3x for Combes. -/
structure Forecast (g : Radar I) (A : Matrix I I ℝ) (σ δ k ν L : ℝ) : Prop where
  fast : Deck g A σ k
  kind : 0<σ
  funds : 0<k
  tide : Buoy A δ
  stable : 0<δ
  still : 0<ν
  slower : 2*(2*ν+ν) ≤ σ
  debt : (2*(2*ν+ν)/σ)*k≤δ/2
  skies : Weather g ν L
  sizes : 0<L

/-- Rectangular cost for poling; can rebate through exact 1/(δ/2+u) instead -/
def deep (δ L : ℝ) := L*(1+2/δ)



namespace Forecast
variable (H : Forecast g A σ δ k ν L)
include H

omit [DecidableEq I] in
lemma waken (hu : 0≤u) {D : Matrix I I ℝ}
    (hd : ∀ i j,bill g (2*ν+ν) D i j≤1/(δ/2+u)) : Deck g D (2*ν) (deep δ L/(1+u)) := by
  have hd0:=H.stable; have hd1:=H.sizes
  have hh : 0<δ/2+u := by positivity
  apply (thaw (by positivity) hd H.skies).mono le_rfl
  rw [div_mul_eq_mul_div,div_le_div_iff₀ hh (by linarith : 0<1+u),deep]
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hd1.le hd0.le) hd0.le,mul_nonneg hd1.le hu]







omit [DecidableEq I] in
lemma speed : ν≤σ := by have:=H.slower; have:=H.still; linarith
end Forecast

def front (W : I → Finset I) (A : Matrix I I ℝ) := (1/2:ℝ) • (floe W A 0 + (floe W A 0).transpose)

omit [Fintype I] in
lemma front_even : (front W A).transpose = front W A := by
  unfold front; rw [transpose_smul,transpose_add,transpose_transpose,add_comm]



omit [Fintype I] in
lemma face_zero : face A 0=A := by simp [face]

/-- C vs A^-1 and S. Provide BOTH apart from norm identification or expansions. -/
def wet (δ L k : ℝ) := deep δ L * (k*deep δ L)

 -- parser may err








end YM.SectorNext.Reconnect.Ice
