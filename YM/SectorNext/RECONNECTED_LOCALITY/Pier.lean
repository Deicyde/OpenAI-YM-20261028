import YM.SectorNext.RECONNECTED_LOCALITY.Radiance

set_option warningAsError false

/-!
Choose rates just once at the map's prices. $u≥0$ (no cutoff at high u).

Conjugate perturbation costs through the absolute Deck, no factor in volume,
window size, or diagonal weight.

Compression is restriction of A itself incl
wrap and identity completion.

No analyticity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {g : Radar I} {A : Matrix I I ℝ} {δ k σ t u : ℝ}

def clip (g : Radar I) (W : Finset I) : Radar ↥W := {
  d i j := g.d i.val j.val
  down _ _ := g.down ..
  same _ := g.same _
  back _ _ := g.back ..
  chain _ _ _ := g.chain .. }

-- principal compression always on actual coordinates
abbrev hotel (W : Finset I) (A : Matrix I I ℝ) := A.submatrix (Subtype.val : ↥W → I) (Subtype.val : ↥W → I)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma clip_bill (W : Finset I) (i j : ↥W) :
    bill (clip g W) σ (hotel W A) i j=bill g σ A i.val j.val := rfl

omit [DecidableEq I] in
lemma Deck.hotel (h : Deck g A σ k) (W : Finset I) : Deck (clip g W) (Ice.hotel W A) σ k := by
  constructor <;> intro i <;> simp_rw [clip_bill]
  · rw [Finset.sum_coe_sort]
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bill_nonneg ..)).trans (h.1 i)
  rw [Finset.sum_coe_sort W (fun x => bill g σ A x (i:I))]
  exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bill_nonneg ..)).trans (h.2 i)

/-- Extend the *vector for the test*, not A^-1. -/
def unpin (W : Finset I) (y : ↥W→ℝ) (i : I) := if h : i∈W then y ⟨i,h⟩ else 0







def face (A : Matrix I I ℝ) (u : ℝ) := A+u • 1

lemma Buoy.face (h : Buoy A δ) (u : ℝ) : Buoy (Ice.face A u) (δ+u) := by
  intro x; unfold Ice.face; rw [add_mulVec,smul_mulVec,one_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul,add_mul];
  exact add_le_add_left (h x) _

-- exp(s)-1<=s exp(s) all s>=0, also works from -s
private lemma push {x y : ℝ} (h : |x| ≤ y) : |Real.exp x-1|≤y*Real.exp y := by
  rw [abs_sub_le_iff]
  have hy : 0≤y := (abs_nonneg _).trans h
  constructor
  · have he : Real.exp x≤Real.exp y := Real.exp_le_exp.mpr ((le_abs_self _).trans h)
    have hm := Real.add_one_le_exp (-y)
    have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos y).le
    rw [←Real.exp_add,neg_add_cancel, Real.exp_zero] at hh; linarith
  have he := Real.add_one_le_exp x
  have hm := Real.add_one_le_exp y
  have hn := neg_le_abs x; nlinarith

private lemma soft {x d t σ : ℝ} (ht : 0≤t) (he : 2*t≤σ) (hd : |x| ≤ d) (hσ : 0<σ) :
    |Real.exp (t*x)-1| ≤ (2*t/σ)*Real.exp (σ*d) := by
  have hl : 0≤d := (abs_nonneg _).trans hd
  apply (push (x:=t*x) (y:=t*d) (by rw [abs_mul,abs_of_nonneg ht]; gcongr)).trans
  rw [show t*d=(2*t/σ)*(σ/2*d) by field_simp,mul_assoc]
  -- rw changes both d factors
  gcongr
  calc
    _ ≤ Real.exp (σ/2*d) * Real.exp (σ/2*d) := by
      apply mul_le_mul (by linarith [Real.add_one_le_exp (σ/2*d)]) ?_ (Real.exp_pos _).le (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      rw [show (2*t/σ)*(σ/2*d)=t*d by field_simp]; gcongr; linarith
    _ = _ := by rw [←Real.exp_add]; ring_nf

/-- Perturb A to A+lifted (adding uI commutes, hence the SAME estimate for all u) -/
def lifted (g : Radar I) (t : ℝ) (q : I) (A : Matrix I I ℝ) : Matrix I I ℝ :=
  of fun i j => (Real.exp (t*(g.d q i-g.d q j))-1)*A i j

omit [DecidableEq I] in
lemma Deck.lifted (h : Deck g A σ k) (ht : 0≤t) (he : 2*t≤σ) (hh : 0<σ) (q : I) :
    Deck g (Ice.lifted g t q A) 0 ((2*t/σ)*k) := by
  refine h.press ?_ (by positivity)
  intro i j
  rw [bill_zero,Ice.lifted,of_apply,abs_mul,bill,mul_left_comm]
  have h1 := g.chain q j i
  have h2 := g.chain q i j
  refine (mul_le_mul_of_nonneg_right (soft ht he (d:=g.d i j) ?_ hh) (abs_nonneg _)).trans_eq ?_
  · rw [g.back j i] at h1
    rw [abs_sub_le_iff]; constructor <;> linarith
  dsimp only [ray]; ring









end YM.SectorNext.Reconnect.Ice
