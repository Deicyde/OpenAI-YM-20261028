import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Tangent
import YM.Org.Theatre

set_option warningAsError false

/-! # Re-description of a signed-source response, full squarefree algebra

Plausible shorter upstream estimate: one-step produces normalized
responses with potentially different exact singleton presentations, but the
purchase can also guarantee that their prescribed replacements differ
by some structured transformations. This is one such transformation (cf
inadequacy of demanding *arbitrary* prescriptions with weak support
reserve, even if they agree on the one-source tangent). Here it is
*constructive* at the displayed infinite-address response API: don't ask
for new kernels or main estimates at the other cost data, explicitly repair
the higher-mode responses with their actual overlapping supports. Mint
need still be purchased at sufficient exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet

open RG Marker Wilson Lattice Multi Finset
open scoped Topology BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {G : Gauge} {n : Side} (P : Rep G n) (s : V)
variable (D : Hot R → Pulse G n) (U : Config G n)

/-- Preserve all incumbent accounting. D are pre-designated response
entries or taps. -/
def share (r : Pack n) : Poly R := Poly.send R.quiet (incumbent P U r) + Multi.lit R (fun i => (D i).2 r U)

variable (p : Pack n) (z : Site n) (F : Config G n→ℂ) (r : Pack n)

def pen : Poly R := if r=p then algebraMap ℂ _ (F U) else 0
def ink (W : Config G n → Poly R) : Poly R := if r=p then (if p.zone ∩ flags P.p.threshold U = p.flagsAt then W U else 0) else 0

def alteration : Poly R := pen (R:=R) U p F r - (ink P U (spread p z) r (fun v => algebraMap ℂ _ (F v)) +
    ∑ i∈attaches p z,ink P U (braid p i) r (fun v => algebraMap ℂ _ (F v)*share P D v i))

def supplement : Poly R := Poly.send (R.fire s) 1 * alteration P D U p z F r

-- applies AFTER taking ordinary prescription Z, not assuming shape of D
-- or introducing a producer selection.
def edited (x : Hot R) : Pulse G n := ((D x).1, fun r U => (D x).2 r U + (supplement P s D U p z F r).part x.val)

omit [Fintype V] in
lemma supplement_quiet : (supplement P s D U p z F r).part R.quiet=0 := by
  simp only [supplement,Poly.quiet_mul,Poly.part_send,if_neg (R.fire_hot _).symm,zero_mul]

omit [Fintype V] in
lemma share_quiet : (share P D U r).part R.quiet = incumbent P U r := by simp [share,Multi.part_lit_quiet]

omit [Fintype V] in
lemma share_at (x : Hot R) : (share P D U r).part x.val = (D x).2 r U := by
  rw [share,Poly.part_plus,Multi.part_lit,Poly.part_send,if_neg,zero_add]
  intro h; obtain H := x.property; rw [h] at H; exact not_nonempty_empty H

omit [Fintype V] in
lemma adds : share P (edited P s D p z F) U r=share P D U r + supplement P s D U p z F r := by
  ext i; by_cases h : i.val.Nonempty
  · let j : Hot R := ⟨i,h⟩; change (share P _ U r).part j.val=(share P D U r + _).part j.val
    rw [Poly.part_plus,share_at,share_at]; rfl
  rw [show i=R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp h),Poly.part_plus, share_quiet, share_quiet,supplement_quiet,add_zero]

omit [Fintype V] in
lemma revenues : (∑ i : Pack n,supplement P s D U p z F i * diamond (flags P.p.threshold U) (share P D U) i) = 0 := by
  let L := Poly.send (R.fire s) (1:ℂ)
  let H := share P D U
  let A := flags P.p.threshold U
  let W := diamond A H
  unfold supplement; simp_rw [mul_assoc, ← Finset.mul_sum]; change L*(∑ i, alteration P D U p z F i*W i) = _
  have charge (p : Pack n) (V : Config G n→Poly R) : (∑ i, ink P U p i V * W i) = V U * W p := by
    unfold ink; rw [sum_eq_single p,if_pos rfl]
    · by_cases h : p.zone∩A=p.flagsAt
      · rw [if_pos (show _ from h)]
      rw [if_neg (show _ from h),zero_mul,show W p = 0 from diamond_guard A H p h,mul_zero]
    · intro j _ hj; rw [if_neg hj,zero_mul]
    simp
  have main (p : Pack n) : (∑ i, pen (R:=R) U p F i * W i)=algebraMap ℂ (Poly R) (F U)*W p := by
    unfold pen; rw [sum_eq_single p,if_pos rfl]
    · intro j _ hj; rw [if_neg hj,zero_mul]
    simp
  have h : ∑ i, alteration P D U p z F i * W i=0 := by
    unfold alteration; simp_rw [sub_mul,add_mul,Finset.sum_mul,sum_sub_distrib,sum_add_distrib,
      Finset.sum_comm (s:=univ) (t:=attaches p z),charge,main]
    change algebraMap ℂ _ (F U) * diamond A H p - _ = _
    rw [diamond_step A H p z,mul_add,mul_sum]
    simp only [W,H,← mul_assoc,sub_self]
  rw [h,mul_zero]

private lemma pay_scattered {α : Type*} [CommRing α] (u : α) (h : u*u=0) (W F : Pack n → α) (S : Finset (Pack n)) :
    ∏ i∈S,(W i+u*F i) = (∏ i∈S,W i)+∑ i∈S,(u*F i)*∏ j∈S.erase i,W j := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih =>
    rw [prod_insert hi,ih,prod_insert hi,sum_insert hi,erase_insert hi]
    rw [add_mul,mul_add,mul_sum,mul_add,mul_sum,add_assoc, add_left_cancel_iff]
    have ht (j : Pack n) : u * F i * (u * F j * ∏ v∈S.erase j,W v)=0 := by rw [show u*F _ *(u*F _ * _) = (u*u)*(F i*F j* ∏ v∈S.erase j,W v) by ring,h,zero_mul]
    simp_rw [ht,sum_const_zero,add_zero,add_comm _ (u*F i * _),add_right_inj]
    exact sum_congr rfl fun j hj => by rw [erase_insert_of_ne (show i≠j from fun h => hi (h ▸ hj)), prod_insert
      (fun h => hi (mem_of_mem_erase h))]; ring

-- `share` shortcut only for the gas. Edit is basis/nullpack only
-- (not changing exponent labels through these moves).
theorem edited_many : many P R (edited P s D p z F)=many P R D := by
  funext U
  let H := Poly.send (R.fire s) (1:ℂ)
  have hx : H*H=0 := send_noProd (x:=R.fire s) (y:=R.fire s) (fun h => by
    obtain ⟨v,h⟩ := h; exact Finset.disjoint_left.mp h.1 (mem_singleton_self s) (mem_singleton_self s)) (1:ℂ) (1:ℂ)
  unfold many composeAt
  let L := share P (edited P s D p z F) U
  let I := flags P.p.threshold U
  let x := Multi.lit R (fun t => (D t).1 U)
  refine congrArg₂ _ rfl ?_; change x.pass * (∑ i∈Pack.clears I, ∏ j∈i,L j) = _
  unfold L; simp_rw [adds, supplement, pay_scattered (Poly.send (R.fire s) 1) (by exact hx), sum_add_distrib, guests]
  rw [show (∑ i : Pack n,(H*alteration P D U p z F i)*diamond I (share P D U) i)=_ from revenues P s D U p z F,
    add_zero]; rfl
end YM.AnalyticNext.GridStop.Alphabet
