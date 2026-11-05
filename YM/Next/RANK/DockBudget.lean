import YM.Next.RANK.StageSpan


/-!
# Ledger of estimates at the middle stop

Use narrow test for entire (uncorrected) marked representation, separate
regular estimate for remainder with single-cell markers, W with error from
free connected value on all the indicated mask. K suppression through narrow,
even carrying threshold-changing and unmarked histories, including any required
spare exponential. These are only the estimates needed from the comparison step
here, not consequences merely of the accepted contracts.

Numerical tests for pre-L geometry and post-L delays are separately listed.
`r/v = exp coefficient`. Expose all gains after attaching failed-mask terms
upon correcting. Sup taken at true gauge fields, constraints
of Lifted; no changing coordinates of actual flags or pruning supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Dock
open Lattice Wilson RG Marker Glyph Camp EntryWord Value Finset Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {o : BudgetPoint}

/-- Estimates/delays bookkeeping. `fee` is per refused mask, `reserve` per
old K; callbacks pay all meetings. Kept exponents J.e plus a
common spare consumed at this stopping. `saving` extra gain from packing on
several reflection cells. -/
structure Change (o : BudgetPoint) (m : ℕ) where
  e : ℝ
  base : 0 ≤ e
  spare : ℝ
  spare_cost : 0 ≤ spare
  fee : ℝ
  fee_cost : 0 ≤ fee
  narrow : ℝ -- charge log of restoration from v
  narrow_cost : 0 ≤ narrow
  inside : ℝ -- ditto from u
  inside_cost : 0 ≤ inside
  reserve : ℝ -- retained output K suppression (besides γ)
  reserve_cost : 0 ≤ reserve
  saving : ℝ -- extra mixed support to cost AFTER v undo
  saves : 0 ≤ saving
  local_pack : 64*(m*narrow+saving) ≤ spare*o.B
  force_pack : 64*(m*narrow+fee* ((2^m:ℕ):ℝ)) ≤ spare*o.B
  radius : ℝ
  pos_r : 0 < radius
  limit_c : ℝ -- sup restored weight on each failed-mask e C, incl (e+1) support
  first_c : 0 ≤ limit_c
  limit_w : ℝ -- sup restored weight on each regular W after subtracting on the mask, e support
  first_w : 0 ≤ limit_w
  output : ℝ -- wanted small sup per marker H and more if further step
  wing : ℝ -- root v cost on remainder H cross, at e+spare
  yard : ℝ -- root u cost on remainder H same-cell, at e
  weather : ((2^m:ℕ):ℝ)*limit_w+(Real.exp (-saving)*wing + Real.exp (m*inside)*yard) ≤ output
  hit : ℝ -- estimate used for K at narrow and e+1+spare
  γ : ℝ
  main : 0 ≤ γ
  force_hit : Real.exp (m*narrow + fee * ((2^m:ℕ):ℝ) + reserve)*hit+
    ((2^m:ℕ):ℝ)*(limit_c*Real.exp (-fee)) ≤ γ
  fits : ((o.B+o.B+1:ℕ):ℝ)^4*γ ≤ 1

variable {A V : Type} [DecidableEq A] [DecidableEq V] [Fintype A] [Fintype V]
variable {m : ℕ}

namespace Change
def m0 (j : Change o m) : ℝ := j.radius * Real.exp (-j.narrow)
def m1 (j : Change o m) : ℝ := j.radius * Real.exp (-j.inside)
def hail (j : Change o m) : ℝ := Real.exp ( - j.reserve)*(Real.exp j.γ - 1)
end Change

variable {ι κ : Type} [Fintype ι] [Fintype κ] {Q : A → Support n} {ζ : A × V → Site n}
variable (J : Change o m)

/-- A W entry per cell and nonempty local subset. $D$ SIGNED correction, minus
free connected moments. -/
structure Wells (P : A × flame V → SourceAt G ζ) (D : A × flame V → ℂ) (Q : A → Support n) : Prop where
  lit i : (P i).fires = sectionAt i
  room i : (P i).extent= Q i.1
  restored i U : Healthy o.threshold (Q i.1) U →
    charge o J.e (Q i.1) * Poly.toll (fun _ => J.radius) (sectionAt i) * ‖(P i).value U + D i‖ ≤ J.limit_w
  failed i : charge o (J.e+1) (Q i.1) * Poly.toll (fun _ => J.radius) (sectionAt i) * ‖D i‖ ≤ J.limit_c

-- W reserved on-cluster. H remainder split, single-cell gain provided from separate
-- regular calculation with that radius. It is NOT applied to force history. K test
-- includes unmarked. Histories here simultaneously carrying ANY allowed selected subset.
structure Reception (H : ι → SourceAt G ζ) (K : κ → Lifted G ζ o.threshold) : Prop where
  regular : ∃ c : ι → ℝ,(∀ i, if singled (H i).fires then
    (H i).pays o (fun _ => J.m1) J.e (c i) else (H i).pays o (fun _ => J.m0) (J.e+J.spare) (c i)) ∧
    (∀ i : A × V, ∑ j, (if ¬ singled (H j).fires ∧ i∈(H j).fires.val then c j else 0) ≤ J.wing) ∧
    (∀ i : A × V, ∑ j, (if singled (H j).fires ∧ i∈(H j).fires.val then c j else 0) ≤ J.yard)
  forced : ∃ c : κ → ℝ,(∀ i,Lifted.pays o (K i) (fun _ => J.m0) (J.e+1+J.spare) (c i)) ∧
    (∀ i : Site n,∑ j,(if i∈(K j).extent then c j else 0) ≤ J.hit)

-- Pay through all ancestry proofs for supports larger than exactly one RC.

lemma paid_marker (d : ℝ) (i : modes V) : Poly.toll (fun _ : V => J.radius) i =
    Real.exp (d*i.val.card)*Poly.toll (fun _ => J.radius * Real.exp (-d)) i := by
  simp only [Poly.toll,prod_const, mul_pow]
  rw [mul_comm d,Real.exp_nat_mul, Real.exp_neg, inv_pow]; field_simp
lemma charged (e l : ℝ) (P : Support n) : charge o (e+l) P=charge o e P*Real.exp (l*coverNumber o.B P) := by simp only [charge,add_mul,Real.exp_add]

lemma mixed_cost (h : rearranged ζ Q o.B) (hm : Fintype.card V ≤ m) (H : SourceAt G ζ) (W : ℝ)
    (he : ¬ singled H.fires)
    (hx : H.pays o (fun _ => J.m0) (J.e+J.spare) W) : H.pays o (fun _ => J.radius) J.e (Real.exp (-J.saving)*W) := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hx.1,fun U hh => ?_⟩
  let q := audience H.fires
  let B := coverNumber o.B H.extent
  let I := (touchedBy Q H.extent).card
  have hp : q.card ≤ I := card_le_card (included Q ζ h.1 _ H.fires H.remembers)
  have hI : 2≤ I := le_trans (show 2 ≤ q.card from Nat.lt_of_not_ge he) hp
  have hc : H.fires.val.card ≤ I*m := (counted H.fires).trans (Nat.mul_le_mul hp hm)
  have hd : (m*J.narrow+J.saving)*I ≤ J.spare*B := dispersal_cost h _ J.spare_cost J.local_pack hI
  have h1 : J.narrow*H.fires.val.card ≤ -J.saving + J.spare*B := by
    have he₁ := mul_le_mul_of_nonneg_left (show (H.fires.val.card:ℝ) ≤ (I:ℝ)*m by exact_mod_cast hc) J.narrow_cost
    have he₂ := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ I by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) hI)) J.saves
    linarith only [he₁,he₂,hd]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hx.2 U hh) (Real.exp_pos _).le)
  rw [charged (o:=o)]
  set a := Poly.toll (fun _ : A × V => J.m0) H.fires
  have h2 : Poly.toll (fun _ => J.radius) H.fires = Real.exp (J.narrow * H.fires.val.card)*a := paid_marker J J.narrow H.fires
  rw [h2]; have h3 : 0 ≤ a := (Poly.worth (fun _ => mul_pos J.pos_r (Real.exp_pos _)) _).le
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) h3)
    (show 0 ≤ charge o J.e H.extent from (Real.exp_pos _).le)) (norm_nonneg _)).trans_eq ?_
  rw [Real.exp_add]; dsimp only [B]; ring

lemma single_cost (hm : Fintype.card V ≤ m) (H : SourceAt G ζ) (W : ℝ) (he : singled H.fires)
    (hx : H.pays o (fun _ => J.m1) J.e W) : H.pays o (fun _ => J.radius) J.e (Real.exp (m*J.inside)*W) := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hx.1,fun U hh => ?_⟩
  have hv : H.fires.val.card ≤ m := by simpa only [one_mul] using (counted H.fires).trans (Nat.mul_le_mul he hm)
  set a := Poly.toll (fun _ : A × V => J.m1) H.fires
  have he := paid_marker J J.inside H.fires
  change Poly.toll (fun _ => J.radius) H.fires= _*a at he
  have h3 : 0 ≤ a := (Poly.worth (fun _ => mul_pos J.pos_r (Real.exp_pos _)) _).le
  rw [he]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (hx.2 U hh) (Real.exp_pos _).le)
  have h1 : J.inside*H.fires.val.card ≤ (m*J.inside) := by
    rw [mul_comm J.inside]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv) J.inside_cost
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) h3)
    (show 0 ≤ charge o J.e H.extent from (Real.exp_pos _).le)) (norm_nonneg _)).trans_eq ?_
  simp only [a]; ring

end YM.Next.Rank.Dock
