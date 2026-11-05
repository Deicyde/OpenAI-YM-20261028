import YM.Work.E07.Defects


/-!
# E07 — bound on all affected M departures

A conditional estimate under exactly E01, E03 and E04. For the transferred
bounds freeze two excess arrays: toll U on `swell` (threshold **t**, not T),
and wire Q V on ALL `aisles`. The macro lemma pays both for the coarse term
of L and for toll V on third-range faces (even though the RHS uses all such
faces in `outs`, they are in `hit`). These payments and the transposed M on
the L rows keep the pre-L constants for large-input charges. All uniform
per-row small costs can use post-L constants and are paid by the size of
`hit`, hence by `spend` (the much higher cutoff T) with the B⁴ fee.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E07
open Lattice RG Finset Wilson Pressure Pressure.Stores Pressure.Teller Filter Bid
open scoped BigOperators Classical

/-- Price per unit of t times the combined fine/noise bill; depends on clips,
penalty and the incoming pre-L constants. -/
def preBill (high low : Clip) (K : KernelChoices) (a d D : ℝ) (N : ℕ) :=
    d * (a * (2 * (Real.sqrt high.direct + d)) + a * Real.sqrt K.penalty +
      2 * (Real.sqrt low.direct + d) * macroLarge N D) +
      2 * low.linear * macroLarge N D

/-- Price of a hit face (unit t²). Small coarse-input costs also here. -/
def seatBill (high low : Clip) (K : KernelChoices) (a d D W : ℝ) (j : ℕ) (L : Side) :=
    d * 2 * (a * (L.val : ℝ)^2 * (Real.sqrt high.direct + d) + a * Real.sqrt K.penalty * (2 * W) +
      (Real.sqrt low.direct + d) * macroSmall j D L W) +
      dCost a d + 2 * low.linear * macroSmall j D L W

section
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A : Stores S} {δ x a d W D : ℝ} {U : Config G f} {V : Config G c} {k : S.Choices} {N : ℕ}

lemma price_at (ha : 0 ≤ a) (hd : 0 ≤ d) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hb : 1 + N ≤ radiusB x) (htemp : temp x ≤ 2 * fiery G x S.patch.L)
    (hh : MacroStore S G N) (hp : Stores.Plot A U k V x W)
    (hq : ∀ p : Cell c, usable S U p.1 k →
      toll V p ≤ fuel (S.prediction U k) V p.1 p.2 + D / (S.patch.L.val : ℝ)^2 * port S p.1 U)
    (he : Payments δ A x U (S.prediction U k) V N)
    (hc : Allowance a T x V) (hm : Maximum d T x V)
    (hu : LaneCounts T.up x (fiery G x S.patch.L) T.high d 1 S.ratio.parent)
    (hv : LaneCounts T.down x (temp x) T.low d S.patch.L.val (id : Site c → Site c)) :
    let Q := S.prediction U k
    let s := A.hit U Q V x
    let t := fiery G x S.patch.L
    T.low.linear * temp x * (∑ i ∈ A.tides V x δ, toll V i) - talll T x U Q V s ≤
      preBill T.high T.low S.kernel a d D N * t *
        ((∑ i ∈ A.swell U t, toll U i) / (S.patch.L.val : ℝ)^2 + ∑ i ∈ A.aisles, wire Q V i) +
      seatBill T.high T.low S.kernel a d D W S.patch.J S.patch.L * t^2 * s.card := by
  intro Q s t
  have ht : 0 ≤ t := temp_nonneg _
  let l : ℝ := S.patch.L.val
  let E := picked (A.swell U t) (toll U)
  let F := picked A.aisles (wire Q V)
  let H := macroExcess S D E F
  let bill := (∑ i, E i) / l^2 + ∑ i, F i
  have hE (p) : 0 ≤ E p := picked_nonneg _ (fun p : Cell f => (show 0 ≤ toll U p from G.chord_nonneg _)) p
  have hF (p) : 0 ≤ F p := picked_nonneg _ (fun p : Bond c => (show 0 ≤ wire Q V p from G.chord_nonneg _)) p
  have hH (p) : 0 ≤ H p := macroExcess_nonneg _ hD hE hF p
  let r := macroSmall S.patch.J D S.patch.L W
  let b := macroLarge N D * bill
  have hr : 0 ≤ r := macroSmall_nonneg _ hD _ hW
  have hb' : ∑ p, H p ≤ b := macroExcess_total hh hD hE hF
  have hV (p : Cell c) (hi : p.1 ∈ A.dome (3 * radiusB x)) : toll V p ≤ r*t + H p :=
    coarse_split hh hD hW hp hb p hi (hq p)
  let u := Real.sqrt T.high.direct + d
  let v := Real.sqrt T.low.direct + d
  let g := Real.sqrt S.kernel.penalty
  let seats := s ×ˢ (univ : Finset Bool)
  let m : ℝ := s.card
  have hs (p : Cell c) (hi : p ∈ s) : p.1 ∈ A.dome (2 * radiusB x) :=
    (mem_filter.mp (show p ∈ A.outs x from (mem_filter.mp hi).1)).2
  have hi (p) (hn : p ∈ seats) : tagged p ∈ A.dome (2 * radiusB x) :=
    hs _ (mem_product.mp hn).1
  have hf : ∑ j ∈ seats, ‖unzip (T.Φ (till x) V) (T.Xf (till x) U) j‖ ≤
      (seats.card : ℝ) * (a*l^2 * (u*t)) + a * (2*u) * bill :=
    fine_total U hc ha hd hu hE
      (le_add_of_nonneg_right (sum_nonneg fun i _ => hF i)) seats hi (toll_split hp)
  have hn : ∑ j ∈ seats, ‖unzip (T.Φ' (till x) V) (Tube.Z S Q V) j‖ ≤
      (seats.card : ℝ) * (a * (g * (2*W*t))) + a * g * bill :=
    noise_total Q hc ha (by positivity) hF
      (le_add_of_nonneg_left (div_nonneg (sum_nonneg fun i _ => hE i) (sq_nonneg l)))
      seats hi (wire_split hp hW)
  have hl : ∑ j ∈ seats, ‖T.Xn (till x) V j‖ ≤
      (seats.card : ℝ) * (v * (r*t)) + 2*v*b := coarse_total hv hd (by positivity) _ hH hb' hi hV
  have hx := workL_total U Q hm hd s hf hn hl
  have hcast : (seats.card : ℝ) = m * 2 := by
    unfold m seats; rw [card_product]; simp
  rw [hcast] at hx
  have hy : -(dCost a d * t^2) * m ≤ ∑ p ∈ s, T.workD (till x) V (temp x) p := by
    apply le_trans _ (sum_le_sum (s := s) fun p _ => workD_ge ha hd hc hm p)
    rw [sum_const, nsmul_eq_mul, mul_comm]
  have hthird : ∑ p ∈ A.tides V x δ, toll V p ≤ m * (r*t) + b := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg he.pushes (fun _ _ _ => G.chord_nonneg _))
    apply (sum_le_sum (s := s) (fun p hh => hV p
      (Corona.halo_mono (by omega) (Subset.refl A.place) (hs p hh)))).trans
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    exact add_le_add_right
      ((sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => hH i)).trans hb') _
  have hlin := T.low.tail_pos
  have hz := mul_le_mul (mul_le_mul_of_nonneg_left htemp hlin.le) hthird
    (sum_nonneg fun _ _ => G.chord_nonneg _) (mul_nonneg hlin.le (show 0 ≤ 2*t by positivity))
  unfold talll; rw [sum_add_distrib]
  apply (sub_le_sub hz (add_le_add hx hy)).trans_eq
  unfold b r bill l E F preBill seatBill m u v g t Q
  rw [picked_sum, picked_sum]
  ring
end

theorem answer : YM.Bid.E07 := by
  intro e1 e3 e4 G P δ hδ
  obtain ⟨N, hN⟩ := e1 P δ hδ
  obtain ⟨a, ha, ha'⟩ := e3 P
  obtain ⟨d, hd, hd'⟩ := e4 e3 P
  obtain ⟨D, hD, hq⟩ := qdc G P.bind P.j
  let C := preBill P.top.clip P.below.clip P.bind a d D N
  have hl := P.below.clip.tail_pos
  refine ⟨C, by unfold C preBill macroLarge; positivity, fun L W hW => ?_⟩
  let Z := seatBill P.top.clip P.below.clip P.bind a d D W P.j L
  have hZ : 0 ≤ Z := by unfold Z seatBill macroSmall macroSize dCost; positivity
  refine ⟨Z*N + 1, by positivity, ⟨?_⟩⟩
  filter_upwards [(hN L W hW).late, (ha' L W).late, (hd' L W).late,
    radiusB_eventually (1 + N), temp_coarse_le G L]
    with x hx hxa hxd hB ht
  intro c f S he hsize T hT F A U k V hh hp
  obtain ⟨h1, hM⟩ := hx _ _ S he hsize T hT F A U k V hh hp
  have h2 := hxa _ _ S he hsize T hT F A U k V hh hp
  obtain ⟨h3, h4, hm⟩ := hxd _ _ S he hsize T hT F A U k V hh hp
  have hscore := price_at ha.le hd.le hD.le hW.le hB (by rw [he]; exact ht) hM hp
    (fun p h => (hq _ _ S hT.knobs.symm hT.atStep.symm U V p.1 k h p.2).2)
    h1 h2 hm (by rw [he]; exact h3) (by rw [he]; exact h4)
  -- quotes chosen at the promised scopes
  have hc' : preBill T.high T.low S.kernel a d D N = C := by
    unfold C; rw [hT.high, hT.low, hT.knobs]
  have hz' : seatBill T.high T.low S.kernel a d D W S.patch.J L = Z := by
    unfold Z; rw [hT.high, hT.low, hT.knobs, hT.atStep]
  rw [he, hc', hz'] at hscore
  intro Q t b
  let m : ℝ := (A.spend U Q V x).shares
  have hcast : ((A.hit U Q V x).card : ℝ) ≤ N * b^4 * m := by
    unfold b m Q; exact_mod_cast h1.covers
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have h : Z * t^2 * ((A.hit U Q V x).card : ℝ) ≤ (Z*N + 1)*t^2 * b^4 * m := by
    calc
      _ ≤ Z * t^2 * ((N : ℝ) * b^4 * m) := mul_le_mul_of_nonneg_left hcast (by positivity)
      _ = Z * N * t^2 * b^4 * m := by ring
      _ ≤ _ := by have H : 0 ≤ m := Nat.cast_nonneg _; gcongr; linarith
  have hpay : T.low.linear * temp x * (∑ i ∈ A.tides V x δ, toll V i) - talll T x U Q V (A.hit U Q V x) ≤
      C*t*((∑ i ∈ A.swell U t, toll U i)/(L.val : ℝ)^2 + ∑ i ∈ A.aisles, wire Q V i) +
        (Z*N + 1) * t^2 * b^4 * m := hscore.trans (add_le_add_right h _)
  apply (sub_le_iff_le_add.mp hpay).trans_eq
  unfold m
  ring

end YM.Work.E07
