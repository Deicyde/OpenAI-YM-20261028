import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
import YM.Next.FLUCTUATIONS.Prediction
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.Push.SECTOR_MEASURE.Bounds

/-!
# Stencil/delay hypotheses used here

Size conventions for local calls. No need to fit whole Stores into one
nonwrapping box. `Works` carries **no input path** beyond service
Funds available at this T in all those calls. Actual directed supply at
`intake_at`, width & delay to be furnished at its calendar. Histories
need a lot more than this for continuation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure   Bid Next.Fluctuations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

structure Works (P : Teller G) (L : Side) (x : ℝ) (S : StepData c f) (T : Tube G S) : Prop where
  funds : P.Funds S T
  length_eq : S.patch.L=L
  fits : 100*(1+radiusB x) ≤ c.val

lemma no_turn (S T : Patch) (h : S.L=T.L) (hg : S.J=T.J) : S=T := by cases S; cases T; congr

lemma Works.patch {L : Side} {P : Teller G} {x : ℝ} {T : Tube G S} {D : Patch}
    (h : Works P L x S T) (hL : D.L=L) (hm : D.J=P.j) : S.patch=D :=
  no_turn _ _ (h.length_eq.trans hL.symm) (h.funds.atStep.trans hm.symm)

/-- More than enough for all core/annulus analytic stencils. Potential
seed queries under integrations may require more room in their supports:
consult constructors there (may themselves wrap). -/
structure Room (P : Teller G) (S : StepData c f) (T : Tube G S) (x : ℝ) : Prop where
  signs : 0<x
  fiery : 0< fiery G x S.patch.L
  accepted : P.Funds S T
  temperatures : Pressure.temp x ≤ 2 * Pressure.fiery G x S.patch.L
  -- Any lift around radius (output coarse) < 50*(B+1) unique
  buys : 100*(1+radiusB x) ≤ c.val
  frame : 10000*(predReach S.patch + Pressure.macroR S.patch + S.patch.L.val + 10) ≤ radiusB x
  laneU : ∀ k : ℕ, Pressure.fiery G x S.patch.L*Real.exp (k/T.high.relaxation) < 2 → k+2 ≤ radiusB x/25
  laneV : ∀ k : ℕ, Pressure.temp x*Real.exp (k/T.low.relaxation) < 2 → k+2 ≤ radiusB x/25

lemma room (G : Gauge) (P : Teller G) (L : Side) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L x S T → Room P S T x := by
  by_cases hp : ∃ D : Patch,D.L=L ∧ D.J=P.j
  swap
  · exact Eventually.of_forall fun _ _ _ S _ hw => (hp ⟨S.patch,hw.length_eq,hw.funds.atStep⟩).elim
  obtain ⟨D,hL,hD⟩ := hp
  let z := G.slopeConstant * Real.log L.val
  filter_upwards [Work.E09.betaF_growth G L |>.eventually (eventually_gt_atTop 0),
    Work.E04.eventually_room z _ P.top.clip.radius_pos,
    Work.E04.eventually_room 0 _ P.below.clip.radius_pos,
    Work.E04.eventually_temp_le z (Work.E04.shift_nonneg G L),
    Work.E08.eventual_radiusB (10000*(predReach D + Pressure.macroR D + D.L.val + 10)),
    eventually_gt_atTop (0:ℝ)] with x hpos hT hB hv hd ht c f S T hw
  have he := hw.patch hL hD
  have hh := hw.length_eq
  simp only [add_zero] at hB
  refine ⟨ht,hh.symm ▸ Work.E09.temp_pos hpos, hw.funds, hh.symm ▸ hv,hw.fits, by rw [he]; exact hd,
    fun k H => ?_, fun k H => ?_⟩
  · rw [hw.funds.high, hh] at H
    have H := hT.2 k H; omega
  rw [hw.funds.low] at H; have H := hB.2 k H; omega

lemma Room.larger {x : ℝ} {P : Teller G} {T : Tube G S} (h : Room P S T x) : Bid.Larger (G := G) S := by
  have hu := h.frame; have hv := h.buys
  have he : c.val ≤ f.val := by
    rw [S.sizes]; exact le_mul_of_one_le_right (by omega) S.patch.L.property
  exact ⟨funds_branch h.accepted,by omega,by omega⟩

lemma Room.sight {x : ℝ} {P : Teller G} {T : Tube G S} (h : Room P S T x) :
    let B := radiusB x
    100 ≤ B ∧ 4*till x+4+predReach S.patch ≤ B/100 := by
  have he := h.frame; dsimp only [till]; omega

lemma serves_void (A : Teller G) (L : Side) (Q : ∀ {c f : Side} (S : StepData c f), Tube G S → ℝ → Config G c → Prop)
    {W x : ℝ} (hq : Teller.live A L W (fun S T _ _ x _ _ V => Q S T x V) x) (T : Tube G S)
    (hp : Works A L x S T) (V : Config G c) : Q S T x V := by
  let F : Forest S.ratio := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  let X : Stores S := ⟨∅,∅,∅⟩
  have hx : ∀ i : Site c, i ∉ X.dome (5*radiusB x) := by simp [Stores.dome,X,place,halo_spec]
  refine hq c f S hp.length_eq hp.fits T hp.funds F X (1:Config G f) (Classical.arbitrary _) V (fun _ _ => rfl) ?_
  have ht : X.dome (5*radiusB x)=∅ := by ext i; simp [hx]
  refine ⟨?_,?_,fun i hi => (hx i hi).elim,fun i hi => (hx i hi).elim⟩ <;> simp [ht]

/-- In particular may use when constructed words outlive the Plot
point but pull the real T costs at V or its local gauge rotation. -/
theorem max_prices (P : Teller G) : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ L : Side,
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L x S T →
      (LaneCounts T.up x (Pressure.fiery G x L) T.high A 1 S.ratio.parent ∧
       LaneCounts T.down x (Pressure.temp x) T.low A L.val (id : Site c→Site c)) ∧
      ∀ (V : Config G c), Maximum A T x V ∧ Allowance C T x V := by
  obtain ⟨C,hC,H⟩ := @Work.E03.answer _ P
  obtain ⟨A,hA,h⟩ := Work.E04.answer Work.E03.answer P
  refine ⟨A,C,hA,hC,fun L => ?_⟩
  filter_upwards [(H L 1).late,(h L 1).late] with x hX hY c f S T he
  have hx V := serves_void (G:=G) P L (@fun c f S T x V => Allowance C T x V) hX T he V
  have ht (V : Config G c) := serves_void P L (@fun c f S T x V =>
      LaneCounts T.up x (Pressure.fiery G x L) T.high A 1 S.ratio.parent ∧
       LaneCounts T.down x (Pressure.temp x) T.low A L.val (id : Site c→Site c) ∧ Maximum A T x V) hY T he V
  exact ⟨⟨(ht 1).1,(ht 1).2.1⟩,fun V => ⟨(ht V).2.2,hx _⟩⟩
end YM.ConnectedActivityE6
