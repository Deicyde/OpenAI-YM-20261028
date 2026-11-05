import YM.Bid.Market
import YM.Bid.Town
import YM.Next.BOUNDARY.Stage
import YM.Next.BOUNDARY.Synchronize
import YM.Work.A01
import YM.Work.A02
import YM.Work.A03
import YM.Work.A04
import YM.Work.A05
import YM.Work.A06
import YM.Work.A08
import YM.Work.A09
import YM.Work.A10
import YM.Work.A11
import YM.Work.A13
import YM.Work.A14
import YM.Work.A15
import YM.Work.A17
import YM.Work.B01
import YM.Work.B02
import YM.Work.B03
import YM.Work.B05
import YM.Work.B07
import YM.Work.B08
import YM.Work.B09
import YM.Work.B11
import YM.Work.B12
import YM.Work.B13
import YM.Work.B14
import YM.Work.B15
import YM.Work.B16
import YM.Work.B17
import YM.Work.B18



/-!
# CONDITIONAL through to Spec.CLOSED

Scope check with a single extraction, retaining Seed and Climb
requirements. No physical construction claimed.

Remaining-input ledger for this version:

Includes already the huge physics
requirements of compatible Metals/Rolls/Alloy (pre AND post pricing), Bolt
(unmarked vacuum Program, history incl Stays/Selected/Moves), cutoff Family
with `Assembly` (history link and Metered including C.Makes and Fuel for
every d,R>0).

Thus e.g. neither multi-source marker estimates nor step/launch
budget conditions have been removed by this interface!

Use conjunction INSIDE the existential, thus haven't
solved earlier coherence questions e.g. retuning schedule, support,
parameters of RG estimates, obtaining stress data for these objects.

Preserve
the ∀ D in the exact `YU` request.

The f here won't generally be the Final
one; we prove the countable common-refinement step above these inputs.

No
independent choice of S even at these early ports.

* And `Bid.Miles` (outer spectral/rotation inputs) and `Bid.Seats`
(replica/slab estimate preparation at unselected).

Neither assumed from the
Assembly program or OS heat positivity or any accepted A,B,C bid; both
explicit remaining research problems.

No claim these remaining problems can
be solved, or ought be taken as axioms.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY
open Boundary Extraction Spec Org
open RG.Supply

/-- Outstanding requests, see ledger and `AtRank`, `AtGrid`. In particular,
as with YU, all the history and the conditions up through choice of f for
the subprojects have to be satisfied TOGETHER. A way to specialize later
stage quantitative obligations *without* asking everyone to produce their
estimates already in the common final refinement. This is still likely very
hard or possibly false.
-/
def Producers : Prop :=
  ∀ (G : Gauge), G.Simple → ∃ M : Metals G, ∀ D : Rolls M.p,
    ∃ (A : Alloy M D) (B : Bolt A) (C : Family G), Assembly B C ∧
    ∃ (f : Order) (S₀ : Table C.book) (P : ℕ → Table C.book), Arrives C f S₀ P ∧
    ∃ (S : Table C.book) (V : DiffPlan S), Cleaner S₀ P S V f ∧
      AtRank C f S ∧ AtGrid C f S ∧
      ∀ (g : Order) (s : Seed C (f.refine g) S), Grill C (f.refine g) →
        ∃ (W : MaxwellData C) (I : IR (C:=C) S), Climb.Pre s.kernel V I.J I.p I.Y ∧
          Climb.ActLaw V W.T I.J s.kernel.spin W.hT.spin

theorem yu_from_producers (h : Producers) : YU := by
  intro G H
  obtain ⟨M, hM⟩ := h G H
  refine ⟨M, fun D => ?_⟩
  obtain ⟨A,B,C,hB,f,S₀,P,R,S,V,hC,a,b,c⟩ := hM D
  obtain ⟨g, hp, hc, W, I, he⟩ := synchronized H hB R hC a b c
  exact ⟨A, B, C, hB, f.refine g, S₀, P, hp, S, V, hc, W, I, he⟩



/-- Use `UV` and the earlier receipts at the SAME (synchronized) Order and
objects with the proven Bid/Work answers. Get the actual endpoint including
the new smooth compatibility work, also keeping the known sector. (Compose
directly with `synchronized`, no global `Producers` needed if
working on a particular supplied `Alloy`/extraction.) -/
theorem at_order
    {G : Gauge} {M : Metals G} {D : Rolls M.p} {A : Alloy M D} {B : Bolt A} {C : Family G}
    (hB : Assembly B C)
    {f : Order} {S₀ S : Table C.book} {P : ℕ → Table C.book} {V : DiffPlan S}
    (hc : Cleaner S₀ P S V f)
    {W : MaxwellData C} {I : IR (C:=C) S} (H : UV C f S V W I)
    (miles : Bid.Miles) (seats : Bid.Seats) :
    ∃ (c : ℝ) (U : ∀ d, Spin.change S d) (J : S.Stress), Tab S V W I H c U J ∧
      ∃ (K : Spins S), K.Descends (mill W I c U) H.basis.kernel.spin ∧
        ∃ F : Final C f S, F.sector=⟨V, mill W I c U, J⟩ ∧ F.action.spin=K ∧
          Compatible S F.α.unselected F.sector K F.room.kernel.spin F.B ∧
          Compatible S F.α.slabs F.sector K F.room.kernel.spin F.A := by
  have ht := Bid.station W V I H miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, T, K, hK⟩ := ht.picks V W I H hc.ready hc.tilt
  let X : Algebra S := ⟨V, mill W I c U, J⟩
  have he := Bid.Looms seats Work.B01.answer Work.B02.answer Work.B03.answer Work.B04.answer
    Work.B05.answer Work.B06.answer Work.B07.answer Work.B08.answer Work.B09.answer
    Work.B10.answer Work.B11.answer Work.B12.answer Work.B13.answer Work.B14.answer
    Work.B15.answer Work.B16.answer Work.B17.answer Work.B18.answer H.tables H.basis X
  obtain ⟨α, hα⟩ := he.cleanse T.locality
  obtain ⟨x, y, Z, hZ, h, hu, hw⟩ := after_materializes (s:=H.basis) hα K hK
  have HY : Calibrated C :=
    ⟨M.p, D, A.θ, A.delay, A.bar, A.asks, M.O, M.K, A.post, A.B, B.history, B.sticks, hB.imported, B.moves⟩
  exact ⟨c, U, J, T, K, hK, ⟨HY, H.basis, X, α, hα, x, y, Z, h⟩, rfl, hZ, hu, hw⟩

/-- **Conditional** on the ledger. This is NOT existence. -/
theorem consequence (P : Producers) (miles : Bid.Miles) (seats : Bid.Seats) : CLOSED := by
  intro G H
  obtain ⟨M, hM⟩ := yu_from_producers P G H
  obtain ⟨D⟩ := Rolls.exists_rolls M.p H
  obtain ⟨A,B,C,hB,f,S₀,P,R,S,V,hC,W,I,he⟩ := hM D
  obtain ⟨_, _, _, _, _, _, F, _, _, _, _⟩ := at_order hB hC he miles seats
  exact ⟨C, f, S, ⟨F⟩⟩
end YM.Next.BOUNDARY
