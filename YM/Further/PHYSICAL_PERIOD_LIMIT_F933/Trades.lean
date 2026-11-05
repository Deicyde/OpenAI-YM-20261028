import YM.Extra.ITERATION_NO_LOSS.Planned
import YM.Extra.MULTISOURCE_BOUNDS.SystemPrices
import YM.Extra.MULTISOURCE_TRAJECTORIES.Collision
import YM.Extra.SOURCE_HISTORIES.Retained
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Compass
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Harmonic
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Issuer
import YM.Next.MULTISOURCE.Journey
import YM.Next.UV_STRESS.Aligned
import YM.Progress.STATIONARY_SCENES.Dispatch
import YM.Progress.STATIONARY_SCENES.SliceGap
import YM.Push.ABSOLUTE_SUMS.Log
import YM.Push.RELAY_DIFFERENCE.SingleMajorant
import YM.Push.STRESS_FLUX.Ward


/-!
# Revised assembling

Expose pre-L opportunities for the *same* path now as charged.
`await` and `Turn.proves` suffice. Does NOT assert feasibility
of a booking/scheduling request or agree with existing cargos
before revision. Assumptions now in `.Serve`, `.Settle` on chosen
context after numerical purchase. Offers, Grids and Shell estimates may
need even FURTHER reservation e.g. chosen smaller Θ or higher thresholds than just
`Ledger.support`. Those are *our caller's* responsibility when trying
to prove the estimates. Additional gates not bought explicitly in this
proposal are not to be presumed available; can instead e.g. adjust
Ω/widths BEFORE calling rental or enroll etc (direct preserved),
and re-review purchases - or use an `Available` with even higher n and
β under `appointment`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Bourse
open Matrix Function Set Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work
    WilsonStartup Change Design F08 Extra.Iteration Supply Pressure
    Next.Foundations Next.Free Timing Input Org
    Extra Extra.Histories Cook Joint Extraction
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical ContDiff
-- pre declaration. Fix κ separately from comparator κ0. X=rolled.K supplies Γ on every J
variable {G : Gauge} {a : Levels G} {κ : ℝ} {hκ : 0 < κ} {J : Timing.OrderBook}
variable (M : Timing.Inception G κ hκ J)

structure Forecasts (K U : MapPrices) (s : Supply.Sheet G) : Prop where
  grant : World.Grant K U
  ready (a : Levels G) : (∀ m, (a.params m).clip.direct=(s.profile (a.clock.J m)).clip.direct) → (∀ i, (a.params i).clip.direct ≤ 1) →
    ∀ H : Horizon a,H.Suffices K → ∃ H', H'.Suffices U ∧ World.Tour a H' H

-- The second more conservative quote known before asking for R and TOP; Ringing charged at posts for this K',
-- new World chosen H' paying both K & K', still uses K in launch, K' used in Directed and by Fuel on later paths.
structure Floated (J : Timing.OrderBook) {κ : ℝ} {hκ : 0<κ} (M : Timing.Inception G κ hκ J) where
  K : MapPrices
  first : Forecasts M.K K M.p
  K' : MapPrices
  outsider : Forecasts K K' M.p



variable (X : Floated J M)

def ship := { M with K := X.K, rollback := fun q e a hi he H h =>
  let ⟨H',h₁,h₂⟩ := M.rollback q e a hi he H h; ⟨H',h₁,World.concedes X.first.grant h₂⟩ }





variable {R : Timing.Requests} {S : Timing.Layout (ship M X) R} {V : Timing.Reserves} {L : Timing.Ledger (ship M X) S V} {n : ℕ → ℕ} {β : ℕ → ℝ}
variable {D : Rolls {L.s with floorL:=n}} {B : Timing.Increments D} {price : ℝ} {Θ : Protection D} {Y H : Supply.Delays Θ} {Z : Bar H} {I : Wait Z}
variable (h : Timing.Available (ship M X) S L n β) (r : Timing.Rail (ship M X) S L (β:=β) B Y H price) (hG : G.Simple)

structure Harbor {Θ : Protection D} {H : Supply.Delays Θ} {Z : Bar H} (I : Wait Z) (hG : G.Simple)
    (a : Levels G) (H P Q : Horizon a) : Prop where
  old : Deployed (L:=L) I hG a H P
  initial : H.Suffices M.K
  appointment : Q.Suffices X.K
  outsource : Q.Suffices X.K'
  transport : World.Tour a Q H
  line N m : m ≤ N → ∀ p, Sworn (Q.H N m) (a.S.side m p) G
  wave N m : m<N → Harmonic (Q.towers N m)
  high i : Design.Suitable G (a.params i)

include h r hG
lemma harbor (I : Wait Z) : ∃ (a : Levels G) (T P Q : Horizon a), Harbor M X (L:=L) I hG a T P Q := by
  obtain ⟨a,_,P,d⟩ := Timing.deployed hG h B r Z I
  have he := d.run
  let N := ship M X
  have hp : Upgrade M.p L.s := Upgrade.chain S.cost L.cost
  have ht := he.kernel.trans hp.kernel
  obtain ⟨H,hH,h'⟩ := M.rollback L.s hp a he.stage ht P d.plates
  have ha (i : ℕ) : a.params i=L.s.profile (a.clock.J i) := congr_fun he.stage _
  have hx (i : ℕ) : Design.Suitable G (a.params i) := (ha i).symm ▸ L.startup _
  obtain ⟨T,hT,hQ⟩ := X.first.ready a (fun m=>ha m ▸ hp.direct _) (fun i=>(hx i).direct) H h'
  have hf := retained_presents a N.X P H d.sought d.plates hH
  refine ⟨a,H,P,T,
    { old := { d with keeps := hH, promise := World.concedes X.first.grant h' }
      initial := h'
      appointment := hT, outsource := World.concedes X.outsider.grant hT,transport := hQ,high := hx,
      line := fun u m hl p=> ?_,wave:=fun u m hl=>?_ }⟩
  · rcases hl.eq_or_lt with h|h
    · subst m; rw [hQ.peak]; exact top_sworn _ (hx u).direct
    rw [hQ.other _ _ h]; exact hf.2 u m _ h.le
  intro f g b c; rw [hQ.links u m hl]; exact PhysicalPeriodLimitF933.harmonic hf.1 _ _ hl f g b c

variable {Q T P : Horizon a} {e : Harbor M X (L:=L) I hG a T P Q} {f : Kin Q (Next.Foundations.chart G)} {v : Timing.Price (L:=L) D}
omit h

structure Checked (u : Harbor M X (L:=L) I hG a T P Q) (f : Kin Q (Next.Foundations.chart G))
    (P : Issuer.Passport a) (b : PostCost D) : Prop where
  planned : f.Planned b
  tags N m : m≤N → Issuer.Marking Q X.K R.U R.A N m (f.path N m) ∧ P N m (f.path N m)
  settled : Q.Suffices S.O -- actual Ringing charged on outsider
  fires (F : Builder.Gates a) : F.Pass → ∀ N p,
    Bid.Oust (Builder.assign u.old.run (chart_ok G) settled planned F) N p

include h
lemma validate (hx : Issuer.Coffers {L.s with floorL:=n} R.A) (hk : S.O=X.K') (u : Harbor M X (L:=L) I hG a T P Q) (P : Issuer.Passport a)
    (hv : Issuer.Sensors Q X.K R.U R.A R.H (ceiling (v:Timing.Price D) B) (Next.Foundations.chart G) P) :
    ∃ f : Kin Q (Next.Foundations.chart G),Checked M X hG u f P (ceiling v B) := by
  obtain ⟨t,H,hT⟩ := Issuer.expedition (L.fit.boost h.earlier) r.lateStep u.old.run u.appointment (v.serves _ rfl)
    (chart_ok G) u.line u.wave u.transport hx hv u.high
  have Hcore n : t.path n n = Design.top G (a.params n).clip := (hT n n le_rfl).1.finished rfl
  have HS : Q.Suffices S.O := hk.symm ▸ u.outsource
  exact ⟨t,H,hT,HS,fun F hF => Builder.launched u.old.run (chart_ok G) HS H F hG Hcore hF r.wilson⟩

variable {h}
omit h
-- choose V dollars before D, but passport and recipe after Levels. estimates still at deadlines
section AfterChecked
variable {Z' : Issuer.Passport a} (c : Checked M X hG e f Z' (ceiling v B))

/-- From here physics probes use exactly Q and f and the *literal* top path even though many atoms are 0. -/
abbrev canopy (F : Builder.Gates a) := Cook.chief hG r e.old.run c.settled c.planned F
variable {F : Builder.Gates a} (u : Bolt (canopy M X r hG c F))

abbrev pal : Backstory (L:=L) (D:=D) a := ⟨_,u,rfl⟩
include r u
lemma approved : Raw (U:=I) hG (pal M X r hG c u) r :=
    ⟨fun N p=>(u.sticks N p).fromTop.inits.2, e.old.run,e.old.history⟩
end AfterChecked

open Joint
/-- Remaining commissions.

Now along the activist not every Bolt at
this L.

`Passport` and `F` opportunity to restrict proper analytic
requests, at cost of having to pay retention prior to new Sensors or
Rebuild calls!

Financial input on book is still the genuine campaign & corrected/weak/Grid/endgame
from PartII, including the Rank Wears/Rain (only when finrank ≠0), no hiding
these as IP-birth etc.

Upstream to `Commission` compare Bought.lean:
**S.O, M.K, travel and Γ's are different!** so don't literally infer this from old
Scheduling assumption or vice versa. -/
structure Duties {h : G.Simple} {r : Timing.Rail (ship M X) S L (β:=β) B Y H price}
    (q : Harbor M X (L:=L) I h a T P Q) (v : Timing.Price (L:=L) D) : Prop where
  shifts : ∃ M0 : Issuer.Passport a, Issuer.Sensors Q X.K R.U R.A R.H (ceiling v B) (Next.Foundations.chart G) M0 ∧
    ∀ f : Kin Q (Next.Foundations.chart G), ∀ p : Checked M X h q f M0 (ceiling v B),
    ∃ Z : Builder.Gates a, Z.Pass ∧ Rebuild.Actual (canopy M X r h p Z).B V.census B.fuel ∧
      ∀ w : Bolt (canopy M X r h p Z),
      let b := pal M X r h p w
      let t := approved M X r h p w
      Ingredients h I b r t ∧
        ∀ T₁,∀ _ : Readies h I b T₁ r t,∀ W : Joint.Comparator (family b T₁),
        ∃ (A : Push.CutoffProjectors.Campaign (family b T₁)) (e : Extraction.Order), Nonempty (Joint.Estimates _ B L.W W A e)

structure Enlisted (h : Timing.Available (ship M X) S L n β) (r : Timing.Rail (ship M X) S L (β:=β) B Y H price)
    (q : Harbor M X (L:=L) I hG a T P Q) (v : Timing.Price (L:=L) D) where
  genus : Issuer.Passport a
  f : Kin Q (Next.Foundations.chart G)
  actual : Checked M X hG q f genus (ceiling v B)
  Z : Builder.Gates a
  used : Z.Pass
  predicted : Rebuild.Actual (canopy M X r hG actual Z).B V.census B.fuel
  γ : Bolt (canopy M X r hG actual Z)
  T₁ (d N p : ℕ) : Source.TransferData ((Labels.frames G).level d) (closedTrail _ (pal M X r hG actual γ).V) N p
  frozen : Readies hG I (pal M X r hG actual γ) T₁ r (approved M X r hG actual γ)
  F' : Extraction.Order
  W : Joint.Comparator (family (pal M X r hG actual γ) T₁)
  units : Push.CutoffProjectors.Campaign (family (pal M X r hG actual γ) T₁)
  receipts : Joint.Coupons (A:=units) W F'
  payments : UVNext.Grade.Recorder (family (pal M X r hG actual γ) T₁) units.presentation F'
  offers : Joint.Estimates _ B L.W W units F'

lemma licensed (hc : Issuer.Coffers {L.s with floorL:=n} R.A) (hk : S.O=X.K') (q : Harbor M X (L:=L) I hG a T P Q)
    (b : Duties M X q v (r:=r)) (Z : Timing.Available (ship M X) S L n β) : Nonempty (Enlisted M X hG Z r q v) := by
  obtain ⟨V₀,hV,h₁⟩ := b.shifts
  obtain ⟨f,hF⟩ := validate M X Z r hG hc hk q V₀ hV
  obtain ⟨U,hP,hh,E⟩ := h₁ f hF
  obtain ⟨B'⟩ := winning (A:=canopy M X r hG hF U) hG (Rebuild.program _ r.recalc Z.remake (fun _ => le_rfl) (hF.fires U hP) hh)
  let w := pal M X r hG hF B'
  let u := approved M X r hG hF B'
  obtain ⟨hsamples,hW⟩ := E B'
  obtain ⟨T,hT⟩ := Cook.assemble hG I w r u hsamples
  obtain ⟨B₀⟩ := Joint.comparator hG (Cook.family w T)
  obtain ⟨A,K,⟨Yt⟩⟩ := hW T hT B₀
  let C := Cook.family w T
  have hL : Extra.Histories.Doors.Budget C.path.levels V.source L.W := hT.printed.terms
  obtain ⟨P'⟩ := Joint.inventory hG Yt hL.bank hL.room (Push.Corrected.Zone.Coverage.paysEarlier hG I (show Paid _ C.path.levels from q.old.run)) r (hT.center K)
  exact ⟨V₀,f,hF,U,hP,hh,B',T,hT,K,B₀,A,P',Joint.roll P' hG hT.calibrated Yt,Yt⟩

/-- Tickets at a given commission on a given chosen scroll. -/
structure Appointment (v : Timing.Price (L:=L) D) (Z₀ : Timing.Available (ship M X) S L n β) (h : G.Simple) : Prop where
  fund : ∃ (B : Timing.Increments D) (aperture : ℕ → ℝ), (∀ i, 0 < aperture i) ∧
    ∃ pressure : ℝ, 0 ≤ pressure ∧ ∀ Θ : Protection D, (∀ i, Θ.theta i ≤ aperture i) → ∃ bells : Supply.Delays Θ,
    ∀ Y : Supply.Delays Θ,∀ r : Timing.Rail (ship M X) S L (β:=β) B bells Y pressure,
    ∃ ζ : ℝ, ∀ Z : Bar Y, ζ ≤ Z.value → ∃ V : Wait Z,
      ∀ (a : Levels G) (H K U : Horizon a) (q : Harbor M X (L:=L) V h a H K U), Duties M X q v (r:=r)

-- explicit pre-let after-Harbor obligations after selecting schedules and proving numerical estimates even with other strengthened (RFuture) bells & aperture controls.
omit r
lemma paid (hx : Issuer.Coffers {L.s with floorL:=n} R.A) (hu : S.O=X.K') {Z0 : Timing.Available (ship M X) S L n β}
    (he : Appointment M X v Z0 hG) : ∃ (B : Increments D) (Θ : Protection D) (X0 Y : Supply.Delays Θ) (Z : Bar Y) (I : Wait Z) (a : Levels G)
      (price : ℝ) (d : Timing.Rail (ship M X) S L (β:=β) B X0 Y price) (T P Q : Horizon a),∃ q : Harbor M X (L:=L) I hG a T P Q,
        Nonempty (Enlisted M X hG Z0 d q v) := by
  obtain ⟨B,A,hA,p,hp,hu'⟩ := he.fund
  obtain ⟨T,hT⟩ := Protection.exists_margin _ A hA
  obtain ⟨h,u⟩ := hu' T hT
  obtain ⟨Y,hY⟩ := Z0.rails hG B p hp T h
  obtain ⟨t,ht⟩ := u Y hY
  obtain ⟨K,hK⟩ := Bar.exists_above Y t
  obtain ⟨I,hI⟩ := ht K hK
  obtain ⟨a,T',P,Q,H⟩ := harbor M X Z0 hY hG I
  exact ⟨B,T,h,Y,K,I,a,p,hY,T',P,Q,H,licensed M X hY hG hx hu H (hI a T' P Q H) Z0⟩

-- some context left in promises, but remove notably-for-all M, arbitrary Price and
-- beta choices, D, arbitrary second-retarget data, arbitrary PerBlock (only on some recipe uh).
-- Does NOT conjecture this universal yet: such promises could even be false or unquantifiably
-- high antecedent scope at separated steps (rail buys, Calendar unanticipated weak-profile
-- gates like overlap etc, staff for *any* Printed and any Sectored deadlines), or simultaneous
-- ones. Harbor on these final thresholds (incl arbitrarily *LARGE* L for the promised stage)
-- might still pay insufficient analytic/aesthetic error: see report; use lamina variant with
-- earlier requests per-analysis budgets if necessary. Also no claim even sufficient
-- pricing/order *exists* for E.S.density across all J.


omit hG



end YM.Further.PhysicalPeriodLimitF933.Bourse
