import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger

/-!
# B70 commissioning at the earlier Local (R1) estimates on the common family

Strongly recommended read REPORT before commissioning. This version
also organizes the outstanding PhysicalPeriodLimitF933 Bequests incl choices ensuring ALL
fit on one context per d. No assertion that the bequests are true (many
incompatibilities encountered, some repaired up to this scope). -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Awaken
open Function Set Matrix MeasureTheory Filter RG Wilson Lattice Precision Pressure Supply Bid Craft Tree Bloch
    Extra.Iteration WilsonStartup Labels Source Org Input
    Next.Foundations Timing Next.Free Extra.Histories Bay  Disk
    Extraction Next.Extract Push.Common UVNext.Grade Joint Bourse Sectioning
    Symphony
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {κ : ℝ} {hκ : 0 < κ} {J : Timing.OrderBook}
variable {M : Timing.Inception G κ hκ J} {X : Bourse.Floated J M} (P : Bay.Roads G) (T : Rerequests.Caps G)
  {R : Timing.Requests} {S : Timing.Layout (Bourse.ship M X) R} {V : Timing.Reserves} {L : Timing.Ledger (Bourse.ship M X) S V} {n : ℕ → ℕ} {β : ℕ → ℝ}
variable {D : Rolls {L.s with floorL:=n}} {B : Timing.Increments D} {price : ℝ} {Θ : Protection D} {Y H : Supply.Delays Θ} {Z : Bar H} {I : Wait Z}
variable (h : Timing.Available (Bourse.ship M X) S L n β) (r : Timing.Rail (Bourse.ship M X) S L (β:=β) B Y H price) (hG : G.Simple)
open Rerequests
open Symphony Inflation
section Safe
variable {u : Levels G} {J0 Hp Q : Horizon u} {f : Kin Q (Next.Foundations.chart G)} {v : Timing.Price (L:=L) D} {i : Symphony.Inflation}
variable {q : Harbor M X (L:=L) I hG u J0 Hp Q} {Y₀ : Issuer.Passport u} (c : Checked M X hG q f Y₀ (Timing.ceiling v B))
  {F : Builder.Gates u} (b : Bolt (canopy M X r hG c F))

open Next.Foundations

abbrev Ward (l : ℕ→ℕ) := ∀ d (N p : ℕ), l d ≤ N → 4 ≤ d → Ink (history r hG c b) N p

abbrev WardOffers {l : ℕ→ℕ} (B0 : Ward r hG c b l) := ∀ d (N p : ℕ) (hl : l d ≤ N) (ht : 4 ≤ d), Goods (B0 d N p hl ht) (localSection G d) (hol G) (l d)

variable {r hG c b}

structure Feasible (l : ℕ→ℕ) (i : Inflation) (B0 : Ward r hG c b l) (B1 : WardOffers r hG c b B0) : Prop where
  local_ d (N p : ℕ) (hl : l d ≤ N) (ht : 4 ≤ d) : Rerequests.Requests (B0 d N p hl ht) (B1 d N p hl ht) T P
  honors (X1 : Small.High (history r hG c b) l) :
    (Small.Fit (history r hG c b) P X1 L.W ∧
     ∀ d N p (h1 : l d ≤ N) (h2 : 4 ≤ d), let Y:= X1 d N p h1 h2; let K:= B0 d N p h1 h2;
        Y.pad=K.cover ∧ Y.ink=0 ∧ Y.flight.rods = fun i => K.roles i (localSection G d)) →
    voices r hG c b i l X1 ∧
    ∀ T, Small.WagesHigh _ P T X1 L.W → let C₀ := Bay.book (history r hG c b) l T;
                                         (∀ N p,Extra.Multi.Thick C₀ N p) → Toy.Luxury C₀ B.multi ∧
                                          ∀ i : Joint.Comparator C₀, ∃ f : Extraction.Order, Nonempty (Symphony.Crewed B C₀ (Small.inventory (E:=Bay.chart P _ _ _) (Small.tint _ P _ X1)) i f)
-- Doesn't yet restrict φ purchasing to the literal generated Flow (equality .play), but same rods/ink/pad promise. Critical that BOTH volatility and Servo bills use its actual .flow.

def Admissible (H : History G) (P : Bay.Roads G) (l : ℕ→ℕ) := ∀ d, d+3 ≤ H.levels.clock.J (l d) ∧ (∀ i,l d ≤ i → Push.Local.hitWidth (H.levels.budget i)*Push.Local.kappa H i ≤ 1) ∧
    ∀ (N p : ℕ), l d ≤ N → ∀ o : Site (H.S.side N p), WardBin.Offsets.OffsetPrice (Bay.earlier P H d) (N:=N) (p:=p) o

-- includes prereq from Desk prior to Earned. Need V.source pressure charges chosen as in `Broker.price`.

end Safe
structure Care (P : Roads G) (M0 : Rerequests.Caps G) (h : G.Simple) (v : Timing.Price (L:=L) D) : Prop where
  purchase : ∃ (B : Timing.Increments D) (aperture : ℕ → ℝ), (∀ i, 0 < aperture i) ∧
    ∃ pressure : ℝ, 0 ≤ pressure ∧ ∀ Θ : Protection D, (∀ i, Θ.theta i ≤ aperture i) → ∃ (bells : Supply.Delays Θ) (b : Inflation),
    ∀ (Y : Supply.Delays Θ), bells.betaEntry ≤ Y.betaEntry → bells.shells ≤ Y.shells → bells.growth ≤ Y.growth → bells.scaleEntry ≤ Y.scaleEntry → Elevation Y b →
    -- we raised bells before rail, so asking OnPage and other exactcustom
    ∀ (H : Supply.Delays Θ) (r : Timing.Rail (ship M X) S L (β:=β) B Y H pressure), Elevation H b →
    ∃ ζ : ℝ, ∀ Z : Bar H, ζ ≤ Z.value → ∃ V0 : Wait Z,
      ∀ (a : Levels G) (U K Q : Horizon a) (q : Harbor M X (L:=L) V0 h a U K Q),
      ∃ T : Issuer.Passport a, Issuer.Sensors Q X.K R.U R.A R.H (Timing.ceiling v B) (Next.Foundations.chart G) T ∧
    ∀ f : Kin Q (Next.Foundations.chart G), ∀ p : Checked M X h q f T (Timing.ceiling v B),
    ∃ Z : Builder.Gates a, Z.Pass ∧ Rebuild.Actual (canopy M X r h p Z).B V.census B.fuel ∧
      ∀ w : Bolt (canopy M X r h p Z), ∀ l,
        Admissible (history r h p w) P l → ∃ B0 B1, Feasible P M0 l b (c:=p) (b:=w) B0 B1









end YM.Further.PhysicalPeriodLimitF933.Awaken
