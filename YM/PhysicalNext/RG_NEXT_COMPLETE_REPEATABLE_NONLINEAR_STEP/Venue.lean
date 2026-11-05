import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Instruments
import YM.PhysicalNext.SERVICE.Mixer


/-!
# One release on both sides of the local E/K calculation

Keep ownership of the **one** machine. In `authorized` not just a conjunction
with some paid Ξ family under other clocks. Even includes `Sworn` **at top**
on the revised metrics, needed for a molecule supplier. Implicit sequence
conventions all use `(N,m,p)` of the Bake. E6 & V9 may evaluate a DIFFERENT
stencil and hence a DIFFERENT covariance (e.g. look at `meeting` B/20 vs.
E6 `frames B`). This funds them together at the same parameters, kernels,
width w, chart, prices, and regards them as two separate proof obligations
when identifying any TERMS in the expansions; it does not license an identity
between those covariances! No separate operation on unmarked input normalizers.

Further costs for Actual or any linearized marked trajectory must still
be bought before L vs after θ as appropriate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {s : Sheet G} {O K : MapPrices} {l v : ℕ→ℕ} {D : Rolls (ThroughLaunch.raise s l)}
  {X : Further.StrongStartup.Tariffs} {Θ : Extra.Multi.Scope} {r : Bid.Worth} {u g k : ℕ→ℝ}
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (Builder.quote s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}

lemma fromBoost {G : Gauge} {s : Sheet G} {D : Rolls s} {T : Protection D} {W V : Delays T} (h : Boost V W) : DelayLe V W := ⟨h.1,h.2,h.3,h.4⟩
lemma asBoost {G : Gauge} {s : Sheet G} {D : Rolls s} {T : Protection D} {W V : Delays T} (h : DelayLe V W) : Boost V W := ⟨h.1,h.2,h.3,h.4⟩

abbrev radiusW (B : ℕ→ℕ→Cafe) j i := (B j i).r
abbrev billW (B : ℕ→ℕ→Cafe) j i := (B j i).E+1

structure Touring {M : Metals G} {J : Rolls M.p} {C : Programs M.p} {L : Targets M.p M.K} {X : Expenses L} {B : ℕ→ℕ→Cafe} {w : Return.Wages} (U : Alloy M J)
    (Bf : Baton G) (v t : Return.Wages) (r : ℕ→ℕ→ℕ) (b : ℕ→ℕ→Booth) (Q : ℕ→ℕ→JointLoad.Clockwork.Menu) (p : ℕ→ℕ→JointLoad.Heir.Record)
    (C' : ℕ→ℕ→JointLoad.Folio.Aux) {u} (Y : Register J X w u) {F : ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) (c : ℝ)
    (E : ℕ→ℕ→Next.Scheduling.Exchange) (q : ResetPrices) (η : ℕ→ℝ) : Prop where
  hearing : Psalm.Stage.Cadence M.O M.K U.delay b (Solo.guardMenu Q p) w B C Bf p v (Solo.raise t) r C'
  sustains : Solo.Sustained U.delay v
  machine : Use.Machine U.B E S η q w (radiusW B) (billW B)
  starts : Service.simpleOrigins U.B.kin
  full N m n : m≤N → Bid.Sworn (U.B.M.H N m) n G
  income : Receiving Y S U.delay c

-- deploy on ALL even bigger delays. SectionData costs retained for Guard consumers.
variable (hG : G.Simple) (h : ThroughLaunch.Pledge s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (Builder.quote s K) (chart G) C z t m E)
  (c : ℝ) (hc : 0<c) {u' : ℕ→ℝ} (R' : Register D E w u') (hy : Concert D w C (Builder.quote s K) (chart G) B bt)

include hG h h₀ hb hc R' hy

end YM.PhysicalNext.Repeat
