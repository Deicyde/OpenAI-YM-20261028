import YM.Bid.Town
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Calendar
import YM.Next.ProgressOct10
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# RScene on Rolls: fix post-L gap prices, deliver on the actual Horizon

This node does NOT require that W_N has already been produced. Its service
is uniform in the input `PathData` (precisely `Funded`), at all cutoff levels
and all periods `p`. Thus it can for instance be used inside the recursion
from its top with these proofs as part of its INDUCTION hypothesis. The
constructor `subscribe` doesn't even require inhabitation of `Funded` yet.
(We'll give concrete width invoices for ell-only uses too.)

The `Beam` is NOT a physical hypothesis. `issue` earns it via SCHEDULE
(`funded_from_verified`, itself using `activate`, `Beam.alight`, using F01
and F04 etc.). η is post-L (already pre-Delays and pre-every such `PathData`);
we don't enlarge or shrink it at some period. Racks from `Catalog` through
`Next.Free.shelves` from FREE_KERNELS, keeping also Sworn. No modifications
of accepted interfaces. In particular don't separately call `before_paid`
getting a *different* K to go with the schedule. Use `Survey.X` as the RRack
quote, get the scheduling K, then use *its* offers (pinning using F06–9 with
the same profile forecast/clock). No T/D confusion. `issue` even carries
other numerical receipts with it to ease integration; costs numerical scopes
ONLY, no implication their remaining nonlinear Wilson invoices are payable.

Use `on_retained` to install also directly on any such funded retained horizon
keeping every Horizon choice. No Wilson representation itself selected here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes

open Filter Lattice RG RG.Supply Precision Bid Pressure Tree
open YM.Next
open YM.Next.Scheduling
open YM.Next.Scheduling.Weak
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {a : Levels G}

/-- Input invoice at *exactly* this budget; no post-out quoting. To use from the
classical recursion, need a way to keep supplying such inputs at arbitrary depth
in the same stage and on transitions. -/
structure Funded (H : Horizon a) (N i : ℕ) (P : PathData G) : Prop where
  bound : P.Bounds (a.params i).clip (a.params i).width (a.params i).paths (a.clock.loopCap i)
  ties : Attached (H.H N i) P

/-- Real stationary data for the step `m+1 → m`. Fixed *same path input* for
every p. The solution works for ANY tag family of that `op`. Keep path and tags
also when calculating higher orders. There is no infinite-volume critical point
here. `comptroller` deliberately exposed for other estimates. -/
structure Answer (H : Horizon a) (N m : ℕ) (P : PathData G) (η : ℝ) where
  station (p : ℕ) (F : Forest (a.clock.op m p).ratio) :
    Dir G (a.S.side m p) → AxisChart G F
  price : 0 < η
  testimony (p : ℕ) (F : Forest (a.clock.op m p).ratio) :
    let c := (a.params (m+1)).clip
    Comptroller F (H.H N (m+1)) c P ∧
      PriceGap F c P η ∧ Critical F c P (station p F) ∧
      Guessed F (Bloch.installed (a.clock.op m p).ratio (H.towers N m).A0) (station p F) ∧
      HeatG F c P (station p F) (H.H N m)

section coverage
variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
  {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
  {B : Beam K D} {t : ℕ → ℕ → Postage}

/-- Frame/Larger from the actual paid step in this funding. -/
def regionHere (h : Paid I a) (g : Regime B e t W) (m p : ℕ) :
    Region (a.clock.op m p) G :=
  buildRegion (Deployment.step_larger h g m p)

/-- Keeping ANY such H. `B` contains the fixed-L *implications* earned
upstream via `Beam.alight`; see `issue` issuing it from the library. Use here
even with already built schedule. -/
theorem answer_exists (h : Paid I a) (g : Regime B e t W) {M H : Horizon a}
    (hM : Craft.Rack a s.X M) (hr : Retained H M) (hh : H.Suffices K)
    {m N : ℕ} (hk : m < N) {P : PathData G} (hP : Funded H N (m+1) P) :
    Nonempty (Answer H N m P ((B.price t).η (a.clock.J (m+1)))) := by
  have hf p : Sworn (H.H N (m+1)) (a.S.side (m+1) p) G := by
    rw [hr.1]; exact hM.oath _ _ _ hk
  have hs p := Deployment.scene h g m p N hk H hh P hP.bound hP.ties (hf p)
  choose ρ hρ using fun p (F : Forest (a.clock.op m p).ratio) => ((hs p) F).2
  refine ⟨ρ, (B.price t).price _, fun p F => ⟨?_, ((hs p) F).1, hρ p F⟩⟩
  exact (Work.F03.answer _ _ _ _ (Deployment.step_larger h g m p) F _ _ _ _ _ _ _ _
    (hh.all N (m+1) hk _) hP.bound hP.ties (hf p) (Work.F02.answer _ _ _ _ _ _ hP.bound)).2

end coverage

/-- Install without rerolling the horizon. Store Suffices; also store the
signed quadratic invariance (on every period). -/
structure Service {S : Sheet G} {D : Rolls S} (a : Levels G) (K : MapPrices) (Q : PostCost D)
    (H : Horizon a) where
  stage : a.clock.stage = S.profile
  lengths : a.clock.factor = D.L
  kernel : a.clock.kernel = S.kernel
  rooms (m p : ℕ) : Region (a.clock.op m p) G
  covered : H.Suffices K
  sworn N m p : m ≤ N → Sworn (H.H N m) p G
  sends {N m : ℕ} {P : PathData G} : m < N → Funded H N (m+1) P →
    Answer H N m P (Q.η (a.clock.J (m+1)))

section horizons
variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
  {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
  {B : Beam K D} {t : ℕ → ℕ → Postage}

def on_retained (h : Paid I a) (g : Regime B e t W) {M H : Horizon a}
    (hM : Craft.Rack a s.X M) (hr : Retained H M) (hh : H.Suffices K) :
    Service a K (B.price t) H where
  stage := h.stage
  lengths := h.lengths
  kernel := h.kernel
  rooms m p := regionHere h g m p
  covered := hh
  sworn N m p hi := by rw [hr.1]; exact hM.oath _ _ _ hi
  sends hk hP := Classical.choice (answer_exists h g hM hr hh hk hP)

/-- Connection to the incoming invoices. This qualifies EVEN a previously
constructed survey by numerical hypotheses, not a silent adjustment. -/
structure Covers (s : Survey G) (l : ℕ → ℝ) (γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop where
  book : Free.Catalog s.B.kernel s.X l γ b
  direct i : s.first ≤ i → s.direct i ≤ γ i
  block i : s.first ≤ i → b i ≤ s.floorL i

lemma qualify (hs : Paid I a) (hp : Prepaid s K q e v) {l γ b} (hg : Covers s l γ b) :
    Free.Credit a γ b :=
  Free.credit_from_sheet hs γ b (fun i => hg.direct i) (fun i hi => (hg.block i hi).trans (hp.higher i))

/-- Produce scenes on real paid regions. Quantify over the entire path invoice.
`Prepaid`, `Regime`, etc. here used as previously earned (see end-to-end below). -/
theorem subscribe (h : Paid I a) (hp : Prepaid s K q e v) (g : Regime B e t W) {l γ b}
    (hg : Covers s l γ b) :
    ∃ M H : Horizon a, Craft.Rack a s.X M ∧ Free.Present a M l ∧ Retained H M ∧
      Free.Present a H l ∧ Nonempty (Service a K (B.price t) H) := by
  have hs : a.clock.kernel = s.B.kernel := h.kernel
  obtain ⟨M,hM,h₁⟩ := Free.shelves a s.X l γ b (hs.symm ▸ hg.book) (qualify h hp hg)
  obtain ⟨H,hr,hh⟩ := Deployment.offers h hp M hM
  exact ⟨M,H,hM,h₁,hr,(Free.retained_presents a _ M H h₁ hM hr).1,⟨on_retained h g hM hr hh⟩⟩




end horizons



/-- Full quantifier/order check. K survives ANY further q/e chosen after
getting that price. η(j) from B priced AFTER every Roll, BEFORE generating
any clock/horizon. Take any constant forecasts at F from B. All results on
the same issued calendar. Preserve Ringing, even though our station does not
require some of these stamps. In particular `Billed` Wait is inhabitable
without already having *any* path bounds. Instead of the existential `a`
at the end a user may use `subscribe` with ANY Paid certification above these
quotes/boosts. Genuine FREE_KERNELS beds (`Present`), not general Gaussian
operators pasted in for just positivity. `hG` at numerical scheduling. -/
theorem issue (hG : G.Simple) (s : Survey G) {l γ b} (h : Covers s l γ b) :
    ∃ K : MapPrices, ∀ (q : Quote) (e : ℕ → ℕ → Exchange),
      ∃ f : ℕ → ℕ, ∀ v ≥ f,
        Nonempty (Rolls (s.paper q v)) ∧ Prepaid s K q e v ∧
        ∀ D : Rolls (s.paper q v), ∀ extraW : ℕ → ℕ → ℝ,
          ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
            ∀ (F : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus)
              (extra : ℕ → ℝ), (∀ i,0 < extra i) → ∃ T : Protection D,T.theta ≤ extra ∧
              ∀ V : Delays T, ∀ c d u, ∃ W : Delays T, Boost V W ∧ Loaded B W e F m f ∧
                Extent d c W ∧ Routed e u W ∧ Bumper e W ∧
                Transmitting R W ∧ Testing.Ringing K R.W W ∧
                ∀ r : ℝ, ∃ Y : Bar W, r ≤ Y.value ∧ ∀ J : Wait Y,
                  ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ ∃ a : Levels G, Paid I a ∧
                    ∃ M H : Horizon a, Craft.Rack a s.X M ∧ Free.Present a M l ∧
                      Retained H M ∧ Free.Present a H l ∧ Nonempty (Service a K (B.price F) H) := by
  obtain ⟨K,hK⟩ := funded_from_verified hG s
  refine ⟨K, fun q e => ?_⟩
  obtain ⟨f,hf⟩ := hK q e
  refine ⟨f, fun v hv => ?_⟩
  obtain ⟨hn,hp,ht⟩ := hf v hv
  refine ⟨hn, hp, fun D W₀ => ?_⟩
  obtain ⟨B,R,hR,H⟩ := ht D W₀
  refine ⟨B,R,hR, fun F m f extra he => ?_⟩
  obtain ⟨T,hT,HH⟩ := H F m f extra he
  refine ⟨T,hT, fun V c d u => ?_⟩
  obtain ⟨W,hW,hg,hv,h1,h2,h3,h4,H'⟩ := HH V c d u
  refine ⟨W,hW,hg,hv,h1,h2,h3,h4, fun r => ?_⟩
  obtain ⟨Y,hY,HJ⟩ := H' r
  refine ⟨Y,hY, fun J => ?_⟩
  obtain ⟨I,hI,hb,a,ha⟩ := HJ J
  exact ⟨I,hI,hb,a,ha, subscribe ha hp hg.taxed h⟩

end YM.Progress.StationaryScenes
