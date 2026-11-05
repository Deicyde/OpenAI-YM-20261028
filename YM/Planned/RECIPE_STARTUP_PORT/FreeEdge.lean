import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Metric
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue

set_option warningAsError false

/-!
# Optional stronger purchase: an actual free Rack itinerary ALSO for the

localized top, with a separate (boundary!) rate at N. No paying a spin width
on the first step, preserve Bleeps etc in a genuine Rack from which final
repaired H is Bid.Retained, using one price pin.

Instead prove the full analogue using top inverse
modifier l=0 (original Reach positivity needed at block OUT, so don't
change l there; `buys` works *for all incoming m≥0*, with constants
possibly m-dependent – take two possibilities before any L). Even on
plateaus i=N is still THE cutoff and i<N still uses the l bought for its
smoothing. New uniform purchases here only pre-L; no call on nonlinear
solvability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Port.Edge
open Function Filter RG RG.Supply Lattice Laurent Bloch Metric Exterior Craft Bid Precision Next Next.Free WilsonStartup
open scoped Matrix.Norms.Frobenius

/-- This really is `Defined 0` (equality even on the Laurent kernels, not
just at the side the step happened to sample). Use Free's bank injectivity
on summable kernels. -/
theorem express (k : ℝ) (hk : 0<k) (j : ℕ) (hj : 4≤j) (p : Clip) : Defined k 0 (Train.top j) (Design.bed p) := by
  let v := Train.top j
  let w : Unit → Train j := fun _ => v
  obtain ⟨h,H⟩ := heart_true k hk hj v
  have ht : Whole (Design.spike 1) := ⟨1,1,zero_lt_one,Design.spike_strip _ _ _ (by simp)⟩
  have h1 := (heart_heats k hk hj w).1.stock.whole ()
  have h2 := (heart_heats k hk hj w).2.stock.whole ()
  change Whole (pink k v) at h1
  change Whole (blue k v) at h2
  have e1 : Design.spike 1 = pink k v := by
    apply bank_injective ht.safe h1.safe (fun n => Whole.eq_on ht h1 ?_ n)
    intro q hq
    rw [Design.spike_read,show (pink k v).read q=_ from h.echo q hq,
      top_metric k hk j (base_subset_realCube zone_pos hq) |>.2]
    simp
  have e2 : Design.spike 1 = blue k v := by
    apply bank_injective ht.safe h2.safe (fun n => Whole.eq_on ht h2 ?_ n)
    intro q hq
    rw [Design.spike_read,show (blue k v).read q=_ from H.echo q hq,
      top_metric k hk j (base_subset_realCube zone_pos hq) |>.1]
    simp
  have e3 : Design.spike 1 = Free.pledge k 0 v := by
    rw [e2]; funext i l x
    unfold Free.pledge Free.plusRows Work.F08.minusRows Work.F08.scaleRows
    simp
  have hM : Whole (Free.amend k 0 v) := (insurance k 0 hk le_rfl hj w).1.stock.whole ()
  have e4 : Design.spike 1 = Free.amend k 0 v := by
    apply bank_injective ht.safe hM.safe
    intro n
    have h := ((heated (pledge_warm k 0 hk le_rfl hj w)).2 ()).2 n
    change ((Free.amend k 0 v).acts n)*((Free.pledge k 0 v).acts n)=1 at h
    rw [← e3, Design.spike_acts,one_smul,Matrix.mul_one] at h
    rw [Design.spike_acts,one_smul,h]
  exact ⟨e1,e2,e4,e3⟩

/-- Extra pre-L ask. Still finite per pair. -/
structure Second (k : KernelChoices) (X : MapPrices) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop extends Catalog k X l γ b where
  price_cap j : X.η j ≤ 1
  space j : 1 ≤ X.Ω j
  small j : γ j ≤ 1
  zeroH j i : Mag j i → HopQuote k j i 0 (l i) (X.α j) (X.η j) (X.Ω j) (b j)



section horizons
variable {G : Gauge} {X K : MapPrices} {l γ : ℕ → ℝ} {b : ℕ → ℕ}

/-- `l` at non-boundary (even if same smoothing as the cutoff); zero at
boundary. Still cumulative Train through actual depths and includes T/A0
of the linear roll, as well as Bleeps and positivity of the substrate via
Rack. -/
def boundaryPresent (a : Levels G) (M : Horizon a) (l : ℕ → ℝ) :=
    (∀ N m,m ≤ N → Defined a.clock.kernel.penalty (if m=N then 0 else l (a.clock.J m)) (Free.location a N m) (M.H N m)) ∧
    (∀ N m,m < N → (M.towers N m).A0=((Free.destination a N m).duo a.clock.kernel.penalty).A0 ∧
      (M.towers N m).T=((Free.destination a N m).duo a.clock.kernel.penalty).T)

/-- Build both *actual* Racks on same levels, exact shared kernels/arrays
thru all further steps. Top altered everywhere for second option incl
N=0. -/
structure Pair (a : Levels G) (X : MapPrices) (M Z : Horizon a) (l : ℕ → ℝ) : Prop where
  rack : Rack a X M
  present : Present a M l
  edge : Rack a X Z
  location : boundaryPresent a Z l
  peak N : Z.H N N = Design.bed (a.params N).clip
  rest N m : m≠N → Z.H N m=M.H N m
  towers : Z.towers=M.towers


end horizons
end YM.Planned.Port.Edge
