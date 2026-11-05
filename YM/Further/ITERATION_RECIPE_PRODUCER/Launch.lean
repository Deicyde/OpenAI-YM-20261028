import YM.Further.ITERATION_RECIPE_PRODUCER.Oven
import YM.Progress.DIRECTED_RECIPE.Deploy

set_option warningAsError false

/-!
# Receipts on the same prepared Directed and its whole-period ancestry
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Lattice Wilson RG RG.Supply RG.Shoot Precision Bid Pressure Exterior Extra.Iteration
open WilsonStartup Next.Scheduling Progress.DirectedRecipe Ovens Ovens.Pipes Input Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {a : Levels G} {M : Horizon a} {s : Survey G} {K : MapPrices} {l : ℕ → ℝ}
    {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Supply.Delays Θ}
    {Y : Bar W} {I : Wait Y} {B : Beam K D} {k : Kin M s.B.chart} {A : ClassicalCosts} {U : Apertures}
    {e : ℕ → ℕ → Exchange} {u : ℕ → ℕ → Postage} (paid : Paid I a) (tax : Regime B e u W) (hm : M.Suffices K)
    (eng : Engine U A B u k) (r : Permissions a)

structure Kick (paid : Paid I a) (tax : Regime B e u W) (hm : M.Suffices K)
    (eng : Engine U A B u k) (r : Permissions a) (N p : ℕ) : Prop where
  menu : Menu k (screen r) N p (pipe a N p) (ink a N p)
  begins : Bid.Oust (alloy k (screen r) paid tax hm eng.worksheet).B N p
  interval : Curve (a.budget N) (serving k N p) (band a N)
  earns β : β∈band a N → let h := serving k N p β; h.beta=β ∧ Lives (alloy k (screen r) paid tax hm eng.worksheet).B.bake N N p h ∧
    (alloy k (screen r) paid tax hm eng.worksheet).B.bake.Starter N p h ∧ PeriodFuture k e u (screen r) N p N h

structure Record (paid : Paid I a) (tax : Regime B e u W) (hm : M.Suffices K)
    (eng : Engine U A B u k) (r : Permissions a) (N m p : ℕ) (t : Trail a p) : Prop where
  starter : (alloy k (screen r) paid tax hm eng.worksheet).B.bake.Starter N p (t N)
  top : t N=serving k N p (t N).beta
  wide : WilsonStartup.Wide (t N)
  through i : m ≤ i → i ≤ N → PeriodFuture k e u (screen r) N p i (t i) ∧
    Packed k e u (screen r) N i p (t i) ∧ HasSlots (t i).p (t i).activities ∧
    Ticket M K U A N i (t i).path ∧
    (∫ U, (t i).eval U ∂prior G _) = partition G (a.S.side N p) (t N).beta
  links i : m ≤ i → i < N → (alloy k (screen r) paid tax hm eng.worksheet).B.Move N i p (t i) (t (i+1)) ∧ (t (i+1)).beta ∈ band a (i+1)

structure Archive (paid : Paid I a) (tax : Regime B e u W) (hm : M.Suffices K)
    (eng : Engine U A B u k) (r : Permissions a) : Prop where
  earns N p : Kick paid tax hm eng r N p
  traces N m p y : (alloy k (screen r) paid tax hm eng.worksheet).B.bake.retain N m p y → m ≤ N ∧ ∃ t, t m=y ∧ Record paid tax hm eng r N m p t
  trial : Invoices k e u (screen r) → ∃ J, (∀ N p, Fired k e u (screen r) N 0 p (J N p)) ∧
    ∃ b : Org.Bolt (alloy k (screen r) paid tax hm eng.worksheet),b.history=seriesOf a J ∧ ∀ C : Family G,C.path=(alloy k (screen r) paid tax hm eng.worksheet).B.bake.make b.history → Spec.Calibrated C

include paid tax hm eng




end YM.Further.IterationRecipe
