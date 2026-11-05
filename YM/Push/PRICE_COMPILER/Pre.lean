import YM.Push.PRICE_COMPILER.Authors
import YM.Push.PRICE_COMPILER.Pin
import YM.Push.PRICE_COMPILER.Pressure
import YM.Push.PRICE_COMPILER.Rates




/-!
# Part of RRequirements: pre-L

Scopes: Use this, for example, with `κ`, author data and `orders` known
(E initial data; allocate all used power demands), and ur clip & `flat`
quotes from linear work. `preMap` pricing the repair can already be called,
BEFORE choosing the `opening`. From the opening quotes commit actual active
widths, then get `Amounts` quotes, evaluate `Amounts.active` for the
actual caps. Then one can get `LoopPrices` quotes. Relaxation can now
be as large as necessary. Budget further cone, stencil, columns and
projection asks known on these data. Stage thus fixed. THEN price the lengths.

The `Before` fields record *numbers* under these scopes; do NOT produce
or assume the proof that all quotes apply, certainly don't assert they are
the only requirements on a schedule. `floorL` can be raised to anticipate
additional costs quoted lawfully. All numbers may be given as functions
of previous tables; we use classical choice of tables, not an algorithm
obeying a computational locality condition. Crucially, per-index
inequalities here require just finite lower/upper bounds and work before
instantiating even one length (including *earlier or later* L); no bounding
an infinite collection of w or post-L path costs by one pre number.

For instance, don't read this as permission to choose `p.profile` from
a report on the actual fields/cutoff after the continuation. The quotes
and any extra required floor are needed HERE. Our work proves sufficiency
for the indicated price conditions. E.g., the raw kernel had BETTER
have suitable pre-L estimates; if the attainable width depends on
unbounded L and destroys prechoice, a producer will be unable to provide
these inputs later. See also obstruction results in this project.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- All numerical PRE-L inputs to our cut. -/
structure Before where
  κ : ℝ
  κpos : 0 < κ
  first : ℕ
  start : 4 ≤ first
  orders : OrderPlan
  clip : ℕ → Clip
  flat : FlatBill
  opening : Openings
  amount : Amounts
  slopePrices : LoopPrices
  reserve : HaloBill
  relaxation : ℕ → ℝ -- additional minimum on R0 in clip
  lead : ℕ → ℝ -- extra Worth asks
  columns : ℕ → ℝ -- extra columns (can depend on the ACTUAL Worth that will be used)

namespace Before
variable (P : Before) (G : Gauge)

def kernelChoice := Next.Foundations.kernel G P.κ P.κpos
/-- Ex ante with JUST those projections needed, to allow subsequent asks from it. -/
def frozen : MapPrices := preMap (P.kernelChoice G) P.clip P.flat G

def principal : Bid.Worth := worth G P.orders P.lead

def profile (i : ℕ) : Stage where
  clip := P.opening.newClip P.clip P.relaxation i
  order := P.orders.k i
  power := P.orders.P i
  supportExponent := P.orders.A i
  width := P.opening.active i
  paths := P.amount.active i
  drift := P.slopePrices.drift i
  columns := columnFee (P.principal G) P.orders P.columns i
  order_ge := P.orders.kbase i
  power_ge := P.orders.Pbase i
  price_pos := P.orders.Apos i
  width_pos := P.opening.active_pos i
  paths_pos := P.amount.active_pos i
  slow_selector := (P.opening.relax_ge ..).2.2
  columns_ge := le_trans ((P.principal G).prices i)
    (worth_le_room _ ((columnFee_requirements _ _ _).2.2.1 i))
  drift_ge := (payHi_pos ..).le

/-- Used before choosing actual L. -/
def sheet (f : ℕ → ℕ) : Sheet G :=
  ⟨P.kernelChoice G, fun _ => Next.Foundations.branches .., P.profile G, P.first,P.start,
    P.orders.kmono,P.orders.Pmono,P.orders.Amono,f⟩



lemma active_plan : Monotone (fun i => (P.profile G i).paths) ∧
    Antitone (fun i => (P.profile G i).width) ∧
    Monotone (fun i => (P.profile G i).clip.relaxation) ∧
    Monotone (fun i => (P.profile G i).columns) ∧
    Monotone (fun i => (P.profile G i).drift) ∧
    KernelMonotone (P.frozen G) :=
  ⟨P.amount.active_mono,P.opening.active_anti,payHi_mono _,(columnFee_requirements ..).1,
    payHi_mono _,(preMap_props ..).2.1⟩

lemma room_cols (i : ℕ) : 64*((P.principal G).K (i+1))^(2:ℕ) ≤ (P.profile G i).columns :=
  (columnFee_requirements ..).2.2.1 i
lemma fact_cols (i : ℕ) : (Nat.factorial (P.profile G i).order:ℝ) ≤ (P.profile G i).columns :=
  (columnFee_requirements ..).2.2.2 i

lemma author_cols (i : ℕ) : authorFee G P.orders i ≤ (P.principal G).K i := worth_pays _ i

def Edge (j i L : ℕ) := EdgeGate P.orders.A P.opening P.amount P.slopePrices P.reserve j i L

/-- Price schedule can buy these properties still pre-L. They can be used
wherever overridden floor ≥ quoted floor. -/
structure Funded (P : Before) (G : Gauge) (floor : ℕ → ℕ) : Prop where
  bank (D : Rolls (P.sheet G floor)) (a : Levels G) : a.clock.factor = D.L → a.clock.stage=P.profile G →
    Bid.Bank (P.principal G) a ∧ Bid.roomCost a (P.principal G)
  edges (j : ℕ) (L : Side) : floor j ≤ L.val → ∀ i, StepStages j i → P.Edge j i L.val ∧
    PressureGate (P.sheet G floor) (P.frozen G) j i L

/-- Main pre-L compiler. Respects arbitrary extra demands already in the
`Before` tables and additional requested length floors `fees`. -/
theorem enoughFloors (fees : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, Monotone f ∧ fees ≤ f ∧ ∀ g : ℕ → ℕ, f ≤ g → Funded P G g := by
  obtain ⟨k,hk,h₁,hprices⟩ := pressureFloors (P.sheet G fees) (P.frozen G)
  obtain ⟨v,hv⟩ := Bid.buffer (P.principal G) (P.sheet G fees) (P.room_cols G)
  obtain ⟨f,hf,h₂,hF⟩ := edgeFloors P.orders.A P.orders.Apos P.opening P.amount P.slopePrices P.reserve
    (fun i => max (k i) (v i))
  have hb (i) : k i ≤ f i ∧ v i ≤ f i := max_le_iff.mp (h₂ i)
  refine ⟨f,hf,fun i => (h₁ i).trans (hb i).1, fun g hG => ⟨?_,?_⟩⟩
  · exact hv g fun i => (hb i).2.trans (hG i)
  intro j L hl i he
  have hx := (hG j).trans hl
  exact ⟨hF j L.val hx i he,hprices j L ((hb j).1.trans hx) i he⟩

section
variable {P G} {f : ℕ → ℕ} (hf : Funded P G f) {a : Levels G}
    {D : Rolls (P.sheet G f)} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
include hf

lemma Funded.qualify (D : Rolls (P.sheet G f)) {j i : ℕ} (h : StepStages j i) :
    P.Edge j i (D.L j).val ∧ PressureGate (P.sheet G f) (P.frozen G) j i (D.L j) :=
  hf.edges j (D.L j) (D.large j).need i h

lemma Funded.at_edge (ha : Paid I a) (m : ℕ) :
    P.Edge (a.clock.J (m+1)) (a.clock.J m) (a.S.block m).val := by
  rw [block_eq ha]; exact (hf.qualify D (step_paid a m)).1


end
end Before
end YM.Push.PriceCompiler
