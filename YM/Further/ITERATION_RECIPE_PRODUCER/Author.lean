import YM.Further.ITERATION_RECIPE_PRODUCER.Entrance
import YM.Further.ITERATION_RECIPE_PRODUCER.Joint
import YM.Further.ITERATION_RECIPE_PRODUCER.Motion
import YM.Further.ITERATION_RECIPE_PRODUCER.Paper

set_option warningAsError false

/-!
# Conditional source consumer on the SAME unmarked history and books

E ordered finite sources. Need Invoices for that trajectory & further the
local source estimate here on its actual representation (AT origin), beyond
Heating. Predicates see the readdressed/widened reps after recipe startup,
NOT a `Start.layout` equality. C readout calibration, placements etc use the
output history; need still prove simultaneous transfer estimates & translated
comparisons on it. No Maker is unconditional. `Release.press` doesn't
produce a signed push identity for arbitrary offsets nor `Metered` or
field-selection claims from these single/mixed initialization receipts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories WilsonStartup
open Bid Precision Next.Scheduling RG.Supply RG.Shoot Progress.Joint Extra.Iteration
open Progress.DirectedRecipe Input Org Mixture Pressure
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y} {Z : Org.Alloy (s.metals q K v) D}
    (b : Bolt Z) (ref : ℕ → ℕ) (c : ℕ → ℝ)

def chronicle := Z.B.bake.make b.history

def Volume (T : ∀ d N p, TransferData (s.B.frames.level d) (chronicle b) N p) : Family G :=
    Family.mk (chronicle b) s.B.hol s.B.frames s.B.entry ref T

def Blocks := ∀ d N p m, ref d ≤ m → m<N → ∃ T, AtomStep (s.B.entry d) (chronicle b) N p m s.B.hol T
    (c ((chronicle b).levels.clock.J (m+1))) (Doors.rate ((chronicle b).S.block m))

def Angeled (C : Family G) := ∀ d N p m i, C.ref d ≤ m → ∀ hm : m ≤ i, ∀ hN : i ≤ N, ∀ (k s : ℝ),
    1 ≤ k → Mix.ticket C k N p m i (hm.trans hN) → ∀ v : C.label d, ‖v‖ ≤ s → Terminal C m N p (hm.trans hN) v (tide C s d N)

structure Release (b : Bolt Z) (ref : ℕ → ℕ) (c : ℕ → ℝ) : Prop where
  marks d N p : ref d ≤ N → ∀ o : Site ((chronicle b).S.side N p), Mark.Prepared (chronicle b) (s.B.entry d) s.B.hol N p o
  covers N p : let H := chronicle b; WilsonStartup.Wide (H.rep N p N) ∧
    (H.rep N p N).activities.KBound (Start.expand (H.levels.budget N)) (1/2)
  contrary N m p : m ≤ N → ¬ Nonempty (Shelf ((chronicle b).rep N p m).activities)
  press : Blocks b ref c → ∃ T, let C := Volume b ref T
                           Scored (chronicle b) s.B q.finish.W ref T ∧ Spec.Calibrated C ∧ Angeled C

lemma calibrated (T) : Spec.Calibrated (Volume b ref T) :=
  ⟨_,_,_,_,_,_,_,_,_,Z.B,b.history,b.sticks,rfl,b.moves⟩

variable {l : ℕ → ℝ} {a : Levels G} {M : Horizon a} {e : ℕ → ℕ → Exchange}
    {u : ℕ → ℕ → Postage} {B : Beam K D} {R : Radios K D} {paid : Paid I a} {tax : Regime B e u W} {A : ClassicalCosts} {U : Apertures}
    {H : QuantumCosts} {V : Rebuild.Census} {F : Rebuild.Fuel D} {rate : ℕ → ℝ} {t : ℕ → ℕ}
    (m : Mission B R paid tax l U A H V F rate t) (g : Prepaid s K q e v) (hm : M.Suffices K)
    {k : Kin M s.B.chart} (hk : Engine U A B u k) (r : Permissions a)
include m hm hk g
local notation "book✶" => alloy k (screen r) paid tax hm hk.worksheet

theorem author (hC : Cash s q v c) (hc : ∀ i,1 ≤ c i) : ∃ ref : ℕ → ℕ, (∀ d m, ref d ≤ m ↔ Admits s.requests (a.clock.J m) d) ∧
    ∀ b : Bolt book✶, Release b ref c := by
  obtain ⟨ref,hr,h⟩ := m.anchors
  obtain ⟨hb,ha⟩ := g.cash D a paid.stage paid.lengths
  refine ⟨ref,hr,fun b => ?_⟩
  let H := chronicle b
  have he N m p (hm : m ≤ N) : PeriodFuture k e u (screen r) N p m (H.rep N p m) := ((b.sticks N p).prices m (Nat.zero_le _) hm).1.loads
  have hv N p : WilsonStartup.Wide (H.rep N p N) ∧ (H.rep N p N).activities.KBound (Start.expand (a.budget N)) (1/2) :=
    annual (he N N p le_rfl) (m.top N) (m.extras N)
  have hj d N (hd : ref d ≤ N) : d ≤ a.clock.J N := (Nat.le_add_right ..).trans (((hr d N).1 hd).1)
  have ht d N p (hd : ref d ≤ N) := Mark.issue H (s.B.entry d) N p (s.B.sound _) (m.entry N d (hj d N hd)) (b.choice.represents _ _ _ le_rfl) (hv N p).1
  refine ⟨ht,hv,fun N m p hm hh => impossible (he N m p hm).pockets.2.2.2.2 hh,fun hA => ?_⟩
  obtain ⟨T,hT⟩ := IterationRecipe.score b.choice ha hb (fun d N p hd => ht d N p hd 0) (h H rfl) fun d N p m he hm =>
    have hL := hC.buys (H:=H) hc paid ((hj d m he).trans (a.fits.mono (Nat.le_succ m)))
    let ⟨v,hu⟩ := hA d N p m he hm; ⟨_,_,_,hL,hu⟩
  refine ⟨T,hT,calibrated b ref T,fun d N p m' i h' hm hN k' s h0 he v hv' => ?_⟩
  exact inherits_mix (C:=Volume b ref T) hT.issued v s hv' h0 h' hm hN he (hv N p).1 (hv N p).2
    (m.entry N d (hj d N (h'.trans (hm.trans hN)))) (m.extras N) hT.reads

omit hm hk in
/-- Arrival of the estimates at a funded Mission from `marked_reserve`
CASE of the launch theorem. Conditional in **local** unmasked & actual
nonlinear supplies; choose one Bake for all downstream obligations.
`Release.press` on the same books. User restrictions on followers and starts
optional (need `Policy` too, and always use `screen`). As `Prepaid` & `Cash`
at this position, no further Bar selection needed here. No unconditional
continuation of even the unmarked recipe.
-/
theorem publishing (hC : Cash s q v c) (hc : ∀ i,1 ≤ c i) : ∃ M : Horizon a, ∃ hM : Panel K s.X l M,
    Heating M K U A H (B.price u) s.B.chart → ∃ k : Kin M s.B.chart, ∃ hk : Engine U A B u k,
      ∀ r : Permissions a, Policy r → let Z := alloy k (screen r) paid tax hM.covers hk.worksheet
        Archive paid tax hM.covers hk r ∧ ∃ ref : ℕ → ℕ,(∀ d n, ref d ≤ n ↔ Admits s.requests (a.clock.J n) d) ∧
          (∀ b : Bolt Z, Release b ref c) ∧ (Invoices k e u (screen r) → Nonempty (Bolt Z)) := by
  obtain ⟨M,hM,-,he⟩ := m.machines
  refine ⟨M,hM,fun hH => ?_⟩
  obtain ⟨k,hk,hs⟩ := he hH
  refine ⟨k,hk,fun r hr => ?_⟩
  obtain ⟨ref,h₁,h⟩ := author c m g hM.covers hk r hC hc
  refine ⟨hs r hr,ref,h₁,h,fun hh => ?_⟩
  obtain ⟨J,hJ,b,-⟩ := ((hs r hr).trial hh)
  exact ⟨b⟩
end YM.Further.IterationRecipe
