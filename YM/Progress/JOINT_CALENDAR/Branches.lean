import YM.Progress.JOINT_CALENDAR.Kinetics

/-!
# Separable higher classical / quantum bills at a priced jump

Use the classical part BEFORE the loop-estimate call. Different preferred
trees or tags for tests in those invoices are fine here; comparison is on the
actual real germs. No exchange of different torus-wide paths or of
independently calibrated families. Exact uniform analytic estimates on the
emitted arrays remain to be proved. Convenience supplier *shape* for
Invoices, not separate existence of either branch. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open Filter Function Lattice RG RG.Supply Wilson Precision Exterior Tree Bid Next.Scheduling
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

def erase (R : PathData G) : PathData G := { R with loop := (silence G).loop }
def addLoop (R V : PathData G) : PathData G := { R with loop := V.loop }

/-- Only the curvature corrections to classical terms (no loop
normalization or support assumptions implicit). -/
structure ClassicalCosts (W : PathData G) (σ C : ℝ) : Prop where
  three : SumBudget (fun i ↦ (W.cubic i).budget σ) C
  four : SumBudget (fun i ↦ (W.quartic i).budget σ) C
  invariant (i : ℕ) : (W.cubic i).Invariant ∧ (W.quartic i).Invariant

structure LoopCosts (W : PathData G) (σ Λ : ℝ) : Prop where
  two : SumBudget (fun i ↦ (W.loop i).budget σ) Λ
  invariant (i : ℕ) : (W.loop i).Invariant
  jets : W.loop_jets

lemma ClassicalCosts.add_loop {W V : PathData G} {σ C Λ : ℝ} (h : ClassicalCosts W σ C) (H : LoopCosts V σ Λ) :
    Charges (addLoop W V) σ C Λ := ⟨H.two,h.three,h.four,fun i => ⟨H.invariant i,h.invariant i⟩,H.jets⟩

lemma ClassicalCosts.erased {W : PathData G} {σ C Λ : ℝ} (h : ClassicalCosts W σ C) (he : 0≤Λ) : Charges (erase W) σ C Λ := by
  have ht := muted (G:=G) zero_le_one he σ
  exact h.add_loop ⟨ht.two,fun i => (ht.invariant i).1,ht.jets⟩

variable {K : MapPrices} {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {V : Delays T} {Y : Bar V} {I : Wait Y} {a : Levels G} {H : Horizon a}
    {O : ChartRatio G} {B : Beam K D} {P : ℕ → ℕ → Postage} {e : ℕ → ℕ → Exchange}

def callFee (q : Quote) (a : Levels G) (m : ℕ) :=
    let b : ℝ := (a.S.block m).val
    classicalFee b (q.classicalCost.classic (a.clock.J (m+1)) (a.clock.J m)) (a.params (m+1)).paths
def loopFee (q : Quote) (a : Levels G) (m : ℕ) :=
    let b : ℝ := (a.S.block m).val
    let r := q.finish.loop (a.clock.J (m+1)) (a.clock.J m)
    r*b^ (4:ℕ)+(r/b^ (2:ℕ))*a.clock.loopCap (m+1)

def MainTest (a : Levels G) (m : ℕ) (R T : PathData G) (ρ : Curves a m) :=
    ∀ n, let S := a.clock.op m n; let p := (a.params (m+1)).clip; let q := (a.params m).clip
      ∃ (U : Forest S.ratio) (t : S.Choices), Higher (fun x => tested U t p R x (ρ n U x)) (fun x => mainTerm q T (represent x))

def MainResult (a : Levels G) (m : ℕ) (R T : PathData G) (ρ : Curves a m) := ∀ n (U : Forest (a.clock.op m n).ratio),
    ClassicalMatch U (a.params (m+1)).clip (a.params m).clip R T (ρ n U)

def LoopTest (a : Levels G) (m : ℕ) (O : ChartRatio G) (P : Postage) (R T : PathData G) (ρ : Curves a m) (α : ℝ) :=
    let p := (a.params (m+1)).clip; let q := (a.params m).clip
    ∀ n, let S := a.clock.op m n; let c := a.S.side m n
      ∃ (U : Forest S.ratio) (k : S.Choices),
        ∀ (i j : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ), (∀ x y, ‖σ x y‖ ≤ 1) → (∀ x y, ‖τ x y‖ ≤ 1) →
          let X := ![wave i σ,wave j τ];
          |iteratedFDeriv ℝ 2 (thermal U k p R (ρ n U) O) 0 X - iteratedFDeriv ℝ 2 (draft α T q) 0 X| ≤
            (Fintype.card (Site c):ℝ)*P.H*a.clock.loopCap (m+1)*Real.exp (-P.rate*c.val)

/-- L for iteration, L₀ auxiliary conditions carried into loop branch (at
fixed zero intermediate loop, with cubic and quartic arrays now determined).
Tests need equality of cubic, quartic before extracting the loop jet. -/
structure MainInvoices {a : Levels G} (H : Horizon a) (B : Beam K D) (L L₀ : Restriction G) : Prop where
  top (N : ℕ) : ∃ W : PathData G,
    let R := scribe (H.H N N) (erase W); let j := a.clock.J N
    L N N R ∧ ClassicalCosts W (q.widths.launch j) (q.classicalCost.beginCost j) ∧
      ∀ n : ℕ, Higher (fun x => mainTerm (a.params N).clip R (represent x))
        (fun x : Dir G (a.S.side N n) => Wilson.energy (represent x))
  jump (N m : ℕ) : m<N → ∀ R : PathData G, OnPage H L N (m+1) R →
    let j := a.clock.J (m+1); let i := a.clock.J m
    ∀ ρ : Curves a m,WarmAt H N m (B.η j) R ρ → ∃ W : PathData G,
      let T := scribe (H.H N m) (erase W)
      L₀ N m T ∧ ClassicalCosts W (q.widths.emits j i) (callFee q a m) ∧ MainTest a m R T ρ

structure LoopInvoices {a : Levels G} (H : Horizon a) (B : Beam K D) (P : ℕ → ℕ → Postage) (O : ChartRatio G) (L L₀ : Restriction G) : Prop where
  wave (N m : ℕ) : m<N → ∀ R T : PathData G, OnPage H L N (m+1) R → OnPage H L₀ N m T →
    let j := a.clock.J (m+1); let i := a.clock.J m; let b := (a.S.block m).val
    T=erase T → ClassicalCosts T (q.widths.emits j i) (callFee q a m) →
    ∀ ρ : Curves a m,WarmAt H N m (B.η j) R ρ → MainResult a m R T ρ → ∃ (α : ℝ) (W : PathData G),
      L N m (addLoop T W) ∧ |α + G.slopeConstant*Real.log b| ≤ q.finish.number j i ∧
        LoopCosts W (q.widths.emits j i) (loopFee q a m) ∧ LoopTest a m O (P j i) R (addLoop T W) ρ α

lemma main_result (ha : Paid I a) (hv : Regime B e P V) (hh : H.Suffices K) (hw : Swears H)
    {N m : ℕ} {R T : PathData G} {L L₀} {ρ} (hm : m<N) (hr : OnPage H L N (m+1) R) (ht : OnPage H L₀ N m T)
    (hc : WarmAt H N m (B.η (a.clock.J (m+1))) R ρ) (hTest : MainTest a m R T ρ) : MainResult a m R T ρ := by
  intro n U k hk t
  obtain ⟨U',t',he⟩ := hTest n
  have hs := Deployment.step_larger ha hv m n
  have hq := B.custody (a.clock.J (m+1))
  obtain ⟨g,h,h',hg⟩ := hc n U
  obtain ⟨g',H',-,_⟩ := hc n U'
  have hy := trial_agrees hs hr.2.2 s.B.chartRatio h H' hq g g' t t'
  obtain ⟨-,hp⟩ := Work.F03.answer G _ _ _ hs U (H.H N (m+1)) _ _ _ _ _ _ _ (hh.all N (m+1) hm _) hr.2.2
    hr.linked (hw N (m+1) _ hm) (Work.F02.answer _ _ _ _ _ _ hr.2.2)
  have hj := tested_second _ h hp _ hg (hh.all N m hm.le _) ht.2.2 ht.linked (hw N m _ hm.le) t
  by_cases hl : k≤2
  · exact hj k hl
  exact ⟨(hj 0 (by omega)).1,(hj 0 (by omega)).2.1, (hy.1 k).trans (he k (by omega) hk)⟩

lemma supply_erased (ha : Paid I a) (hp : Designing K q) (g : Prepaid s K q e v) (hv : Regime B e P V)
    (hh : H.Suffices K) {N m} (hm : m<N) {W : PathData G}
    (hc : ClassicalCosts W (q.widths.emits (a.clock.J (m+1)) (a.clock.J m)) (callFee q a m)) :
    FitsAt a m (scribe (H.H N m) (erase W)) := by
  let T := scribe (H.H N m) (erase W)
  let j := a.clock.J (m+1); let i := a.clock.J m
  have hq := Deployment.adj a m
  have ht := (a.params (m+1)).paths_pos
  have hw := q.classicalCost.pos_ij j i
  have hFee : q.classicalCost.classic j i ≤ callFee q a m := by
    unfold callFee classicalFee
    apply le_mul_of_one_le_right (by linarith)
    rw [add_assoc,add_assoc]; exact le_add_of_nonneg_right (by positivity)
  have hΛ : 0 ≤ loopFee q a m := by
    have hp := q.finish.loop_pos j i
    change 0 ≤ q.finish.loop j i*(_ : ℝ)^ (4:ℕ)+(q.finish.loop j i/_)*(a.clock.loopCap _)
    unfold Calendar.loopCap Calendar.monitor; positivity
  exact Deployment.nextPath ha g hv m T (charged _ _ (q.widths.rate j i) (hh.rows N m hm.le) (hp.emits _ _ hq).1
    (hp.emits _ _ hq).2 (hh.all N m hm.le 1) ((hp.classic _ _ hq).trans hFee) (hc.erased hΛ))

/-- Combine branch invoices without any pre-assumption that one usable tree
exists for BOTH, or changing the rows after they matched on Main.
Current results only support this implication, NOT discharging these input
ports or finding their costs in usable scheduling order. -/
theorem Invoices.split (ha : Paid I a) (g : Prepaid s K q e v) (hp : Designing K q) (hv : Regime B e P V)
    (hh : H.Suffices K) (hw : Swears H) {L L₀ : Restriction G} (h1 : MainInvoices H B L L₀) (h2 : LoopInvoices H B P O L L₀) :
    Invoices H B P O L := by
  constructor
  · intro N; obtain ⟨W,hL,hc,hj⟩ := h1.top N
    exact ⟨erase W,hL,hc.erased le_rfl,fun _ => rfl,hj⟩
  intro N m hm R hr j i b ρ hρ
  obtain ⟨W,hX,Hq,hF⟩ := h1.jump N m hm R hr ρ hρ
  let T := scribe (H.H N m) (erase W)
  have hT : OnPage H L₀ N m T := ⟨rfl,hX,supply_erased ha hp g hv hh hm Hq⟩
  have he := main_result ha hv hh hw hm hr hT hρ hF
  have hc : ClassicalCosts T (q.widths.emits j i) (callFee q a m) := ⟨Hq.three,Hq.four,Hq.invariant⟩
  obtain ⟨α,A,hL,hα,hA,hG⟩ := h2.wave N m hm R T hr hT rfl hc ρ hρ he
  refine ⟨α,addLoop W A,hL,hα,Hq.add_loop hA,fun n => ?_⟩
  obtain ⟨U,k,hU⟩ := hG n
  exact ⟨U,k,fun x _ hx => (he n U x hx k).2.2,hU⟩
end YM.Progress.Joint
