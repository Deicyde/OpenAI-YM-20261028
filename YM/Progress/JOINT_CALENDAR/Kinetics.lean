import YM.Progress.JOINT_CALENDAR.Germs
import YM.Progress.JOINT_CALENDAR.Rows

/-!
# Deploying the scheduling receipts before the nonlinear RLoops calculations

On ONE actual jointly priced horizon.

Induction
usable with finitely priced width-compatible estimates on the higher pieces
.

These pieces are not consequences of the RG
work packages currently imported.

We do not certify feasibility of finding
all these estimates together at the quantifier positions of `joint_budget`.

All lower jets, root rows and analytic/rate handoffs discharged here; avoid
assuming `Directed`, a rollout of a `Planned` family etc at this point.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open Filter Function Lattice RG RG.Supply Wilson Precision Exterior Tree Bid Next.Scheduling
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev Curves (a : Levels G) (m : ℕ) := ∀ n : ℕ, (U : Forest (a.clock.op m n).ratio) →
    (Dir G (a.S.side m n) → AxisChart G U)

def WarmAt {a : Levels G} (H : Horizon a) (N m : ℕ) (η : ℝ) (R : PathData G) (ρ : Curves a m) :=
    let p := (a.params (m+1)).clip
    ∀ (n : ℕ) (U : Forest (a.clock.op m n).ratio), PriceGap U p R η ∧ Critical U p R (ρ n U) ∧
      Guessed U (Bloch.installed (a.clock.op m n).ratio (H.towers N m).A0) (ρ n U) ∧ HeatG U p R (ρ n U) (H.H N m)

def Higher {n : Side} (F F' : Dir G n → ℝ) := ∀ t : ℕ,3≤t → t≤4 → iteratedFDeriv ℝ t F 0=iteratedFDeriv ℝ t F' 0

/-- Single period invoice at possibly one usable tree/tag. All quantitative
bounds still true finite-volume comparisons, with COMMON infinite kernels
and correction arrays. No equal-direction/strictly off-harmonic premise. -/
def Differences (a : Levels G) (m n : ℕ) (O : ChartRatio G) (P : Postage) (R T : PathData G) (ρ : Curves a m) (α : ℝ) :=
    let S := a.clock.op m n; let p := (a.params (m+1)).clip; let q := (a.params m).clip; let c := a.S.side m n
    ∃ (U : Forest S.ratio) (k : S.Choices), Higher (fun x => tested U k p R x (ρ n U x)) (fun x => mainTerm q T (represent x)) ∧
      ∀ (i j : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ), (∀ x y, ‖σ x y‖ ≤ 1) → (∀ x y, ‖τ x y‖ ≤ 1) →
        let X := ![wave i σ,wave j τ];
        |iteratedFDeriv ℝ 2 (thermal U k p R (ρ n U) O) 0 X - iteratedFDeriv ℝ 2 (draft α T q) 0 X| ≤
          (Fintype.card (Site c):ℝ)*P.H*a.clock.loopCap (m+1)*Real.exp (-P.rate*c.val)

abbrev Restriction (G : Gauge) := ℕ → ℕ → PathData G → Prop

def FitsAt (a : Levels G) (m : ℕ) (R : PathData G) :=
    let p := a.params m; R.Bounds p.clip p.width p.paths (a.clock.loopCap m)

def OnPage {a : Levels G} (H : Horizon a) (L : Restriction G) (N m : ℕ) (R : PathData G) :=
    R = scribe (H.H N m) R ∧ L N m R ∧ FitsAt a m R

variable {K : MapPrices} {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {V : Delays T} {Y : Bar V} {I : Wait Y} {a : Levels G} {H : Horizon a}
    {L : Restriction G} {O : ChartRatio G} {B : Beam K D} {P : ℕ → ℕ → Postage} {e : ℕ → ℕ → Exchange}

/-- NOT proved. At top and at the **single-step** scale respectively, before
composing into sequences. Eta taken at exact pre-all-histories post-L Beam.
No need for `Built` to realize arbitrary Width/E choices *from* these clauses,
or for caller to anticipate heights using post-volume constants. But needs
actual corrections at the scheduled prices: common α and cover arrays across
periods, witness restrictions retained, expandable at `emits` widths incl
when j repeats, etc. `W` output has an UNUSED row field (overwritten).
Startup invoice independent of step solutions. -/
structure Invoices {a : Levels G} (H : Horizon a) (B : Beam K D) (P : ℕ → ℕ → Postage)
    (O : ChartRatio G) (L : Restriction G) : Prop where
  top (N : ℕ) : ∃ W : PathData G,
    let R := scribe (H.H N N) W; let j := a.clock.J N
    L N N R ∧ Charges W (q.widths.launch j) (q.classicalCost.beginCost j) 0 ∧ (∀ b,(W.loop b).coeff=0) ∧
      ∀ n : ℕ, Higher (fun x => mainTerm (a.params N).clip R (represent x))
        (fun x : Dir G (a.S.side N n) => Wilson.energy (represent x))
  descend (N m : ℕ) : m<N → ∀ R : PathData G, OnPage H L N (m+1) R →
    let j := a.clock.J (m+1); let i := a.clock.J m; let b := (a.S.block m).val
    ∀ ρ : Curves a m,WarmAt H N m ((B.price P).η j) R ρ → ∃ (α : ℝ) (W : PathData G),
      L N m (scribe (H.H N m) W) ∧ |α + G.slopeConstant*Real.log b| ≤ q.finish.number j i ∧
      Charges W (q.widths.emits j i) (classicalFee b (q.classicalCost.classic j i) (a.params (m+1)).paths)
        (q.finish.loop j i*(b:ℝ)^ (4:ℕ)+(q.finish.loop j i/(b:ℝ)^ (2:ℕ))*a.clock.loopCap (m+1)) ∧
      ∀ n : ℕ,Differences a m n O (P j i) R (scribe (H.H N m) W) ρ α

-- Pieces of Kin.Planned in a convenient sequence form.
def AtPeak (a : Levels G) (N : ℕ) (R : PathData G) := (∀ b,(R.loop b).coeff=0) ∧ ∀ (n i : ℕ), i ≤ 4 →
    SameJet i (fun x => mainTerm (a.params N).clip R (represent (x:Dir G (a.S.side N n)))) (fun x => Wilson.energy (represent x))

structure Jump {a : Levels G} (H : Horizon a) {p' : Sheet G} {D' : Rolls p'} (Q : PostCost D') (O : ChartRatio G)
    (N m : ℕ) (R T : PathData G) (α : ℝ) (ρ : Curves a m) : Prop where
  hot : WarmAt H N m (Q.η (a.clock.J (m+1))) R ρ
  kinetic : |α + G.slopeConstant*Real.log (a.S.block m).val| + 1 ≤ (a.params (m+1)).drift
  laws (n : ℕ) : let j := a.clock.J (m+1); let p := (a.params (m+1)).clip; let q := (a.params m).clip
    ∀ U : Forest (a.clock.op m n).ratio, ClassicalMatch U p q R T (ρ n U) ∧
      FiniteBound U R T p q α O (ρ n U) (Q.Γ j) (Q.c j) (a.clock.loopCap (m+1))

lemma OnPage.linked {N m} {R : PathData G} (h : OnPage H L N m R) : Attached (H.H N m) R :=
    h.1.symm ▸ scribe_attached (H.H N m) R

abbrev Swears {a : Levels G} (H : Horizon a) := ∀ N m n,m≤N → Sworn (H.H N m) n G

variable (ha : Paid I a) (g : Prepaid s K q e v) (hp : Designing K q) (hv : Regime B e P V) (hh : H.Suffices K)
    (hw : Swears H) (hO : LocalRatio O) (hi : Invoices H B P O L)
include ha hp hh hw hi

lemma earn_top (N : ℕ) : ∃ R,OnPage H L N N R ∧ AtPeak a N R := by
  let j := a.clock.J N
  obtain ⟨W,hL,hc,hZ,hb⟩ := hi.top N
  let R := scribe (H.H N N) W
  have hA : FitsAt a N R := Deployment.topPath ha N R (charged _ _ (q.widths.top_rate j)
    (hh.rows N N le_rfl) (hp.launch j).1 (hp.launch j).2 (hh.all N N le_rfl 1) (hp.beginCost j) hc)
  refine ⟨R, ⟨rfl,hL,hA⟩,hZ,fun n i hi' => ?_⟩
  have he := top_second (H.H N N) R (hh.all N N le_rfl (a.S.side N n)) (hh.top N _) hA (hw _ _ _ le_rfl) (scribe_attached ..)
  by_cases h : i≤2
  · exact he i h
  obtain ⟨h1,h2,-⟩ := he 0 (by omega)
  exact ⟨h1,h2,hb n i (by omega) hi'⟩

include hv
omit hi hp in
lemma earn_station {N m : ℕ} (hm : m<N) {R : PathData G} (h : OnPage H L N (m+1) R) :
    ∃ ρ : Curves a m, WarmAt H N m ((B.price P).η (a.clock.J (m+1))) R ρ := by
  have he := fun n => Deployment.scene ha hv m n N hm H hh R h.2.2 h.linked (hw _ _ _ hm)
  choose r hr using fun n U => (he n U).2
  exact ⟨r, fun n U => ⟨(he n U).1,hr n U⟩⟩

include g hO
omit hi hp g in
lemma earn_period {N m : ℕ} (hm : m<N) (n : ℕ) {R T' : PathData G} {α : ℝ} {ρ : Curves a m}
    (hR : OnPage H L N (m+1) R) (hT : OnPage H L N m T') (hc : WarmAt H N m ((B.price P).η (a.clock.J (m+1))) R ρ)
    (hd : Differences a m n O (P (a.clock.J (m+1)) (a.clock.J m)) R T' ρ α) :
    let S := a.clock.op m n; let j := a.clock.J (m+1); let p := (a.params (m+1)).clip; let q := (a.params m).clip
    ∀ U : Forest S.ratio, ClassicalMatch U p q R T' (ρ n U) ∧
      FiniteBound U R T' p q α O (ρ n U) ((B.price P).Γ j) ((B.price P).c j) (a.clock.loopCap (m+1)) := by
  intro S j p q' U
  obtain ⟨U₀,t,hj,hF⟩ := hd
  obtain ⟨h1,h2,h3,h4⟩ := hc n U
  obtain ⟨h1',h2',h3',h4'⟩ := hc n U₀
  have hQ := (B.price P).price j
  have hl := Deployment.step_larger ha hv m n
  have he := fun i : S.Choices => trial_agrees hl hR.2.2 hO h2 h2' hQ h1 h1' i t
  obtain ⟨-,hU⟩ := Work.F03.answer G _ _ S hl U (H.H N (m+1)) p R _ _ _ _ _ (hh.all N (m+1) hm _)
    hR.2.2 hR.linked (hw N (m+1) _ hm) (Work.F02.answer _ _ _ _ _ _ hR.2.2)
  have hM := tested_second (H.H N (m+1)) h2 hU (H.H N m) h4 (hh.all N m hm.le _)
    hT.2.2 hT.linked (hw N m _ hm.le)
  constructor
  · intro k hk u
    by_cases h : k≤2
    · exact hM u k h
    obtain ⟨ha,hb,-⟩ := hM u 0 (by omega)
    exact ⟨ha,hb, ((he u).1 k).trans (hj k (by omega) hk)⟩
  refine ⟨Work.F05.hessian_pos hQ h1 h2, fun u => thermal_born u hR.2.2 h2 hQ h1 hO, draft_born hT.2.2 α, fun u i k σ τ hσ hτ => ?_⟩
  intro W
  rw [(he u).2]
  apply (hF i k σ τ hσ hτ).trans
  obtain ⟨hΓ,hr,-⟩ := B.leg P (Deployment.adj a m)
  have hx := (B.price P).pos j
  have hg : 0≤ a.clock.loopCap (m+1) := by unfold Calendar.loopCap Calendar.monitor; positivity
  gcongr

lemma earn_jump {N m : ℕ} (hm : m<N) {R : PathData G} (hR : OnPage H L N (m+1) R) :
    ∃ (Q : PathData G) (α : ℝ) (ρ : Curves a m), OnPage H L N m Q ∧ Jump H (B.price P) O N m R Q α ρ := by
  obtain ⟨ρ,hc⟩ := earn_station ha hv hh hw hm hR
  obtain ⟨α,W,hL,hα,hC,hn⟩ := hi.descend N m hm R hR ρ hc
  let Q := scribe (H.H N m) W
  have hadj := Deployment.adj a m
  obtain ⟨he,h₁⟩ := hp.emits _ _ hadj
  have hC' := q.classicalCost.pos_ij (a.clock.J (m+1)) (a.clock.J m)
  have hT : OnPage H L N m Q := ⟨rfl,hL, Deployment.nextPath ha g hv m Q (charged _ _ (q.widths.rate ..) (hh.rows N m hm.le)
    he h₁ (hh.all N m hm.le 1) (by
      refine (hp.classic _ _ hadj).trans ?_
      unfold classicalFee
      have hP := (a.params (m+1)).paths_pos
      apply le_mul_of_one_le_right (by linarith)
      rw [add_assoc,add_assoc]
      exact le_add_of_nonneg_right (by positivity)) hC)⟩
  have hd := add_le_add_left hα 1
  refine ⟨Q,α,ρ,hT,hc, ?_, fun n => earn_period ha hv hh hw hO hm n hR hT hc (hn n)⟩
  rw [Deployment.params ha]
  exact hd.trans (s.drift q _ _ hadj)

lemma sweep {m N : ℕ} (hm : m≤N) :
    ∃ (R : ℕ → PathData G) (α : ℕ → ℝ) (ρ : ∀ m : ℕ, Curves a m), AtPeak a N (R N) ∧
      (∀ i, m ≤ i → i≤N → OnPage H L N i (R i)) ∧
      ∀ i,m ≤ i → i<N → Jump H (B.price P) O N i (R (i+1)) (R i) (α i) (ρ i) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    obtain ⟨R,hR,hr⟩ := earn_top ha hp hh hw hi N
    exact ⟨fun _ => R,0,fun _ _ _ => 0,hr,fun i h h' => (le_antisymm h' h).symm ▸ hR,fun _ h h' => (h'.not_ge h).elim⟩
  | of_succ m hm ih =>
    obtain ⟨R,α,ρ,hr,hR,h⟩ := ih
    obtain ⟨Q,α',ρ',hQ,hq⟩ := earn_jump ha g hp hv hh hw hO hi hm (hR _ le_rfl hm)
    refine ⟨update R m Q,update α m α', update ρ m ρ', ?_,fun i hu hy => ?_,fun i hx ht => ?_⟩
    · simpa only [update_of_ne hm.ne'] using hr
    · rcases eq_or_lt_of_le hu with hu|hu
      · subst i; simpa using hQ
      simpa only [update_of_ne hu.ne'] using hR i hu hy
    · have hz : i+1 ≠ m := by omega
      rcases eq_or_lt_of_le hx with hx|hx
      · subst i; simpa only [update_self,update_of_ne hz] using hq
      simpa only [update_of_ne hz,update_of_ne hx.ne'] using h i hx ht

/-- Priced full Kin from `Invoices` at an actual call position. Same kinetic
witness usable at EVERY further operation. Does not include an E/K step or
select the trajectory in β, nor assert prices of those follow from Kin. -/
theorem planning_support : ∃ M : Kin H O, M.Planned (B.price P) ∧
    (∀ N m,m ≤ N → OnPage H L N m (M.path N m)) ∧
    ∀ N m,m < N → WarmAt H N m (B.η (a.clock.J (m+1))) (M.path N (m+1)) (M.stationary N m) := by
  choose R α ρ hA hL h using fun N : ℕ => sweep ha g hp hv hh hw hO hi (Nat.zero_le N)
  exact ⟨⟨α,R,ρ⟩, ⟨ha.stage.symm,ha.lengths.symm,fun N m hm => (hL N m (Nat.zero_le _) hm).linked,
    fun N m hm => (hL N m (Nat.zero_le _) hm).2.2, fun N => (hA N).2,fun N => (hA N).1,
    fun N m p hm U => ((h N m (Nat.zero_le _) hm).hot p U).1, fun N m p hm U =>
      ⟨((h N m (Nat.zero_le _) hm).hot p U).2.1, ((h N m (Nat.zero_le _) hm).hot p U).2.2.1⟩,
    fun N m p hm U => ((h N m (Nat.zero_le _) hm).laws p U).1,fun N m hm => (h N m (Nat.zero_le _) hm).kinetic,
    fun N m p hm U => ((h N m (Nat.zero_le _) hm).laws p U).2⟩,
    fun N m => hL N m (Nat.zero_le _),fun N m hm => (h N m (Nat.zero_le _) hm).hot⟩

theorem planning : ∃ M : Kin H O, M.Planned (B.price P) ∧ ∀ N m,m ≤ N → L N m (M.path N m) := by
  obtain ⟨M,hM,hm,-⟩ := planning_support ha g hp hv hh hw hO hi
  exact ⟨M,hM,fun i j h => (hm i j h).2.1⟩
end YM.Progress.Joint
