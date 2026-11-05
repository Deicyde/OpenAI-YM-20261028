import YM.Extra.WILSON_STARTUP.Fast
import YM.Extra.WILSON_STARTUP.Roll
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Branches



set_option warningAsError false

/-!
# Repainting just the boundary, at prices fixed even before the final profile

Issue old T (here variable `K`) e.g. from Joint's Desk or before_kin's
pinning mechanism. Reprice to `inked P K` *then*, before floors, purchase
Regime etc there; still build the free shelf via old K at the same Levels.
"Built at K'" for the weaker K' would NOT suffice as input to paint!
The Clip table here can be the cheap preliminary one; tested on just
direct, not e.g. requiring the final selector/width choice to match it.

Strengthening of WilsonStartup.Change.retarget at this seam. In addition
to the Overlay to call `Change.engine`, keep towers.T identically, off-first
towers entirely, and supply Sworn for the new boundary Bed. This is NOT
Retained of the new Horizon from the free Rack; the top Bed *is* changed
(both metrics identity there). Lower Free.Present clauses remain available
as shown. No stability claim for nonlinear estimates on the old objects.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Port
open Function Filter Lattice RG Wilson Bid Precision Exterior Bloch Next Next.Scheduling WilsonStartup
open Matrix

variable {G : Gauge}

/-- Buying more room, not a claim of a stronger estimate. -/
structure BudgetLe (K U : MapPrices) : Prop where
  alpha i : U.α i ≤ K.α i
  cost i : K.Ω i ≤ U.Ω i
  floor i : U.η i ≤ K.η i

lemma relax {K U : MapPrices} (h : BudgetLe K U) {a : Levels G} {M : Horizon a} (H : M.Suffices K) : M.Suffices U :=
  ⟨fun _ _ e => Change.covered_mono (H.rows _ _ e) (h.alpha _) (h.cost _),
    fun _ _ e n => Change.floor_mono (H.all _ _ e n) (h.floor _) (h.cost _),
    fun _ _ e => Change.deep_mono _ (H.costs _ _ e) (h.alpha _) (h.cost _),
    H.crossings,H.stack,H.top⟩



private lemma bed_direct {p q : Clip} (h : p.direct=q.direct) : Design.bed p = Design.bed q := by
  unfold Design.bed Design.sideRoot Design.bulk
  rw [h]

private lemma full_direct (B : Bed) {p q : Clip} (he : p.direct=q.direct) (n : Side) : B.full p n = B.full q n := by
  unfold Bed.full; rw [he]

/-- Spin cost independent of Roll and of the non-direct Clip parameters.
First Clip is whatever we had at pricing; p' can be from the actual Call.
-/
lemma spin_bid (p : Clip) (η A : ℝ) (hη : 0 < η) :
    ∃ τ C : ℝ, 0 < τ ∧ ∀ B : Bed, ∀ p' : Clip, p.direct=p'.direct → p'.direct ≤ 1 → B.roots.strip η A →
      ∃ X : Polar.LiftRows, ∀ L k (U : Towers L), U.Deep η A k →
        (Change.spin X U).Deep τ C k ∧ ∀ c f h,
        installed (Ratio.mk (c:=c) (f:=f) L h) (Change.spin X U).mf = X.acts f * installed ⟨L,h⟩ U.mf ∧
        ((X.acts f)ᵀ*X.acts f=1 ∧ ∀ a v, Floor B p' f a v → B.diagonal.acts f=1 → X.acts f*(B.full p' f * d 1 f)=(Design.bed p').full p' f * d 1 f) := by
  obtain ⟨τ,C,ht,H⟩ := Change.spin_cost p η A hη
  refine ⟨τ,C,ht,fun B p' he hd hr => ?_⟩
  obtain ⟨X,hX⟩ := H B (he.trans_le hd) hr
  refine ⟨X,fun L k U H => ?_⟩
  obtain ⟨hc,hq⟩ := hX _ _ U H
  refine ⟨hc,fun c f h => ?_⟩
  obtain ⟨h1,h2,h3⟩ := hq c f h
  refine ⟨h1,h2,fun a v H' hD => ?_⟩
  have hg := h3 _ _ (Free.floor_direct he.symm H') hD
  rwa [bed_direct he, full_direct _ he, full_direct _ he] at hg

def strip (P : ℕ → Clip) (K : MapPrices) (i : ℕ) :=
    (spin_bid (P i) (K.α i) (K.Ω i) (K.alpha_pos i)).choose
def price (P : ℕ → Clip) (K : MapPrices) (i : ℕ) :=
    (spin_bid (P i) (K.α i) (K.Ω i) (K.alpha_pos i)).choose_spec.choose

private theorem spins (P : ℕ → Clip) (K : MapPrices) (i : ℕ) : 0 < strip P K i ∧ ∀ B : Bed, ∀ p' : Clip, (P i).direct=p'.direct → p'.direct ≤ 1 → B.roots.strip (K.α i) (K.Ω i) →
      ∃ X : Polar.LiftRows, ∀ L k (U : Towers L), U.Deep (K.α i) (K.Ω i) k →
        (Change.spin X U).Deep (strip P K i) (price P K i) k ∧ ∀ c f h,
        installed (Ratio.mk (c:=c) (f:=f) L h) (Change.spin X U).mf = X.acts f * installed ⟨L,h⟩ U.mf ∧
        ((X.acts f)ᵀ*X.acts f=1 ∧ ∀ a v, Floor B p' f a v → B.diagonal.acts f=1 → X.acts f*(B.full p' f * d 1 f)=(Design.bed p').full p' f * d 1 f) :=
    (spin_bid (P i) (K.α i) (K.Ω i) (K.alpha_pos i)).choose_spec.choose_spec

/-- One quote before further width/cost/floor choices incl startup path
budget. Beam/PostCost, Ringing etc will use THIS quote. -/
def inked (P : ℕ → Clip) (K : MapPrices) : MapPrices := {
    α := fun i => min (K.α i) (strip P K i)
    alpha_pos := fun i => lt_min (K.alpha_pos i) (spins P K i).1
    Ω := fun i => max 1 (max (K.Ω i) (price P K i))
    η := fun i => min 1 (K.η i)
    eta_pos := fun i => lt_min one_pos (K.eta_pos i) }

lemma budgetLe (P : ℕ → Clip) (K : MapPrices) : BudgetLe K (inked P K) :=
  ⟨fun _ => min_le_left .., fun _ => (le_max_left ..).trans (le_max_right ..),fun _ => min_le_right ..⟩

/-- Stronger overlay info for consumers. Doesn't say the `mf` on the
first step has been held fixed. -/
structure Painting {a : Levels G} (H M : Horizon a) : Prop extends Change.Overlay H M where
  guess_all N m : (H.towers N m).A0=(M.towers N m).A0
  t N m : (H.towers N m).T=(M.towers N m).T
  floors N m : m+1≠N → H.towers N m=M.towers N m
  beds N m : m≠N → H.H N m=M.H N m

/-- Execute the top reprice at ONE paid (or just `Levels`) geometry
without touching calendars, and without requiring any information from the
(potential) Planned witness besides that the *old* horizon is at the quoted
pre-repaint prices. Here the carrier of new Kin can already be fixed before
asking anything at Kin. -/
theorem paint (P : ℕ → Clip) (K : MapPrices) (a : Levels G) (ha : ∀ N,(P (a.clock.J N)).direct=(a.params N).clip.direct)
    (hg : ∀ N,(a.params N).clip.direct ≤ 1) (M : Horizon a) (hM : M.Suffices K) :
    ∃ H : Horizon a, H.Suffices (inked P K) ∧ Painting H M := by
  let H := Change.mapped M
  have h := Change.overlaid M
  choose X hX using fun N : ℕ => (spins P K (a.clock.J N)).2 (M.H N N) (a.params N).clip (ha N)
    (hg N) ((hM.rows N N le_rfl).2.2.2.1)
  let T := fun (N m : ℕ) => if m+1=N then Change.spin (X (m+1)) (M.towers N m) else M.towers N m
  have hT N m : (T N m).A0=(M.towers N m).A0 ∧ (T N m).T=(M.towers N m).T := by unfold T; split <;> exact ⟨rfl,rfl⟩
  have he (i : ℕ) : price P K i ≤ (inked P K).Ω i := (le_max_right ..).trans (le_max_right ..)
  let Z : Horizon a := ⟨H.H,T⟩
  have hp : Painting Z M := ⟨⟨h.peak,h.other,fun N m _ => (hT N m).1⟩,fun N m => (hT N m).1,fun N m => (hT N m).2,
    fun N m hh => if_neg hh,fun N m hh => if_neg hh⟩
  have hr := relax (budgetLe P K) hM
  refine ⟨Z,⟨fun N m hx => ?_,fun N m hx n => ?_,fun N m hx => ?_,fun N m p hx => ?_,fun N m p hx => ?_,fun N n => ?_⟩,hp⟩
  · obtain hx|rfl := lt_or_eq_of_le hx
    · rw [hp.other _ _ hx]; exact hr.rows N m hx.le
    rw [hp.peak]; exact Design.covered _ (hg _) (le_max_left ..)
  · obtain hx|rfl := lt_or_eq_of_le hx
    · rw [hp.other _ _ hx]; exact hr.all _ _ hx.le _
    rw [hp.peak]; exact Design.level _ (hg _) _ (min_le_left ..) (le_max_left ..)
  · obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [hp.floors _ _ hq.ne]; exact hr.costs N m hx
    rw [show Z.towers (m+1) m=Change.spin (X (m+1)) (M.towers (m+1) m) from if_pos rfl]
    exact Change.deep_mono _ (hX (m+1) _ _ _ (hM.costs _ _ hx) |>.1) (min_le_right ..) (he _)
  · rw [hp.other _ _ hx]
    obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [hp.other _ _ hq,hp.floors _ _ hq.ne]; exact hM.crossings _ _ _ hx
    rw [hp.peak]
    apply Change.top_diagonal (η:=K.η (a.clock.J (m+1))) (B:=M.H (m+1) (m+1)) (Ω:=K.Ω (a.clock.J (m+1))) _ (hM.all _ _ le_rfl _) (hM.top _ _)
    obtain ⟨e1,e2,e3⟩ := hM.crossings (m+1) m p hx
    constructor <;> simpa only [hp.guess_all,hp.t]
  · rw [hp.other _ _ hx]
    obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [hp.other _ _ hq,hp.floors _ _ hq.ne]; exact hM.stack _ _ _ hx
    rw [hp.peak,show Z.towers (m+1) m=Change.spin (X (m+1)) (M.towers (m+1) m) from if_pos rfl]
    obtain ⟨hL,hR,Hx⟩ := (hX (m+1) _ _ _ (hM.costs _ _ hx)).2 _ _ (a.clock.op m p).sizes
    exact Change.trans_roll (hM.stack _ _ _ hx) hL hR (Hx _ _ (hM.all _ _ le_rfl _) (hM.top _ _))
  rw [hp.peak]; simp only [Design.bed,Design.spike_acts,one_smul]





end YM.Planned.Port
