import YM.Shoot.Race
import YM.PCalc.Loop

/-!
# Adapters to actual T stack (ADJ branch, uninhabited inputs possible)

Strengths beyond endpoint used as sufficient criteria for later developments;
specialize estimates to one history of any given cutoff and its continuations
only. `Directed.a` fixes exactly Levels. `Prog` candidate ties α used in
reset to determinant gate, not arbitrarily redistributing β per p. Any
additional scratch data/tests needed for eligibility during steps and later
IR/matching can be stored in retainers. Record which trajectory produced B.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Input
open Lattice Wilson RG Precision Shoot Supply
open Filter MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators Topology

variable {G : Gauge} {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}

/-- dependent pass-through code, build even for m=0. Every return estimator
must hold for the same B/B' chosen. -/
structure Directed (G : Gauge) {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} (I : Wait Y)
    (Z : ChartRatio G) (K : MapPrices) (P : PostCost D) where
  a : Levels G
  valid : Paid I a
  ratio : LocalRatio Z
  M : Horizon a
  kin : Kin M Z
  plan : M.Suffices K
  support : kin.Planned P
  bake : Recipe a
  bases : bake.path=kin.path

variable {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}

namespace Directed
variable (B : Directed G I Z K P)

/-- Coupling reset associated to same paths and map.

Use actual reference coupling claim reconstructed here after
band comparability in positive lane.

No drift until using determinant sign. -/
structure Move (N m p) (u : Rep G (B.a.S.side m p)) (v : Rep G (B.a.S.side (m+1) p)) : Prop where
  ident : u.eval=(B.a.clock.op m p).push v.beta v.eval
  step : B.bake.next N m p u v
  bundle : Lives B.bake N m p u
  forced :
    u.activities.KBound u.p (Real.exp (-(P.g (B.a.clock.J (m+1)))*(B.a.clock.monitor (m+1))^2))
  δ : |u.beta-v.beta-B.kin.alpha N m| ≤ 1

lemma links {N m p} (hk : m<N) {u v} (h : Move B N m p u v) : B.bake.Relays N m p u v := by
  refine ⟨h.ident,?_,h.step⟩
  obtain ⟨h₁,h₂⟩ := abs_le.mp h.δ
  have he := B.support.kinetic N m hk
  apply abs_le.mpr
  obtain ⟨ht,hi⟩ := (abs_le.mp <| le_sub_iff_add_le.mpr he)
  constructor <;> linarith

structure Program (B : Directed G I Z K P) : Prop where
  begins N p : ∃ F, Curve (B.a.budget N) (n:=B.a.S.side N p) F (band B.a N) ∧
      ∀ β∈band B.a N,(F β).beta=β ∧ Lives B.bake N N p (F β) ∧ B.bake.Starter N p (F β)
  advances N p (m : ℕ) : m < N →
    ∀ l u : ℝ, l ≤ u → ∀ Q, Curve (B.a.budget (m+1)) Q (Set.Icc l u) →
      (∀ x∈ Set.Icc l u, Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta ∈ band B.a (m+1)) →
      ∃ T, Curve (B.a.budget m) T (Set.Icc l u) ∧
        ∀ x∈ Set.Icc l u,B.Move N m p (T x) (Q x)

lemma supplies (h : B.Program) (N p : ℕ) : B.bake.Issues N p := by
  refine ⟨h.begins N p,fun m hk l v hu Q hw hx => ?_⟩
  obtain ⟨E,e,he⟩ := h.advances N p m hk l v hu Q hw hx
  exact ⟨E,e,fun x hj => ⟨(he _ hj).bundle,B.links hk (he x hj)⟩⟩

/-- If also need EXTRA outputs Move.forced/δ retained, set `bake.next`
to include those! Here ready for next consumers of Stays. -/
lemma actually (hG : G.Simple) (h : B.Program) : ∃ T, B.bake.Stays T ∧ (B.bake.make T).Selected ∧
    ∀ N m p, m≤N → Attached (B.M.H N m) (((B.bake.make T).rep N p m).path) := by
  obtain ⟨T,HT,H⟩ := B.bake.races hG (B.supplies h) (Drifting.pay B.valid)
  refine ⟨T,HT,H,fun N m p hm ↦ ?_⟩
  have he := ((HT N p).prices m (Nat.zero_le _) hm).1.path
  change Attached _ (T N p m).path
  rw [he,B.bases]; exact B.support.links N m hm
/-- Build a history *retaining* the actual Move tickets (δ from the
    kinetic reset on THIS Kin, and stronger exp at forcing) as well as
    the initially exposed bake.stays tests. Need no assumption on what
    choices the spatial history carries at unrelated periods. -/
theorem holding (hG : G.Simple) (h : B.Program) : ∃ T, B.bake.Stays T ∧
    (B.bake.make T).Selected ∧ ∀ N m p, m<N → B.Move N m p (T N p m) (T N p (m+1)) := by
  let R := { B.bake with next := fun N m p u v => B.Move N m p u v }
  have hp N p u : Lives R N N p u ↔ Lives B.bake N N p u := by
    constructor <;> rintro ⟨A,X,C,T,Z⟩ <;> exact ⟨A,X,C,T,Z⟩
  have hv n m p u : Lives R n m p u ↔ Lives B.bake n m p u := by
    constructor <;> rintro ⟨A,X,C,T,Z⟩ <;> exact ⟨A,X,C,T,Z⟩
  have hh N p : R.Issues N p := by
    constructor
    · obtain ⟨u,H,U⟩ := h.begins N p
      refine ⟨u,H,fun t ht ↦ ?_⟩
      obtain ⟨a,b,c,d,y⟩ := U t ht
      exact ⟨a,(hp ..).2 b,c,d,y⟩
    intro m hm l u hl Q hQ hL
    obtain ⟨x,hx,Z⟩ := h.advances N p m hm l u hl Q hQ (fun x hx => ⟨(hv ..).1 ((hL x hx).1),(hL x hx).2⟩)
    exact ⟨x,hx,fun t ht ↦ ⟨(hv ..).2 (Z t ht).bundle, (Z t ht).ident,(B.links hm (Z t ht)).drift,Z t ht⟩⟩
  obtain ⟨T,t,w⟩ := R.races hG hh (Drifting.pay B.valid)
  have he N m p (h : m < N) : B.Move N m p (T N p m) (T N p (m+1)) := ((t N p).persists m (Nat.zero_le _) h).continues
  refine ⟨T,?_,w,he⟩
  intro N p; have hu := (t N p).fromTop
  exact ⟨fun i hi hx => ⟨(hv ..).1 ((t N p).prices i hi hx).1,((t N p).prices i hi hx).2⟩,
    ⟨hu.scalars,hu.raw,hu.inits⟩, fun i _ hi => B.links hi (he N i p hi)⟩
end Directed
end YM.Input
