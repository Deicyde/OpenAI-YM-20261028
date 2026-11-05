import YM.Extra.MULTISOURCE_BOUNDS.Trajectory
import YM.Further.THRESHOLD_SOURCE_RESTART.License
import YM.Further.THRESHOLD_SOURCE_RESTART.Omissions
/-!
# A kernel-estimate port for kraw in the unscaled comparison wire

Notation: output level R and inputs on P (not necessarily at same beta or
threshold). Use with actual cutoff comparison steps; see the Propagate files.
Disentangle pricing (on these actual terms) from producing the unintegrated /
first-system facts asserting even the pre-exclusion expansion computes the
integral. Session receipt does *not* assume support-weighted rents of the
resulting Bands. Geometry counted before estimating the sums, and forces paid
again after log omissions. No canonical singleton reallocation in this step.

`Pre` is the physical input decomposition cut, `Receipt.book` still requires
actual per-entry estimates, including the unmarked hard ones in the right
alphabet. In particular it is legitimate to produce that data algorithmically
with the usual propagations *if* the cost proofs and complete identity are
also produced. This file not claiming existence of compatible leases stage by
stage or of actual kernel expansions under those prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {V : Type*} [DecidableEq V] [Fintype V] {R : Census V} {α : Type}
variable {n m : Side} {P : Rep G n} {Q : Rep G m} {o : V → Site m}
variable {M : Bands R P} {C D : Capital} {w : V → ℝ} {B : ℕ} {u a b c : ℝ}

/-- List pointwise laws for the omission-containing identity cut. No
claim that just bounding the real push of individual marks would suffice.
-/
structure Session (Q : Rep G m) (o : V → Site m) (R : Census V) (α : Type) where
  setup : Pre Q o R α
  drawer : Vault Q o R
  actual : drawer.hard=setup.hard

omit [Fintype V] in
lemma affordable {M' : ℕ} {F : Bands R Q} (h : Prepare.Further F w M' D.a u b c)
    (he : M'=Q.p.B) (hu : u≤D.unit) (hb : b≤D.b) (hc : c≤D.divisor*D.c) : Owned F D w := by
  subst M'
  obtain ⟨s,hs,hS⟩ := h.bulk; obtain ⟨p,hp,hP⟩ := h.hits
  obtain ⟨t,ht,hT⟩ := h.regular_budget; obtain ⟨y,hy,hY⟩ := h.forced_budget
  refine { h with units := fun i => (h.units i).trans hu
                  bulk := ⟨s,hs,fun i => Budget.mono (hS i) (hS i).1 (fun _ => le_rfl) hb⟩
                  hits := ⟨p,hp,fun i => Budget.mono (hP i) (hP i).1 (fun _ => le_rfl) hc⟩
                  regular_budget := ⟨t,ht,fun i => Budget.mono (hT i) (hT i).1 (fun _ => le_rfl) hb⟩
                  forced_budget := ⟨y,hy,fun i => Budget.mono (hY i) (hY i).1 (fun _ => le_rfl) hc⟩ }

omit [Fintype V] in
lemma atoms_cost (L : Pre Q o R α) {e : α → ℝ} (hg : ∀ i,0 ≤ e i ∧ ∀ U,
    Healthy Q.p.threshold (L.regular.sites i) U → ‖L.regular.H i U‖ ≤ e i)
    (h : Rooted (fun i => (L.regular.tag i).val) L.regular.sites B a
      (tariff w (fun i => (L.regular.tag i).val) e) b) : L.regular.Cost w B a b := by
  refine ⟨e,hg,fun i => ?_⟩
  simpa only [emit,tariff, LogTerms.duty,Poly.toll, mul_comm (Real.exp _)] using! h i

omit [Fintype V] in
lemma atoms_levy (L : Pre Q o R α) {e : α → ℝ} (hg : ∀ i,0 ≤ e i ∧ ∀ U,
    Healthy Q.p.threshold (L.regular.sites i) U → ‖L.regular.H i U‖ ≤ e i)
    (h : Ac.Hit L.regular.sites B (tariff w (fun i => (L.regular.tag i).val) e) a b) :
    ∃ f : α → Poly R, (∀ i U,Width.Covered (L.docks.letter i U) (f i)) ∧
      Ac.Hit L.docks.patch B (fun i => Poly.price w (f i)) a b := by
  let f i := Poly.send (L.regular.tag i) (e i:ℂ)
  have ht i : Poly.price w (f i)=Poly.toll w (L.regular.tag i)*e i := by
    rw [Poly.solo, Complex.norm_real,Real.norm_of_nonneg (hg i).1] -- f
  refine ⟨f,fun i U => ?_,?_⟩
  · rw [L.amendment]
    apply covered_send _ rfl
    exact value_of_mask _ _ _ _ (hg i).1 (fun h => by rw [norm_neg]; exact (hg i).2 _ h)
  simp_rw [ht]; exact h

namespace Session
variable (S : Session Q o R α)

/-- Cost tests before the omission merger. Incoming `Income` here is NOT
an assumption of a rooted result, but knobs from the fine bands (pinned
units, no positive prices from blanks if value on own mask is zero).
`ξ` can buy K exports under a stronger rate than even the output wants,
to get enough back through the full-comparison array with omissions.
This is an application at specific Q,P,r on this call (and would need
kernel estimates with admissible parameter scopes in ultimate use). Test even strengths on every
entry of the physical representation, with the actual exponent
reservations at those supports.
-/
structure Receipt (M : Bands R P) (μ : ℕ) (C D : Capital) : Prop where
  book : ∃ ξ old raw l : ℝ, 0 < ξ ∧ ξ ≤ 1 ∧ 0 ≤ old ∧ 0 ≤ raw ∧ 0 ≤ l ∧
    let L := S.setup.regular
    let F := S.drawer
    let B := Q.p.B
    VacuumReserve Q B (D.a+1) (ξ*old) ∧
    (∀ e, Income M C.divisor e →
      ∃ g : α → ℝ, (∀ i,0 ≤ g i ∧ ∀ U, Healthy Q.p.threshold (L.sites i) U → ‖L.H i U‖ ≤ g i) ∧
        Licence M m e C B μ o (fun i => (L.tag i).val) L.sites g (D.a+1) D.b l ∧
        ∃ f c, (∀ i,0 ≤ f i ∧ ∀ U, ‖F.entry i U‖ ≤ f i) ∧
          Licence M m e C B μ o (fun i => (F.mark i).val) (KSite Q) f (D.a+1) c (ξ*raw)) ∧
    ((B+B+1:ℕ):ℝ)^4*(old+raw+l) ≤ 1 ∧ ξ*(Real.exp (old+raw+l)-1) ≤ D.divisor*D.c

variable [Countable α] [Nonempty V]


end Session
end YM.Further.ThresholdSourceRestart
