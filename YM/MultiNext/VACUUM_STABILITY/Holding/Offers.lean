import YM.MultiNext.VACUUM_STABILITY.Component.Compiled
import YM.MultiNext.VACUUM_STABILITY.Holding.Wealth


set_option warningAsError false

/-!
# Offer at the actual family

Even earlier gate.

Theorem:
for a commissioned path whose unmarked operator estimates price holding these inputs,
get the multi Stability from the UNMARKED physical prices and chosen projection/w's.

Doesn't
assume the orbit chosen this way.

Concerts paid once with the compatible family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Holding
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture Puff Stamp
open Arrival Arrival.Flock Tune Gauss Tree YM.Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {f p : Side} {Q : Rep G f} {P : Rep G p}
  {o : V→Site p} {F : Flock V G f}

/-- Support goals from Curves. -/
def cleared {Y : Type*} (r : Ratio p f) (ref : V→Option Y) (o : V→Site p)
    (X : V→ℕ→Support f) (D : V→Pulse G f) (i : V) (L : Support p) : Prop := if ref i=none then
      (∃ z, (X i z).image r.parent ⊆ L) ∨ (∃ q : Pack _,(D i).2 q ≠ 0 ∧ q.zone.image r.parent ⊆ L)
    else o i∈L



/-- Actual price inputs in terms of uniformly quoted unmarked component estimates.
All operations at these committed choices. Keep normalization and projected
linear closures together. -/
structure Appointment [Fintype V] (S : StepData p f) (Q : Rep G f) (P : Rep G p) (o : V→Site p)
    (F : Flock V G f) (L : V→Support p→Prop) (T : Finset V) (w : V→Pulse G p)
    (κ β η b : ℝ) where
  I : Type
  [occurrences : Countable I]
  R : Currency G f p
  useR : R.Live
  exactR : R.ratio=S.ratio
  licenses : R.M=P.p.B
  samePrice : R.P=Q.p
  θ : ℝ
  W : ℝ
  tree : Forest S.ratio
  traversal : Allocation G S θ W
  brush : Brush V G p
  A : Pasture (Station I F) brush
  parts : Slicer brush
  χ : ℝ
  m : ℕ
  safe : 1 ≤ χ
  chart : Charts brush P.p
  details : Hire (F:=F) (I:=I) chart
  /-- transferred unmarked background estimates, allocations/prices post/pre-L -/
  K : ℝ
  J : ℝ
  H : ℝ
  l : ℕ
  k : ℕ
  cost : ℕ
  normal : 0 ≤ K ∧ 1 ≤ J ∧ 0 ≤ H
  continuity : R.strong ≥ (Rates.inner P.p+13)+2
  t : ℝ
  threshold : 0 ≤ t ∧ siteUnit P.p.B*t ≤ 1 ∧
    coat K J l*H*(sizeTax (l+k)*(Real.exp t-1)) ≤ Tune.Price.first P.p m χ
  e : ℝ
  c : ℝ
  cabin : 0≤e ∧ crossingPrice R cost e c b β η ≤ t
  tax : Station I F → ℝ
  paid : Passable Q F R A tax cost e c
  pattern : Table Q F R A
  holds : details.Approved Q A K J H κ k l tax
  -- identities/context also not from the affordability proofs
  steam : ∃ back, Flow S tree traversal F Q P.p A back
  local_raw (i) : LocalOn (brush.u i).zone (brush.u i).stamp.ink ∧ Measurable (brush.u i).stamp.ink ∧
      GaugeInvariant (brush.u i).stamp.ink
  lives (i) : Legible P.p (brush.pack i) (brush.d i).ink
  pilot (i) : i∉T → brush.pay i=0
  stamps (i) : Rejoin.Spanned P.p (parts.base i).zone (parts.base i).stamp.ink ∧ (parts.base i).stamp.name=0 ∧
      ∀ U,Healthy P.p.threshold (parts.base i).zone U → (parts.base i).stamp.ink U=0
  placements (i) : (parts.cuts i).Receipted P.p m χ ∧
      ∀ x, x∈T → (brush.chapter i).stamp.name=spike x → L x (parts.cuts i).ringSites
  restore : parts.Landed P T w
  royalties : ∃ u : ℕ→ℝ, (∀ i, ∀ U, ‖(parts.base i).stamp.ink U‖ ≤ u i) ∧
      Ac.Hit (fun i => (parts.base i).zone) P.p.B u (Rates.inner P.p) (Rates.window P.p/2)

namespace Appointment
variable {L : V→Support p→Prop} {w : V→Pulse G p} {T : Finset V} [Fintype V] {κ η β b : ℝ} {S : StepData p f}
    (C : Appointment S Q P o F L T w κ β η b)

include C in
lemma suffices_for {k : V → ℝ} {D : V→Pulse G f} (hD : Attended F Q.p D (fun i => S.ratio.embed (o i)) k β)
    (he : 0<η) (hη : η ≤ 1) (hp : 0<κ) (hβ : 0<β) {σ c Λ δ : ℝ}
    (hQ : Q.Lawful σ c Λ δ b) (hb : 0 ≤ b) (hr : S.patch.Branches S.kernel G) (hv : Widens L)
    (hX : GaugeInvariant Q.exponent) {X : V→ℕ→Support f} {Y : Type*} (ref : V→Option Y)
    (hw : L=cleared S.ratio ref o X D) (hf : Silent F ref X) :
    ∃ (B : Brush V G _) (E : Restock V G _), Supported B E P.p L T ∧ Settled B E P T w ∧
        ∀ z∈allot o k η, Quoted B E P.p κ z ∧ S.push Q.beta (perturbs Q D z)=B.flush P.p z := by
  let B:=C.brush; let T':=C.parts.package P.p T
  have hD' : Attended F Q.p D (fun i => C.R.ratio.embed (o i)) k β := by rw [C.exactR]; exact hD
  have hu i := C.local_raw i
  have hS : C.A.Visited P.p L := by
    refine ⟨fun i => Charts.regular P.p C.chart i (hu i).1 (hu i).2.1 (hu i).2.2,C.lives,?_⟩
    intro i x ht
    have hs := Table.readouts Q C.pattern hD' hf i x ht
    rw [congrFun (congrFun hw x) (C.A.sites i)]; unfold cleared; simpa only [C.exactR] using hs -- dependent instance
  have hh i x := C.A.lottery hS hv i x
  have ht : Office S C.tree C.traversal (P:=P) C.A L T w C.parts (allot o k η) C.χ κ C.m F Q := by
    refine ⟨C.steam,⟨hS.ok,fun i x => hh (.inl i) x,C.lives,fun i x => hh (.inr i) x,C.pilot,
      fun i => (C.stamps i).1,fun i => (C.stamps i).2.2,fun i => (C.stamps i).2.1,fun i => (C.placements i).1,
      fun i => (C.placements i).2⟩,C.safe,?_,?_,C.restore⟩
    · intro z hz
      exact filled Q C.A C.details _ _ _ _ _ _ _ C.normal.1 C.normal.2.1 C.normal.2.2 C.holds C.R C.useR
        C.licenses C.samePrice C.cost C.e C.c C.cabin.1 C.pattern C.paid C.t _ _ C.threshold.1
        (by have hh := Rates.inner_pos P.p; linarith) C.continuity C.threshold.2.1 C.threshold.2.2 he.le hη hβ hQ hb
        C.cabin.2 o z k D hD' hz
    intro z hz
    obtain ⟨u,hv,hf⟩:=C.royalties; exact ⟨u,fun i U => by simpa [Stamp.tells,(C.stamps i).2.1] using hv i U,hf⟩
  exact ⟨B,T',Component.deposits S C.tree C.traversal C.A L T w C.parts o k η C.χ κ C.m F Q D hr hX hQ hv
    hβ hp he hη hD ht⟩
end Appointment






end YM.Multi.Vacuum.Holding
