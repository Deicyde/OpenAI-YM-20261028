import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Nil
import YM.Work.H03

/-!
# Reading the coarse birth at actual `P.p`

Even combined mode payloads have the required `UsesFinal`. Thus leaves
and newly assigned supports use actual flags and root sites. Complete output
`Active`, not yet `Radial`. Needed for volume-independent budgets. Some
proofs use Summability even of OLD marks; don't infer from payload identities
alone.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Cells MeasureTheory Measure Function Filter Finset Ac Marker Overlay Nil
open scoped Topology BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
    {P : Rep G n} {a : Bands R P} (I : Plan a)


lemma peel_meas (i : V) : Measurable (peel I i) :=
  (I.good i).borel.sub (RG.masked_measurable _ _ _ (I.good i).borel)
lemma peel_reads (i : V) : UsesFinal P.p.threshold (I.Y i) (peel I i) := by
  intro U W hU hW
  have he : Healthy P.p.threshold (I.Y i) U ↔ Healthy P.p.threshold (I.Y i) W := by
    simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hW]
  unfold peel; by_cases hp : Healthy P.p.threshold (I.Y i) U
  · rw [RG.masked_eq _ _ _ _ hp,RG.masked_eq _ _ _ _ (he.mp hp),sub_self,sub_self]
  rw [RG.masked_ne _ _ _ _ hp,RG.masked_ne _ _ _ _ (by exact mt he.mpr hp),(I.good i).sites U W hU]
lemma peel_gauge (i : V) : GaugeInvariant (peel I i) := by
  intro t U; unfold peel
  have he : Healthy P.p.threshold (I.Y i) (Lattice.gauge t U) ↔ Healthy P.p.threshold (I.Y i) U := by
    unfold Healthy; rw [gauge_flags]
  classical
  by_cases hu : Healthy P.p.threshold (I.Y i) U
  · rw [RG.masked_eq _ _ _ _ hu,RG.masked_eq _ _ _ _ (he.mpr hu),sub_self,sub_self]
  rw [RG.masked_ne _ _ _ _ hu,RG.masked_ne _ _ _ _ (by exact mt he.mp hu),(I.good i).symmetry t U]

section payload
variable (hR : P.activities.ForcedFamily P.p) (hA : a.Active)
include hR hA



lemma leaf_meas (l : Alphabet V) : Measurable (leaf I l) := by
  cases l with
  | inl i =>
    apply Measurable.add ((Bands.sends _).measurable.comp (Complex.continuous_ofReal.measurable.comp (hR.meas i)))
    exact Measurable.tsum fun j => (Bands.sends _).measurable.comp (hA.meas i j)
  | inr j => exact (Bands.sends _).measurable.comp (peel_meas I j)
lemma leaf_reads (l : Alphabet V) : UsesFinal P.p.threshold (patch I l) (leaf I l) := by
  intro U W ha hw
  cases l with
  | inl i =>
    change a.each i U=a.each i W
    unfold Bands.each; rw [hR.reads i U W ha hw]
    congr 1; refine tsum_congr fun j => ?_
    change Poly.send _ (a.entries i j U) = _
    rw [hA.inspects i j U W ha hw]; rfl
  | inr i => exact congr_arg (Poly.send (R.fire i)) (peel_reads I i U W ha hw)
lemma leaf_gauge (l : Alphabet V) : GaugeInvariant (leaf I l) := by
  intro t U
  cases l with
  | inl i =>
    change a.each i _=a.each i U
    unfold Bands.each; rw [hR.sym i t U]
    congr 1; refine tsum_congr fun j => ?_
    change Poly.send _ (a.entries i j _) = _
    rw [hA.invi i j t U]; rfl
  | inr i => exact congr_arg (Poly.send (R.fire i)) (peel_gauge I i t U)

variable {I} (T : Spares I)

lemma conn_meas (j : Block I) : Measurable (connection T j) := by
  classical
  unfold connection; apply Measurable.ite (Work.H03.eligible_measurable _ _ (hR.meas_test _))
  · exact Finset.measurable_fun_prod _ fun i _ => leaf_meas I hR hA _
  exact measurable_const
lemma conn_reads (j : Block I) : UsesFinal P.p.threshold (P.activities.forced (T.tag j)).support (connection T j) := by
  intro U W hu hw
  have he := Work.H03.eligible_reads _ _ (hR.reads_test (T.tag j)) U W hu hw
  classical
  by_cases hh : (P.activities.forced (T.tag j)).eligible P.p.threshold W
  · simp only [connection,he,hh,↓reduceIte]
    apply Finset.prod_congr rfl; intro i hi
    apply Work.H03.reads_larger ?_ (leaf_reads I hR hA i) U W hu hw
    rw [T.full]; intro x hx; exact Finset.mem_biUnion.mpr ⟨i,hi,hx⟩
  simp only [connection,he,hh,↓reduceIte]
lemma conn_gauge (j : Block I) : GaugeInvariant (connection T j) := by
  intro t U
  have he := Work.H03.eligible_gauge P.p.threshold _ _ _ (hR.symtest (T.tag j) t U)
  classical
  unfold connection; simp only [he, leaf_gauge I hR hA _ t U]
end payload

section scope
variable {w : V → ℝ} {δ κ u c d b : ℝ}
variable (hR : P.activities.Valid P.p δ κ) (hA : a.Active) (ht : a.Radial w u c d b)
include hR hA ht

lemma leaf_scope (l : Alphabet V) (U : Config G n) : Scoped {i | a.origins i∈patch I l} (leaf I l U) := by
  cases l with
  | inr j =>
    exact scope_send _ _ _ (by intro i hi; obtain rfl : i=j := Finset.mem_singleton.mp hi; exact I.origin _)
  | inl i =>
    apply scope_plus (scope_send _ _ _ (by simp [Census.quiet]))
    intro s hs; rw [Poly.share ((a.baseBound hA ht hR U).1 i)]
    have he (j) : (a.tagged i j U).part s=0 := by
      unfold Bands.tagged
      by_cases he : a.entries i j = 0
      · rw [he, Pi.zero_apply,Poly.send_zero,Poly.part_nil]
      exact scope_send _ (a.marks i j) _ (fun _ h => hA.retained i j he _ h) s hs
    simp_rw [he,tsum_zero]

lemma conn_scope (T : Spares I) (j : Block I) (U : Config G n) :
    Scoped {i | a.origins i∈(P.activities.forced (T.tag j)).support} (connection T j U) := by
  rw [T.full]
  classical
  unfold connection; split
  · refine scope_prod _ _ fun i hi => ?_
    intro s hs
    refine leaf_scope I hR hA ht i U s fun he => hs ?_
    intro k hk; exact Finset.mem_biUnion.mpr ⟨i,hi,he hk⟩
  exact fun i hi => Poly.part_nil _
end scope

section out
variable {w : V → ℝ} {δ κ u c d b : ℝ}
variable (hR : P.activities.Valid P.p δ κ) (hA : a.Active) (ht : a.Radial w u c d b)
variable {I} (T : Spares I) [Nonempty V]

lemma conn_nz (j : Block I) (s : R.Mode) (U : Config G n) (he : (connection T j U).part s≠0) :
    (P.activities.forced (T.tag j)).eligible P.p.threshold U := by
  by_contra hh; simp [connection,hh] at he

include hR hA ht
lemma operates : (attached T).Active := by
  have he (i j) : let y := attached T; let p := P.activities.forced i
      (y.marks i j).val.Nonempty ∧ Measurable (y.entries i j) ∧ Lattice.GaugeInvariant (y.entries i j) ∧
      UsesFinal P.p.threshold p.support (y.entries i j) ∧
        (∀ U, y.entries i j U≠0 → p.eligible P.p.threshold U) ∧
        (y.entries i j ≠ 0 → ∀ s∈(y.marks i j).val, y.origins s ∈ p.support) := by
    intro y p
    by_cases h : ∃ t, T.tag t=i
    · obtain ⟨t,rfl⟩ := h; unfold y
      by_cases h : ∃ s : R.Mode,s.val.Nonempty ∧ code s=j
      · obtain ⟨s,hs,rfl⟩ := h
        rw [mark_in T _ s hs,entry_in T _ s hs]
        refine ⟨hs,(Poly.part_cont s).measurable.comp (conn_meas hR.forced hA T t),fun k U => ?_,fun U W hu hw => ?_,
          fun U h => conn_nz T t s U h,?_⟩
        · dsimp only; rw [conn_gauge hR.forced hA T t k U]
        · dsimp only; rw [conn_reads hR.forced hA T t U W hu hw]
        intro hh i hi; by_contra hn
        exact hh (funext fun U => conn_scope I hR hA ht T t U s (fun he => hn (he hi)))
      obtain ⟨hf,hh⟩ := entry_extra T t j (by push Not at h; exact h)
      rw [hf, hh]
      exact ⟨Finset.singleton_nonempty _, measurable_const, fun _ _ => rfl, fun _ _ _ _ => rfl,
        fun _ h => (h rfl).elim, fun h => (h rfl).elim⟩
    unfold y; rw [mark_out T i (by tauto),entry_out T i (by tauto)]
    exact ⟨hA.occurs i j,hA.meas i j,hA.invi i j,hA.inspects i j,hA.keeps i j,hA.retained i j⟩
  have hf (i) : let y := attached T; (y.rays i).val.Nonempty ∧
      (∀ j∈(y.rays i).val,y.origins j∈y.support i) ∧ P.p.Regular (y.support i) (y.H i) := by
    dsimp only [attached]; cases h : shapes V i with
    | inl j => exact ⟨hA.proper j,hA.pins j,hA.regular j⟩
    | inr j => exact ⟨Finset.singleton_nonempty _, fun s hs => (Finset.mem_singleton.mp hs).symm ▸ I.origin j,I.good j⟩
  exact ⟨fun i => (hf i).1,fun i => (hf i).2.1,fun i => (hf i).2.2,
    fun i j => (he i j).1,fun i j => (he i j).2.2.2.2.2,
    fun i j => (he i j).2.2.2.1,fun i j => (he i j).2.2.2.2.1,fun i j => (he i j).2.1,fun i j => (he i j).2.2.1⟩
end out
end YM.Push.GridApprox.Attach
