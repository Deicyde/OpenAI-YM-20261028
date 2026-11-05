import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Terrain

set_option warningAsError false

/-!
# Locality of the coordinate tables in the actual record lookup

Separate the numerical stencil from the seed-dependence halo for the
entries. Don't delete the latter when taking footprints. All bonds here are in
positive storage orientation. Record tests give sufficient agreement of all
queries (incl for trunk & freeze) even across changes well outside.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Terrain
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Precision Exterior Bloch Tree Matrix Finset
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

-- Each bounds by outer for seed queries vs numeric for group/choice arguments.
-- Query radius at V-link level includes its GRID INITIAL SITE; for all-vertices
-- retention allocate the bounded enlarged regions in the consumer. `flag` is
-- as *stored*, not asserting that summing without an exact V-predicate is OK.
structure Teams (S : StepData c f) (o : Site c) (numeric outer : ℕ)
    (F F' : Forest S.ratio) (A A' : Stores S) (t t' : S.Choices) (V V' : Config G c) : Prop where
  signal : Peers (E:=G.El) o numeric V V'
  tree (i : Site f) : separation o (S.ratio.parent i) ≤ outer → F.up i=F'.up i
  flag (i : Site c) : separation o i ≤ outer → (i∈A.flags ↔ i∈A'.flags)
  aisle (i : Bond c) : separation o i.1 ≤ outer → (i∈A.aisles ↔ i∈A'.aisles)
  cost (i : Cell f) : separation o (S.ratio.parent i.1) ≤ outer → (i∈A.costs ↔ i∈A'.costs)
  branch (i : Site c) : separation o i ≤ outer → t.1 i=t'.1 i
  point (i : Bond c) : separation o i.1 ≤ outer → t.2 i=t'.2 i

namespace Teams
variable {F F' : Forest S.ratio} {A A' : Stores S} {t t' : S.Choices} {V V' : Config G c}
  {o p : Site c} {n r : ℕ} (h : Teams S o n r F F' A A' t t' V V')
include h
lemma reciprocate : Teams S o n r F' F A' A t' t V' V := by
  exact ⟨fun i hi => (h.signal i hi).symm,fun i hi => (h.tree i hi).symm,fun i hi => (h.flag i hi).symm,
    fun i hi => (h.aisle i hi).symm,fun i hi => (h.cost i hi).symm,fun i hi => (h.branch i hi).symm,fun i hi => (h.point i hi).symm⟩
lemma zone {k s : ℕ} (he : separation o p+k ≤ n) (ht : separation o p+s ≤ r) :
    Teams S p k s F F' A A' t t' V V' := by
  have ha i (h : separation p i ≤ s) : separation o i ≤ r := le_trans (separation_triangle o p i) (by omega)
  exact ⟨fun i hi => h.signal i ((separation_triangle _ p _).trans (by omega)),fun i hi => h.tree i (ha _ hi),
    fun i hi => h.flag i (ha _ hi),fun i hi => h.aisle i (ha _ hi),fun i hi => h.cost i (ha _ hi),
    fun i hi => h.branch i (ha _ hi),fun i hi => h.point i (ha _ hi)⟩

lemma votes {i : Bond c} {s : Signed} (he : separation o (s.act i.1)+1 ≤ r) :
    let k := choice (S:=S) s t; let m := choice (S:=S) s t'
    k.1 i.1=m.1 i.1 ∧ k.1 (i.1+step i.2)=m.1 (i.1+step i.2) ∧ k.2 i=m.2 i := by
  intro k m
  have hv j (ht : separation o (s.act j) ≤ r) : k.1 j=m.1 j := by
    change (S.patch.orient s).symm (t.1 (StepData.sendSites s 0 j))=(S.patch.orient s).symm (t'.1 (StepData.sendSites s 0 j))
    apply congr_arg; apply h.branch
    change separation o (affine s 0 j)≤r; unfold affine; simpa
  let j := i.1+step i.2
  have hz : separation o (s.act j) ≤ r := (separation_triangle _ (s.act i.1) _).trans
    ((Nat.add_le_add_left ((separation_signed ..).trans_le (Work.E01.sep_step_le ..)) _).trans he)
  refine ⟨hv _ (by omega),hv _ hz,?_⟩
  change (S.patch.offset s).symm (t.2 (StepData.sendBonds s 0 i))=(S.patch.offset s).symm (t'.2 (StepData.sendBonds s 0 i))
  apply congr_arg; apply h.point
  change separation o (sendEdge s 0 i).1≤r
  unfold sendEdge Step.used affine; split
  next ht =>
    let k := (posDir i.2).rotate s
    have hp : s.act j = s.act i.1-step (k.dir) := by
      unfold j; rw [s.act_add,← Step.vec_pos (i:=i.2),← Step.vec_rotate]; unfold k Step.vec; simp only [ht,if_true,sub_eq_add_neg]
    rw [hp] at hz
    simpa only [add_zero] using hz
  next ht => rw [add_zero]; change separation o (s.act i.1) ≤ r; omega

lemma trunk_agrees {i : Bond f} (he : separation o (S.ratio.parent i.1)+1 ≤ r) : i∈F.trunks ↔ i∈F'.trunks := by
  have H {F F' : Forest S.ratio} (h : ∀ i : Site f, separation o (S.ratio.parent i) ≤ r → F.up i=F'.up i)
      (ht : i∈F.trunks) : i∈F'.trunks := by
    obtain ⟨j,hj,hp⟩ := (F.trunk_mem_iff i).mp ht
    apply (F'.trunk_mem_iff _).mpr
    refine ⟨j,hj,?_⟩; rw [←h, hp]
    have hz : separation (S.ratio.parent i.1) (S.ratio.parent j) ≤ 1 := by
      rw [← hp]; unfold Step.used; split
      next ht =>
        have hh := Work.E03.parent_step S (j-step (F.up j).dir) (F.up j).dir
        rw [sub_add_cancel] at hh; exact hh
      next ht => rw [separation_self]; omega
    exact le_trans (separation_triangle _ (S.ratio.parent i.1) _) (by omega)
  exact ⟨H h.tree,H h.reciprocate.tree⟩

omit h in
private lemma parent_cell {i : Cell f} {j : Site c} (h : j∈startPos S i) : separation (S.ratio.parent i.1) j ≤ 4 := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
  rw [touched,square_corners] at hy
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
  have hh x i := Work.E03.parent_step S x i
  have ht w v : separation (S.ratio.parent i.1) (S.ratio.parent (i.1+step w+step v)) ≤ 4 :=
    (separation_triangle _ (S.ratio.parent (i.1+step w)) _).trans ((Nat.add_le_add (hh _ _) (hh _ _)).trans (by norm_num))
  rcases hy with hx|hx|hx|hx|hx <;> rw [hx]
  · simp
  · exact (hh _ _).trans (by omega)
  · exact ht _ _
  · exact (hh _ _).trans (by omega)
  simp
omit h in
private lemma pins {i : Bond c} {j : Site c} (h : j ∈ pinPos i) : separation i.1 j ≤ 4 := by
  rcases Finset.mem_insert.mp h with h|h
  · rw [h,separation_self]; omega
  rw [Finset.mem_singleton.mp h]; exact (Work.E01.sep_step_le ..).trans (by omega)

private lemma ballot {i : Site c} (he : separation o i+4 ≤ r) (hf : i∈A.place) : i∈A'.place := by
  have hp j (h : separation j i ≤ 4) : separation o j ≤ r := by
    apply (separation_triangle _ i _).trans; rw [separation_comm i]; omega
  rcases Finset.mem_union.mp hf with hi|hi
  swap
  · exact mem_union_right _ ((h.flag i (by omega)).mp hi)
  apply mem_union_left
  rcases Finset.mem_union.mp hi with hi|hi
  · obtain ⟨j,hj,hk⟩ := mem_biUnion.mp hi
    exact mem_union_left _ (mem_biUnion.mpr ⟨j,(h.cost _ (hp _ (parent_cell hk))).mp hj,hk⟩)
  obtain ⟨j,hj,hk⟩ := mem_biUnion.mp hi
  exact mem_union_right _ (mem_biUnion.mpr ⟨j,(h.aisle _ (hp _ (pins hk))).mp hj,hk⟩)

private lemma lists {k : ℕ} {i : Site c} (he : separation o i+k+4 ≤ r) (hf : i∈A.dome k) : i∈A'.dome k := by
  obtain ⟨j,hj,hk⟩ := halo_spec.mp hf
  apply halo_spec.mpr
  refine ⟨j,h.ballot ?_ hj,hk⟩; have ht := separation_triangle o i j; rw [separation_comm i j] at ht; omega

/-- Active AND frozen tests via full halo. Query through at least 10B of
endpoint, keep also incident partners of trunk and computations of place. -/
lemma curtain {x : ℝ} {i : Bond f} (he : separation o (S.ratio.parent i.1)+10*radiusB x+6 ≤ r) :
    onStage A F x i ↔ onStage A' F' x i := by
  have ht j (hg : separation (S.ratio.parent i.1) j ≤ 1) : j∈A.dome (10*radiusB x) ↔ j∈A'.dome (10*radiusB x) := by
    have hi : separation o j + 10*radiusB x +4 ≤ r := by have hi := separation_triangle o (S.ratio.parent i.1) j; omega
    exact ⟨h.lists hi,h.reciprocate.lists hi⟩
  unfold onStage
  rw [h.trunk_agrees (by omega),ht (S.ratio.parent i.1) (by simp),ht _ (Work.E03.parent_step ..)]
end Teams
end YM.AnalyticBridge.Covariance.Terrain
