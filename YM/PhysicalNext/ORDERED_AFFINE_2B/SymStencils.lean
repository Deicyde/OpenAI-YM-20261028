import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Channels

/-!
# The orientation-sensitive mask issue

`SC.shots` uses *initial* sites of positive edges, hence not by
construction closed under negative flips. Can't prove tensoriality of
F0 (with a MASK, even at rank zero); at least not from the fact that
skipped slopes on active sites are zero. Instead we prove the stronger
geometric answer here. On this coarse parent geometry each block has a
regular-capable **internal** link. Thus the test for existence detects
just the existence of a remote parent in the span. This shows the actual
curb and keep are symmetric. Also proves we can charge/query a full,
symmetric stencil of potential reads yielding the exact same answers.
Need all of this for  (see E history and project's Choices).
No statement of invariant price *families* or that all ingredient
masks or policies are themselves equivariant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymStencil
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores Exterior
open Next.SectorChange Next.SectorChange.Rows AnalyticBridge.GaussianFieldAlignment
open Channels Locations
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Read the actual tree up endpoints, including shifts for negative direction. -/
lemma limb (F : Forest S.ratio) {x : Site f} {a : Axis} (he : (x,a) ∈ F.trunks) :
    (leaf S.ratio x ∧ F.up x = posDir a) ∨
      (leaf S.ratio (x+step a) ∧ F.up (x+step a) = negDir a) := by
  obtain ⟨i,hi,h⟩ := (Forest.trunk_mem_iff _ _).1 he
  rcases hy : F.up i with ⟨j,d|d⟩
  · rw [hy] at h; change (i,j)=(x,a) at h; cases h; exact .inl ⟨hi,hy⟩
  rw [hy] at h; change (i-step j,j)=(x,a) at h; cases h; rw [sub_add_cancel]; exact .inr ⟨hi,hy⟩

/-- All four positive sides of the unit square o, o+0hat, ..., about the real root. -/
theorem vacancy (F : Forest S.ratio) (x : Site c) : ∃ e : F.Free,
    S.ratio.parent e.val.1=x ∧ S.ratio.parent (e.val.1+step e.val.2)=x := by
  let g := S.ratio
  let o := g.embed x
  let L := g.count.val/2
  have hL : 0 < L := by have ht : 3 ≤ g.count.val := S.patch.coarse; unfold L; omega
  have ho : g.parent o=x := g.embed_parent x
  have home (u : Cover) (hu : u∈box L) : g.parent (o+wrap f u)=x := by
    rw [show o+wrap f u=g.assemble (x,wrap g.count u) by rw [Ratio.assemble,g.half_lift S.patch.odd_side u hu]]
    exact g.assemble_parent _
  have hone (a : Axis) : g.parent (o+step a)=x := by
    rw [← wrap_step f a]; apply home
    rw [box_iff_layers]; intro i
    unfold layers; rw [Finset.mem_Icc]
    by_cases hi : i=a
    · simp [hi]; omega
    simp [hi]
  let i : Axis := 0; let j : Axis := 1
  let p := o+step i; let q := o+step j
  have hcorner : p+step j=q+step i := by dsimp only [p,q]; abel
  have htwo : g.parent (p+step j)=x := by
    unfold p; rw [add_assoc, ← wrap_step f i, ← wrap_step f j, ← map_add]; apply home
    rw [box_iff_layers]; intro a
    have hij : i ≠ j := by unfold i j; decide
    unfold layers; rw [Finset.mem_Icc]; by_cases ha : a=i 
    · have hb : a ≠ j := ha ▸ hij; simp [ha,hij]; omega
    by_cases hb : a=j
    · simp [hb,hij.symm]; omega
    simp [ha,hb]
  by_contra H
  have h (y : Site f) (a : Axis) (hp : g.parent y=x) (hq : g.parent (y+step a)=x) : (y,a) ∈ F.trunks := by
    by_contra ht; exact H ⟨⟨_,ht⟩,hp,hq⟩
  have branch (a : Axis) : F.up (o+step a) = negDir a := by
    have he := limb F (h o a ho (hone _))
    apply (he.resolve_left ?_).2
    exact fun hl => hl.1 (congr_arg g.embed ho.symm)
  rcases limb F (h p j (hone i) htwo) with he | he
  · rw [show F.up p=_ from branch i] at he; have hh : negDir i=posDir j := he.2; cases congr_arg Step.neg hh
  rcases limb F (h q i (hone j) (hcorner ▸ htwo)) with hv|hv
  · rw [show F.up q=_ from branch j] at hv; have hh : negDir j=posDir i := hv.2; cases congr_arg Step.neg hh
  rw [hcorner] at he; have ha : negDir j = negDir i := he.2.symm.trans hv.2; exact (show negDir j ≠ negDir i by unfold i j; decide) ha

variable (A : Stores S) (F : Forest S.ratio) (x : ℝ) (s : Signed) (b : Site c) (q : Signed) (j : Where S)

/-- Symmetric possible-read ledger on fine bonds. `span` still on the same root. -/
def sweep (S : StepData c f) (x : ℝ) : Stencils S := fun q j => Finset.univ.filter fun i =>
    ∃ y ∈ Next.SectorChange.points S i, separation (q.act (roots S j)) y ≤ span S.patch x
lemma swept {i : Bond f} : i∈sweep S x q j ↔ ∃ y ∈ Next.SectorChange.points S i, separation (q.act (roots S j)) y ≤ span S.patch x := by simp [sweep]
lemma included : shots S x q j ⊆ sweep S x q j := by
  intro i hi; exact (swept x q j).mpr ⟨_,Set.mem_insert _ _,(contains ..).mp hi⟩

def prospect := ∃ y : Site c, y ∉ A.dome (10*radiusB x) ∧ separation (q.act (roots S j)) y ≤ span S.patch x

lemma curb_exact : curb (shots S x) A F x q j ↔ prospect A x q j := by
  refine ⟨fun ⟨i,hi⟩ => ⟨_,remote i,(contains ..).mp hi⟩,?_⟩
  rintro ⟨w,hw,he⟩
  obtain ⟨i,hg,hh⟩ := vacancy F w
  let a : Active A x F := ⟨i,by simp [chill,hg,hh,hw]⟩
  exact ⟨a,(contains ..).mpr (hg.symm ▸ he)⟩

theorem exact_mask : curb (shots S x) A F x q j ↔ curb (sweep S x) A F x q j := by
  refine ⟨fun ⟨i,hi⟩ => ⟨i,included x q j hi⟩,?_⟩
  rintro ⟨i,hi⟩
  obtain ⟨y,hv,hy⟩ := (swept x q j).mp hi
  exact (curb_exact ..).mpr ⟨y,fun ht => i.property ((chill_points ..).mpr ⟨_,hv,ht⟩),hy⟩





def past : Equiv.Perm (Where S) := Equiv.sumCongr (shift (S.ratio.embed (offset s b q)) _) (shift (offset s b q) _)
lemma rooting : (s*q).act (roots S (past s b q j))= affine s b (q.act (roots S j)) := by
  have he : roots S (past s b q j)=roots S j + offset s b q := by
    obtain (i|i) := j
    · simpa only [affine,Signed.act_one] using! parent_map (S:=S) 1 (offset s b q) i.1
    rfl
  rw [he,Signed.act_add,offset,Signed.act_inv]; unfold affine; rw [Signed.act_mul]

lemma ledger {i : Bond f} : i∈sweep S x q j ↔ sendEdge s (S.ratio.embed b) i∈sweep S x (s*q) (past s b q j) := by
  rw [swept,swept,Tensor.moves_points, rooting]
  simp only [Set.exists_mem_image,affine,separation_translate,separation_signed]

theorem curb_turn : curb (shots S x) (book s b A) (Locations.forest s b F) x q j ↔
    curb (shots S x) A F x (s*q) (past s b q j) := by
  rw [exact_mask, exact_mask, curb, curb]
  rw [← (Locations.active s b A F x).exists_congr_right]
  exact exists_congr fun i => ledger ..

theorem standing (i : Slots S) : keep x (shots S x) (book s b A) (Locations.forest s b F) i ↔
    keep x (shots S x) A F (Channels.perChannel s b S i) := by
  obtain ⟨q,j|j⟩ := i <;> exact curb_turn A F x s b q _

/-- The THRESHOLD in the book is the physical one, even at equality. -/
lemma flagged (V : Config G c) (t : ℝ) : (book s b A).flags = RG.flags t (pull s b V) ↔
    A.flags = RG.flags t V := by
  have h := Work.H03.flags_send s b t V
  let e := StepData.sendSites s b
  -- map both sides
  rw [← (Finset.map_injective e.toEmbedding).eq_iff]; convert! Iff.rfl using 2
  · unfold book; change A.flags=(A.flags.map e.symm.toEmbedding).map e.toEmbedding; ext; simp only [Finset.mem_map_equiv,Equiv.symm_symm, Equiv.apply_symm_apply]
  · rw [Finset.map_eq_image]; exact h.symm

end YM.PhysicalNext.OrderedAffine2B.SymStencil
