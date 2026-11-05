import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Seeds
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils

/-!
# Spend assessed rows inside, annulus rows outside

Use (drows) in the literal Stores convention of row anchors, through
radius D ( etc D=200). Thus the two summands in LargeField boost
won't double count any anchor even at a boundary. Also compare the
selection stencil in SectorChange in its own (common physical bond)
coordinates before asking for subtraction.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
open Finset Affine

private lemma places_mono {O A : Stores S} {n} (h : Packet O A n) : O.place ⊆ A.place := by
  rw [place_plots,place_plots]
  intro i hi; obtain ⟨p,hp,ht⟩ := mem_biUnion.mp hi
  exact mem_biUnion.mpr ⟨p,h.subset_plots hp,ht⟩

lemma farther {r R} {O : Stores S} (h : r ≤ R) : O.dome r ⊆ O.dome R :=
  Corona.halo_mono h (Finset.Subset.refl _)
lemma Packet.inside {O A : Stores S} {n} (h : Packet O A n) (r) : O.dome r ⊆ A.dome r :=
  Corona.halo_mono (le_refl r) (places_mono h)

/-- Works in one orientation at literal anchors. When s ≠ 1 call with
*turned* O (see `band_bought`). -/
def anchorage (O : Stores S) (R : ℕ) : Window S where
  face := univ.filter fun p => S.ratio.parent p.1 ∈ O.dome R
  noise := univ.filter fun b => b.1∈O.dome R
  coarse := univ.filter fun x => x.1∈O.dome R
  rows := univ.filter fun i => i.1∈O.dome R

/-- The band's inner boundary is NOT part of its list. -/
def hollow (A B : Window S) : Window S := ⟨A.face \ B.face,A.noise\B.noise,A.coarse\B.coarse,A.rows\B.rows⟩

def bandRows (O : Stores S) (D B : ℕ) := hollow (anchorage O (D*B)) (anchorage O (2*B))

def harvest (A O : Stores S) (x : ℝ) (F : Forest S.ratio) (s : Signed) (D : ℕ) : Window S :=
  let H := anchorage (turnStore s O) (D*radiusB x)
  ⟨H.face.filter (fun p=>curb (shots S x) A F x s (.inl p)),
    H.noise.filter (fun i=>curb (shots S x) A F x s (.inr i)),∅,∅⟩



lemma load_inside (O : Stores S) (x : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) (T : Tube G S) :
    (anchorage O (2*radiusB x)).work T x U k V=O.assessed T x U (S.prediction U k) V := by
  unfold anchorage assessed Window.work onWindow Pressure.Stores.tally talli tallc talln talll limit outs intern coordN
  simp only [sum_add_distrib]; abel

lemma band_bought {O A : Stores S} {D B R} (h : Packet O A R) (hp : (D+2)*B ≤ R) :
    (bandRows O D B).annulus O A D B := by
  have he {i} (hi : i∈O.dome (D*B)) (hh : i∉O.dome (2*B)) : inSweep O A D B i :=
    ⟨fun hf => hh (h.zone_transfer (by rwa [← Nat.add_mul]) hi hf),hi⟩
  have ht {α : Type} [Fintype α] [DecidableEq α] (g : α → Site c) (i : α) (hi : i∈
      (univ.filter (fun i : α => g i∈O.dome (D*B))) \ (univ.filter (fun i : α => g i∈O.dome (2*B)))) : inSweep O A D B (g i) := by
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hi
    exact he (mem_filter.mp h1).2 (fun hh => h2 (mem_filter.mpr ⟨mem_univ _,hh⟩))
  refine ⟨?_,?_,?_⟩
  · exact fun i => ht (fun i : Cell f => S.ratio.parent i.1) i
  · exact fun i => ht Prod.fst (i : Bond c)
  exact fun i => ht Prod.fst (i : Cell c)

lemma curb_outside {s : Signed} {A : Stores S} {F : Forest S.ratio} {i : Where S} {x : ℝ}
    (hx : span S.patch x ≤ radiusB x/50) (he : curb (shots S x) A F x s i) :
    roots S i ∉ (turnStore s A).dome (2*radiusB x) := fun ht =>
  (guarded hx he).1 (farther (by omega) ((dome_turn ..).1 ht))

lemma harvesting {A O : Stores S} {R x} {F : Forest S.ratio} {s : Signed} {D : ℕ}
    (hx : span S.patch x ≤ radiusB x/50) (h : Packet O A R) :
    (harvest A O x F s D).selects (bandRows (turnStore s O) D (radiusB x)) := by
  let B := radiusB x; let O0:= turnStore s O
  have ht (i) (hi : curb (shots S x) A F x s i) : roots S i ∉ O0.dome (2*B) := fun he =>
    curb_outside hx hi ((h.turns s).inside _ he)
  constructor
  · intro p hp; obtain ⟨ha,hb⟩ := mem_filter.mp hp
    exact mem_sdiff.mpr ⟨ha,fun he => ht (.inl p) hb ((mem_filter.mp he).2)⟩
  intro p hp; obtain ⟨ha,hb⟩ := mem_filter.mp hp
  exact mem_sdiff.mpr ⟨ha,fun he => ht (.inr p) hb ((mem_filter.mp he).2)⟩

lemma hollow_pay (T : Tube G S) (N M : Window S) (x : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c)
    (h1 : N.face⊆M.face) (h2 : N.noise⊆M.noise) (h3 : N.coarse⊆M.coarse) (h4 : N.rows⊆M.rows) :
    N.work T x U k V + (hollow M N).work T x U k V = M.work T x U k V := by
  let a := till x; let l := temp x
  let Q := S.prediction U k
  let w : Cell f→ℝ := T.workF a U V (fiery G x S.patch.L) l
  let y : Bond c→ℝ := T.workI a Q V l
  let m := fun i:Cell c => T.workC a V l i + (T.workL a U Q V l i + T.workD a V l i)
  let n := T.workN a V l
  have i := sum_sdiff (f:=w) h1
  have j := sum_sdiff (f:=y) h2
  have q := sum_sdiff (f:=m) h3
  have r := sum_sdiff (f:=n) h4
  change (∑ k∈N.face,w k)+(∑ k∈N.noise,y k)+(∑ k∈N.coarse,m k)+(∑ k∈N.rows,n k)+
      ((∑ k∈M.face \ N.face,w k)+(∑ k∈M.noise \ N.noise,y k)+(∑ k∈M.coarse \ N.coarse,m k)+(∑ k∈M.rows \ N.rows,n k)) =
      (∑ k∈M.face,w k)+(∑ k∈M.noise,y k)+(∑ k∈M.coarse,m k)+(∑ k∈M.rows,n k)
  rw [← i,← j,← q,← r]; abel

lemma band_bill (T : Tube G S) (O : Stores S) (x : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) {D} (hD : 2 ≤ D) :
    O.assessed T x U (S.prediction U k) V + (bandRows O D (radiusB x)).work T x U k V =
      (anchorage O (D*radiusB x)).work T x U k V := by
  rw [← load_inside O x k U V T]
  let b:=radiusB x
  have he : O.dome (2*b)⊆O.dome (D*b) := farther (Nat.mul_le_mul_right b hD)
  have ht {α : Type} [Fintype α] (g : α → Site c) :
    (univ.filter (fun i : α => g i ∈O.dome (2*b))) ⊆ (univ.filter (fun i : α => g i∈O.dome (D*b))) := by
      intro i hi; exact mem_filter.mpr ⟨mem_univ _,he (mem_filter.mp hi).2⟩
  let N := anchorage O (2*b); let M := anchorage O (D*b)
  have h1 : N.face ⊆ M.face := ht (fun i : Cell f => S.ratio.parent i.1)
  have h2 : N.noise ⊆ M.noise := ht (fun i : Bond c => i.1)
  have h3 : N.coarse ⊆ M.coarse := ht (fun i : Cell c => i.1)
  have h4 : N.rows ⊆ M.rows := ht (fun i : Co c Gain => i.1)
  exact hollow_pay T N M x k U V h1 h2 h3 h4



end YM.AnalyticBridge.Annulus1AD
