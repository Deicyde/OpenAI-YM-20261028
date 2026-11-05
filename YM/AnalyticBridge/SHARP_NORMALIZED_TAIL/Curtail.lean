import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Contact
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

/-! # Per-panel covariance read at V -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Contact
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Tree MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows Schur
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory Almanac Presented
open Precision Exterior SectorNext.Remainder
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio} {V : Config G c} {L : Almanac T D R F}
  {A B : Stores S} {k l : S.Choices} {X : Support c}
  {a a' : Rows.In x A F (G:=G)} {b b' : Rows.In x B F (G:=G)}

private lemma same_log (h : Pins a b) : arc a=arc b := congr_arg Subtype.val h.slot

/-- Need the common active pattern on the stencil paying for each breeze
read, independent of ancillary factors at that read. -/
def By (a : Rows.In x A F (G:=G)) (B : Stores S) := ∀ i : F.Free,
    separation (atSite a) (S.ratio.parent i.val.1) ≤ radiusB x/20 → (chill A x F i ↔ chill B x F i)

private def slot (h : Pins a b) (hy : By a B) : ↥(panels A F a) → ↥(panels B F b) := fun i => by
  have ht : meeting S x (arc a) (arc i.val) := i.property
  have hr : ¬chill B x F i.val.1.val := fun hi => i.val.1.property ((hy _
    (ht _ (Set.mem_insert ..) _ (Set.mem_insert ..))).mpr hi)
  refine ⟨(⟨i.val.1.val,hr⟩,i.val.2),?_⟩
  change meeting S x (arc b) (arc i.val); rw [← same_log h]; exact ht
private def align (h : Pins a b) (hy : By a B) : ↥(panels A F a) ≃ ↥(panels B F b) where
  toFun := slot h hy
  invFun := slot (show Pins b a from ⟨h.coord.symm,h.slot.symm⟩) (fun i hi => by
    unfold atSite at hi; rw [← same_log h] at hi; exact (hy i hi).symm)
  left_inv _ := rfl
  right_inv _ := rfl

def billRadius (S : StepData c f) (x : ℝ) := radiusB x/20+(Next.SectorChange.span S.patch x+2)

private lemma per_align {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (H : Gaussian.Table X) (H' : Gaussian.Table Y)
    (Z : X → Set X) (Z' : Y → Set Y) {i i' : X} {j j' : Y} (E : ↥(Z i) ≃ ↥(Z' j)) (hi : i∈Z i)
    (hx : i'∈Z i) (hj : j∈Z' j) (hu : j'∈Z' j) (hb : E ⟨i,hi⟩=⟨j,hj⟩) (hy : E ⟨i',hx⟩=⟨j',hu⟩)
    (hm : principal H (Z i)=(principal H' (Z' j)).submatrix E E) : per Z H i' i=per Z' H' j' j := by
  rw [per_read Z H hi hx,per_read Z' H' hj hu,hm,Matrix.inv_submatrix_equiv,submatrix_apply,hb,hy]

/-- Changing to another panel with shared holes/test set. Here V does not
move. The lanes of `per` are ordered compressed inverses! -/
lemma captive (h : S.patch.Branches S.kernel G) (hx : 120 ≤ radiusB x) (hp : Pins a b) (ht : Pins a' b')
    (hy : By a B) (he : Tags.Synchronized X k l) (hs : halo (billRadius S x) {atSite a} ⊆ X) :
    per (panels A F) (Rows.gram T x V k (shots S x) A F) a' a =
      per (panels B F) (Rows.gram T x V l (shots S x) B F) b' b := by
  let E := align hp hy
  let Z := panels A F a; let Z' := panels B F b
  let H := Rows.gram T x V k (shots S x) A F
  let H' := Rows.gram T x V l (shots S x) B F
  have hv i (hi : i∈panels A F a) : halo (Next.SectorChange.span S.patch x+2) {atSite i} ⊆ X := by
    intro j hj; obtain ⟨u,hu,hj⟩ := halo_spec.mp hj
    rw [mem_singleton.mp hu] at hj
    have ht : separation (atSite a) (atSite i)≤radiusB x/20 := hi _ (Set.mem_insert ..) _ (Set.mem_insert ..)
    exact hs (halo_spec.mpr ⟨atSite a,mem_singleton_self _,(separation_triangle ..).trans (Nat.add_le_add ht hj)⟩)
  have hW (i : Z) : Pins i.val (E i).val := ⟨rfl,rfl⟩
  have hM : Schur.principal H Z=(Schur.principal H' Z').submatrix E E := by
    ext i j; exact gram_read h (hW i) (hW j) he (hv i i.property) (hv j j.property)
  have hr : a ∈ Z := boards A F G hx a a (by rw [separation_self]; omega)
  have hY : b ∈ Z' := boards B F G hx b b (by rw [separation_self]; omega)
  have hi : a'∈Z ↔ b'∈Z' := by change meeting _ _ (arc a) (arc a')↔meeting _ _ (arc b) (arc b'); rw [same_log hp,same_log ht]
  change per (panels A F) H _ _ = per (panels B F) H' _ _
  by_cases hb : a'∈Z
  ·
    have hw : E ⟨a',hb⟩=⟨b',hi.mp hb⟩ := Subtype.ext <| Prod.ext (Subtype.ext ht.slot) ht.coord
    have hg : E ⟨a,hr⟩=⟨b,hY⟩ := Subtype.ext <| Prod.ext (Subtype.ext hp.slot) hp.coord
    exact per_align H H' _ _ E hr hb hY (hi.mp hb) hg hw hM
  rw [per_zero _ _ hb, per_zero _ _ (mt hi.mpr hb)]

lemma synchronized (h : S.patch.Branches S.kernel G) {r : Ribbon F X} (hx : 120 ≤ radiusB x)
    (p : r.Placed x A) (q : r.Placed x B) (he : Tags.Synchronized X k l)
    (hy : ∀ i : r.lit G, By (Ribbon.lighten p i) B)
    (hv : ∀ i : r.lit G, halo (billRadius S x) {atSite (Ribbon.lighten p i)} ⊆ X) :
    Ribbon.reel (fog A F T x V k) p = Ribbon.reel (fog B F T x V l) q := by
  have hh (i : r.lit G) : Pins (Ribbon.lighten p i) (Ribbon.lighten q i) := ⟨rfl,rfl⟩
  ext i j
  rw [Ribbon.reel,Ribbon.reel,submatrix_apply,submatrix_apply]
  simp only [fog,clouded, Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,
    captive h hx (hh j) (hh i) (hy j) he (hv j), captive h hx (hh i) (hh j) (hy i) he (hv i)]
end YM.AnalyticBridge.Sharp.Contact
