import YM.Work.F05.Transport

/-!
# Using the same linear space for a pair of slices

Permute the link indices, no change of color basis or normalization of
volumes. Equal counts hold without requiring positive lieDim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {g : Ratio c f}

section count
variable (B T : Forest g)

private lemma used_eq_imp {x y : Site f} (hx : leaf g x) (hy : leaf g y)
    (e : (B.up x).used x = (B.up y).used y) : x = y := by
  have hh := B.rise x hx
  have ht := B.rise y hy
  cases a : (B.up x).neg <;> cases b : (B.up y).neg <;>
    simp only [Step.used, Step.vec, a, b, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq,
      ← sub_eq_add_neg] at e hh ht
  · exact e.1
  · have hi : B.height x < B.height y := by rwa [← e.1] at ht
    have hc : x + step (B.up x).dir = y := by rw [e.2, e.1, sub_add_cancel]
    exact (hi.not_gt (hc ▸ hh)).elim
  · have hi : B.height y < B.height x := by rwa [e.1] at hh
    have hc : y + step (B.up y).dir = x := by rw [← e.2, ← e.1, sub_add_cancel]
    exact (hi.not_gt (hc ▸ ht)).elim
  · have hi : x - step (B.up x).dir = y - step (B.up x).dir := by rw [← e.2] at e; exact e.1
    exact sub_left_inj.mp hi

def pinEquiv : {x : Site f // leaf g x} ≃ ↥B.trunks :=
  let F (x : {x : Site f // leaf g x}) : ↥B.trunks :=
    ⟨(B.up x.val).used x.val, (B.trunk_mem_iff _).mpr ⟨_,x.property,rfl⟩⟩
  Equiv.ofBijective F ⟨fun x y h => Subtype.ext (used_eq_imp B x.property y.property
    (congr_arg Subtype.val h)), fun i => by
      obtain ⟨x,hx,he⟩ := (B.trunk_mem_iff _).mp i.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩⟩

lemma free_card : Fintype.card B.Free = Fintype.card T.Free := by
  have h : Fintype.card ↥B.trunks = Fintype.card ↥T.trunks :=
    Fintype.card_congr ((pinEquiv B).symm.trans (pinEquiv T))
  rw [show Fintype.card B.Free = _ from Fintype.card_subtype_compl (fun x => x ∈ B.trunks),
    show Fintype.card T.Free = _ from Fintype.card_subtype_compl (fun x => x ∈ T.trunks), h]

def freeEquiv : B.Free ≃ T.Free := Fintype.equivOfCardEq (free_card B T)
end count

def countingBasis (B : Forest g) (G : Gauge) : Module.Basis (Key B G) ℝ (AxisChart G B) :=
  Module.Basis.reindex
    (Pi.basis fun _ : B.Free => (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis)
    (Equiv.sigmaEquivProd _ _)

lemma countingBasis_apply (B : Forest g) (G : Gauge) (i : Key B G) :
    countingBasis B G i = frame B i := by
  rw [countingBasis, Module.Basis.reindex_apply, Pi.basis_apply]
  rfl

variable {B T : Forest g}

def index (e : B.Free ≃ T.Free) : AxisChart G B ≃L[ℝ] AxisChart G T :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => G.Color) e

lemma index_apply (e : B.Free ≃ T.Free) (x : AxisChart G B) (i : B.Free) :
    index e x (e i) = x i := Equiv.piCongrLeft_apply_apply (fun _ => G.Color) e x i

lemma index_preserves (e : B.Free ≃ T.Free) : MeasurePreserving (index (G:=G) e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => G.Color) e

def onKey (e : B.Free ≃ T.Free) : Key B G ≃ Key T G :=
  Equiv.prodCongr e (Equiv.refl _)

lemma index_frame (e : B.Free ≃ T.Free) (i : Key B G) :
    index e (frame B i) = frame T (onKey e i) := by
  funext j
  obtain ⟨k,rfl⟩ := e.surjective j
  rw [index_apply]
  by_cases h : k=i.1 <;> simp [frame,onKey,h]

def move (e : B.Free ≃ T.Free) (x : Bid.Dir G c) (y : AxisChart G B) : AxisChart G B :=
  (index e).symm (switch B T x y)

lemma move_eq (e : B.Free ≃ T.Free) (x : Bid.Dir G c) :
    switch B T x = index e ∘ move e x := by
  funext y
  simp only [move, comp_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma move_jet (e : B.Free ≃ T.Free) : ContDiffAt ℝ ω (uncurry (move (G:=G) e)) 0 :=
  (index e).symm.contDiff.contDiffAt.comp (0 : Bid.Dir G c × AxisChart G B) (switch_jet B T)

end YM.Work.F05
