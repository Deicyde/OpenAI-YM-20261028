import YM.Slice.Positive
import YM.Slice.Copies

/-!
# Integrate seam, alone. For site seams there are only seam posts
(left/right share these). For link seams integrate the gates conditional on
whole leaves; kernel positive. Includes degenerate half length=1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory
open Lattice Wilson Cells Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} {C : Cut n}

namespace Link

def ebb (h : C.kind=.link) : ↥(gate C) := ⟨bottom C, by rw [gates h]; exact mem_insert ..⟩
def high (h : C.kind=.link) : ↥(gate C) := ⟨top C, by rw [gates h]; simp⟩
lemma clear (h : C.kind=.link) : ebb h ≠ high h := fun H => piers_split (C := C) (congr_arg Subtype.val H)

lemma points_into (h : C.kind=.link) (x : ↥(gate C)) : x=ebb h ∨ x=high h := by
  have hs (y : Per n) (hq : y∈ gate C) : y ∈ ({bottom C,top C} : Set (Per n)) := (gates h) ▸ hq
  have he := hs x x.property
  exact he.elim (fun H => Or.inl (Subtype.ext H)) (fun H => Or.inr (Subtype.ext (eq_of_mem_singleton H)))

def first (h : C.kind=.link) (x : Open C G) := x.1 ⟨bottom C+1,(below_base h).2⟩
def last (h : C.kind=.link) (x : Open C G) := x.1 ⟨top C,(leaving_top h).1⟩

lemma outer (h : C.kind=.link) (P : Dwelling C G) (β) : rim C β P =
    weight C.pos β (first h P.2.2) (first h P.2.1) (P.1.2 (ebb h)) *
      weight C.pos β (last h P.2.1) (last h P.2.2) (P.1.2 (high h)) := by
  classical
  have Hx : Finset.univ = {ebb h, high h} := Finset.ext fun x => by simp [points_into h x]
  unfold rim
  rw [Hx, Finset.prod_pair (clear h)]
  unfold follow; rw [checkpoint C (ebb h),checkpoint C (high h)]
  have he : top C+1 = level C (top C) := Eq.symm (sub_eq_iff_eq_add.mp (tr h))
  have hu : bottom C=level C (bottom C+1) := by rw [chord_end,br h]
  let p := (P.1,P.2.1,replace C P.2.2)
  rw [show (wire C p (ebb h).val).1 = first h P.2.2 from by
      change (wire C p (bottom C)).1 = _
      conv_lhs => rw [hu]
      exact hitOpp C ⟨_, (below_base h).2⟩ p,
    show (wire C p ((ebb h).val+1)).1 = first h P.2.1 from hit C ⟨_, (below_base h).2⟩ p,
    show (wire C p (high h).val).1 = _ from hit C ⟨_, (leaving_top h).1⟩ p,
    show (wire C p ((high h).val+1)).1 = last h P.2.2 from by
      change (wire C p (top C+1)).1 = _
      conv_lhs => rw [he]
      exact hitOpp C ⟨_, (leaving_top h).1⟩ p]
  all_goals rfl

instance : BorelSpace (Doors C G) := by unfold Doors Thread; infer_instance
instance : SecondCountableTopology (Doors C G) := by unfold Doors Thread; infer_instance
instance : BorelSpace (Thread G C.pos n × Thread G C.pos n) := Prod.borelSpace

/-- Two independent gates. -/
lemma independent (h : C.kind=.link) : MeasurePreserving
    (fun u : Doors C G => (u (ebb h), u (high h))) (doorM G C) ((threads n G C.pos).prod (threads n G C.pos)) := by
  let L : Doors C G →* (Thread G C.pos n × Thread G C.pos n) :=
    { toFun u := (u (ebb h),u (high h)), map_one' := rfl,map_mul' := fun _ _ => rfl }
  haveI : Measure.IsHaarMeasure ((threads n G C.pos).prod (threads n G C.pos)) := Measure.prod.instIsHaarMeasure
    (G := Thread G C.pos n) (H := Thread G C.pos n) _ _
  refine MonoidHom.measurePreserving (f := L) (by exact continuous_prodMk.mpr ⟨continuous_apply _,continuous_apply _⟩) ?_ (by simp)
  rintro ⟨a,b⟩; classical
  refine ⟨update (fun _ => a) (high h) b, ?_⟩
  simp [L, update_of_ne (clear h)]
end Link

variable (C) (β : ℝ)
def port (K : Posts C G) (V W : Open C G) := ∫ g : Doors C G, (rim C β ((K,g),V,W) : ℂ) ∂doorM G C

open Link
lemma wall (K : Posts C G) (V W : Open C G) (h : C.kind=.site) : port C β K V W=1 := by
  haveI := gates_site h
  simp [port,rim]

lemma links (K : Posts C G) (V W) (h : C.kind=.link) :
    port C β K V W = heat C.pos β (first h W) (first h V) * heat C.pos β (last h V) (last h W) := by
  simp_rw [port, outer h, Complex.ofReal_mul]
  let F := fun p : Thread G C.pos n × Thread G C.pos n =>
    (((weight C.pos β (first h W) (first h V) p.1 : ℝ) : ℂ) *
      ((weight C.pos β (last h V) (last h W) p.2 : ℝ) : ℂ))
  have hp := independent (G := G) h
  have hc (x y : Leaf G C.pos n) : Continuous fun p : Thread G C.pos n => ((weight C.pos β x y p : ℝ) : ℂ) := by
    have he := (weight_cont (G := G) (n := n) C.pos β).comp (show Continuous fun p : Thread G C.pos n => (x,y,p) from by fun_prop)
    exact Complex.continuous_ofReal.comp he
  have hx := integral_map hp.aemeasurable (show AEStronglyMeasurable F _ by
    rw [hp.map_eq]; exact (((hc _ _).comp continuous_fst).mul ((hc _ _).comp continuous_snd)).aestronglyMeasurable)
  rw [hp.map_eq] at hx
  exact hx.symm.trans (integral_prod_mul (fun p => ((weight C.pos β (first h W) (first h V) p : ℝ) : ℂ)) (fun p => ((weight C.pos β (last h V) (last h W) p : ℝ) : ℂ)))

lemma portPos (K : Posts C G) (hβ : 0 ≤ β) : NNKernel (port C β K) := by
  cases he:C.kind with
  | site => rw [show port C β K = (fun _ _ => 1) from funext fun x => funext fun y => wall C β K x y he]; exact NNKernel.one
  | link =>
    rw [show port C β K = _ from funext fun x => funext fun y => links C β K x y he]
    have H : NNKernel (fun x y : Open C G => heat C.pos β (first he y) (first he x)) := by
      intro m f
      exact ((step_positive C.pos hβ) m ((Link.first he) ∘ f)).transpose
    exact H.times ((step_positive (C.pos) hβ).titled (Link.last he))

lemma portContinuous (K : Posts C G) : Continuous fun p : Open C G × Open C G => port C β K p.1 p.2 := by
  cases he : C.kind with
  | site => simp_rw [wall C β K _ _ he]; exact continuous_const
  | link =>
    simp_rw [links C β K _ _ he]
    have hx (f : Open C G → Leaf G C.pos n) (hw : Continuous f) :
        Continuous fun p : Open C G × Open C G => heat C.pos β (f p.1) (f p.2) := by
      have h := (heat_cont (G := G) (n := n) C.pos β).comp (((hw.comp continuous_fst).prodMk
        (hw.comp (show Continuous (Prod.snd (α := Open C G)) from continuous_snd))))
      exact h
    have hp := (hx _ (show Continuous (Link.first he (G := G)) from (continuous_apply _).comp continuous_fst)).comp continuous_swap
    exact hp.mul (hx (Link.last he) (by unfold Link.last; fun_prop))
end YM.Slice
