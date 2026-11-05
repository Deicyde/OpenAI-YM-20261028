import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Slice.Positive
import YM.TimeKernel.Unit



/-!
# Slab kernels *on the Euclidean regulator*

`m` interior transverse slices (width m+1 in native units). Include half
weights at endpoints. Compute adjoint by time reversal using Haar; all local
cylinder germs (not restricted to gauge invariant for trace facts).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open MeasureTheory Measure Filter Function Lattice Wilson TimeKernel Set
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {n : Side} {a : Axis} {G : Gauge} {m : ℕ}

abbrev LinksIn (m : ℕ) (G : Gauge) (a : Axis) (n : Side) := (Fin m → Leaf G a n) × (Fin (m+1) → Thread G a n)
abbrev Sequence (m : ℕ) (G : Gauge) (a : Axis) (n : Side) := (Fin (m+2) → Leaf G a n) × (Fin (m+1) → Thread G a n)

variable (G a n m) in
def middle := (Measure.pi fun _ : Fin m => trans n G a).prod
  (Measure.pi fun _ : Fin (m+1) => threads n G a)
instance : IsProbabilityMeasure (middle n a G m) := by unfold middle;infer_instance
instance : IsHaarMeasure (middle n a G m) := by
  unfold middle
  exact Measure.prod.instIsHaarMeasure ..

abbrev FieldTest (m : ℕ) (G : Gauge) (a : Axis) (n : Side) := Sequence m G a n → ℂ

def crop (a : Axis) (t : Per n) (m) (U : Circle G a n) : Sequence m G a n :=
    (fun i => (U (t+i.val)).1, fun i => (U (t+i.val)).2)
@[fun_prop] lemma crop_cont (a : Axis) (t : Per n) (m) : Continuous (crop (G := G) a t m) :=
  (continuous_pi (fun k : Fin (m+2) => continuous_fst.comp (continuous_apply (t+(k.val:Per n))))).prodMk
    (continuous_pi (fun k : Fin (m+1) => continuous_snd.comp (continuous_apply (t+(k.val:Per n)))))

def seed (x y : Leaf G a n) (v : LinksIn m G a n) : Sequence m G a n := (packet v.1 x y, v.2)

@[fun_prop] lemma seed_cont : Continuous fun p : (Leaf G a n × Leaf G a n) × LinksIn m G a n => seed p.1.1 p.1.2 p.2 := by
  unfold seed; apply Continuous.prodMk ?_ (by fun_prop); apply continuous_pi; intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [packet]; fun_prop
  simp [packet]; refine Fin.cases ?_ (fun i => ?_) j <;> simp <;> fun_prop

def weightFrame (β) (S : Sequence m G a n) := ∏ i : Fin (m+1), (weight a β (S.1 i.castSucc) (S.1 i.succ) (S.2 i) : ℂ)

def evaluated (β) (B : FieldTest m G a n) (S : Sequence m G a n) := B S * weightFrame β S

def oneElem (β : ℝ) (i : Fin (m+1)) (S : Sequence m G a n) := ((weight a β (S.1 i.castSucc) (S.1 i.succ) (S.2 i) : ℝ) : ℂ)

private lemma continuous_elem (β : ℝ) (i : Fin (m+1)) : Continuous (oneElem (n := n) (G := G) (a := a) β i) := by
  let f := fun S : Sequence m G a n => (S.1 i.castSucc,S.1 i.succ,S.2 i)
  have ht : Continuous f := by unfold f; fun_prop
  have hh : Continuous (fun p : Leaf G a n × Leaf G a n × Thread G a n => ((weight a β p.1 p.2.1 p.2.2 : ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (weight_cont a β)
  change Continuous ((fun p : Leaf G a n × Leaf G a n × Thread G a n => ((weight a β p.1 p.2.1 p.2.2 : ℝ):ℂ)) ∘ f)
  exact hh.comp ht
lemma continuous_frame (β : ℝ) : Continuous (weightFrame (m := m) (G := G) (a := a) (n := n) β) := by
  refine continuous_finsetProd (f := fun i S => oneElem β i S) (Finset.univ (α := Fin (m+1))) (fun i _ => ?_); exact continuous_elem β i

@[fun_prop] lemma eval_cont (β) (B : FieldTest m G a n) (h : Continuous B) : Continuous (evaluated β B) := h.mul (continuous_frame _)

def testB (β : ℝ) (B : FieldTest m G a n) (x y : Leaf G a n) : ℂ :=
    ∫ v, evaluated β B (seed x y v) ∂(middle n a G m)

lemma testB_cont (β) (B : FieldTest m G a n) (h : Continuous B) : possible (testB β B) := by
  have he : Continuous fun z : (Leaf G a n × Leaf G a n) × LinksIn m G a n => evaluated β B (seed z.1.1 z.1.2 z.2) :=
    (eval_cont _ _ h).comp seed_cont
  obtain ⟨c,hc⟩ := he.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  refine continuous_iff_continuousAt.mpr fun x => tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => c) (F := fun z : Leaf G a n × Leaf G a n => fun u => evaluated β B (seed z.1 z.2 u))
    (Eventually.of_forall fun i => (he.comp (show Continuous (fun p : LinksIn m G a n => (i,p)) from by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall fun u => hc (i,u)) (integrable_const _) (Eventually.of_forall fun u => ?_)
  exact (he.comp (show Continuous (fun p : Leaf G a n × Leaf G a n => (p,u)) from by fun_prop)).continuousAt.tendsto

def reverseF (S : Sequence m G a n) : Sequence m G a n := (S.1 ∘ Fin.rev, fun i => (S.2 i.rev)⁻¹)

def reverseI (S : LinksIn m G a n) : LinksIn m G a n := (S.1 ∘ Fin.rev, fun i => (S.2 i.rev)⁻¹)

lemma switched (S : LinksIn m G a n) (x y : Leaf G a n) : seed y x (reverseI S) = reverseF (seed x y S) := by
  refine Prod.ext ?_ rfl
  funext i
  change packet _ _ _ _ = packet _ _ _ _
  simp only [packet]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  simp only [Fin.snoc_castSucc, Fin.rev_castSucc]; rw [← Fin.cons_snoc_eq_snoc_cons,Fin.cons_succ]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  rw [Fin.cons_succ,Fin.rev_succ,Fin.snoc_castSucc]
  rfl

@[simp] lemma switchedFrame (S : Sequence m G a n) : reverseF (reverseF S)=S := by
  ext1 <;> ext1 <;> simp [reverseF]
@[simp] lemma switchedI (S : LinksIn m G a n) : reverseI (reverseI S)=S := by
  ext1 <;> ext1 <;> simp [reverseI]
@[fun_prop] lemma switch_cont : Continuous (reverseF : Sequence m G a n → _) := by unfold reverseF;fun_prop
@[fun_prop] lemma switchI_cont : Continuous (reverseI : LinksIn m G a n → _) := by unfold reverseI;fun_prop

def starred (B : FieldTest m G a n) : FieldTest m G a n := fun s => star (B (reverseF s))

lemma star_cont {B : FieldTest m G a n} (h : Continuous B) : Continuous (starred B) := (h.comp switch_cont).star

lemma preservationReversal : MeasurePreserving (reverseI : LinksIn m G a n → _) (middle n a G m) (middle n a G m) := by
  let L := trans n G a
  let T := threads n G a
  have he : MeasurePreserving (fun x : (Fin m→Leaf G a n) => x ∘ Fin.rev) (Measure.pi fun _ => L) (Measure.pi fun _ => L) := by
    exact measurePreserving_arrowCongr' (fun _ => trans n G a) (fun _ => trans n G a) (Fin.revPerm (n := m))
      (MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)
  have ht : MeasurePreserving (fun x : Fin (m+1) → Thread G a n => x ∘ Fin.rev) (Measure.pi fun _ => T) (Measure.pi fun _ => T) := by
    exact measurePreserving_arrowCongr' (fun _ => threads n G a) (fun _ => threads n G a) (Fin.revPerm (n := m+1))
      (MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)
  exact he.prod ((measurePreserving_pi _ _ fun i : Fin (m+1) => show MeasurePreserving (Inv.inv : Thread G a n → _) T T from
    measurePreserving_pi _ _ fun _ : Row a n => G.preserve_inv).comp ht)

lemma read_star (β) (S : Sequence m G a n) : weightFrame β (reverseF S)=star (weightFrame β S) := by
  simp only [weightFrame,Complex.star_def,map_prod,Complex.conj_ofReal,reverseF, Fin.rev_castSucc,Fin.rev_succ,Function.comp_apply]
  simp only [weight_reflect]
  exact Equiv.prod_comp Fin.revPerm (fun i : Fin (m+1) => ((weight a β (S.1 i.castSucc) (S.1 i.succ) (S.2 i) : ℝ):ℂ))

theorem starB (β) (B : FieldTest m G a n) (_ : Continuous B) : testB β (starred B) = op (testB β B) := by
  let V : LinksIn m G a n ≃ₜ LinksIn m G a n :=
    { toFun := reverseI
      invFun := reverseI
      left_inv := switchedI
      right_inv := switchedI
      continuous_toFun := switchI_cont
      continuous_invFun := switchI_cont }
  have hV : MeasurePreserving V (middle n a G m) (middle n a G m) := preservationReversal
  funext x y
  unfold testB op
  rw [Complex.star_def,← integral_conj, ← hV.integral_comp V.measurableEmbedding (fun v => evaluated β B (seed y x v) |> (starRingEnd ℂ))]
  apply integral_congr_ae; filter_upwards with v
  change evaluated β _ _ = star (evaluated β _ (seed _ _ (reverseI v)))
  simp only [evaluated,star_mul',starred,switched,read_star,star_star]

lemma integ_segment (β) (B : FieldTest m G a n) (h : Continuous B) (x y) :
    Integrable (fun v => evaluated β B (seed x y v)) (middle n a G m) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact (eval_cont β B h).comp (seed_cont.comp ((continuous_const (y := (x,y))).prodMk continuous_id))

lemma visible (β : ℝ) (x y : Leaf G a n) : testB β (m := 0) (fun _ => 1) x y = heat a β x y := by
  let B : FieldTest 0 G a n := fun _ => 1
  have he (v : LinksIn 0 G a n) : evaluated β B (seed x y v)=((weight a β x y (v.2 0) : ℝ):ℂ) := by
    simp [evaluated,B,weightFrame]; rfl
  unfold testB; rw [middle,integral_prod_symm _ (integ_segment β B continuous_const x y)]
  change (∫ y', ∫ x', evaluated β B (seed x y (x',y')) ∂_ ∂_)= _
  simp_rw [he]; simp only [integral_const,MeasureTheory.probReal_univ, one_smul]
  exact (measurePreserving_funUnique (threads n G a) (Fin 1)).integral_comp (MeasurableEquiv.measurableEmbedding _)  (fun u => ((weight a β x y u : ℝ):ℂ))
end YM.Slice
