import YM.Slice.Segment

/-!
# Decompose into slabs and laps

Tour invariants: no repeated starts, no unused seam. Temporal thread belongs
to preceding slice. Prove EXACT integral equal to trace of kernels on tour.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open MeasureTheory Measure Filter Function Fin Lattice Wilson TimeKernel Set
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {n : Side} (a : Axis) {G : Gauge} {m : ℕ}

structure Tour (n : Side) (m : ℕ) where
  window : Fin m → ℕ
  start : Fin m → Per n
  steps (i : Fin m) : start (finRotate m i)=start i + ((window i+1:ℕ):Per n)
  bins : Bijective (fun i : Sigma (fun k : Fin m => Fin (window k+1)) => start i.1 + ((i.2.val:ℕ):Per n))

namespace Tour
variable (T : Tour n m) (G)

abbrev Width (i : Fin m) := T.window i
abbrev Slot := Sigma (fun i : Fin m => Fin (T.Width i+1))
def row (i : Fin m) (j : ℕ) : Per n := T.start i+j

def mark : T.Slot ≃ Per n := Equiv.ofBijective _ T.bins
@[simp] lemma arrival (p : T.Slot) : T.mark p = T.row p.1 p.2 := rfl
@[simp] lemma nextMark (p) : T.row p (T.Width p+1)=T.start (finRotate m p) := (T.steps p).symm

abbrev InteriorTravel := ∀ i, LinksIn (T.window i) G a n

abbrev Arena := (Fin m → Leaf G a n) × T.InteriorTravel a G

variable {G} {a}

def harvest (U : Circle G a n) : T.Arena a G :=
  (fun k => (U (T.start k)).1, fun i => (fun j => (U (T.row i (j.val+1))).1, fun j => (U (T.row i j.val)).2))

def returnTo (p : T.Arena a G) (i : T.Slot) : Layer G a n :=
    (Fin.cons (α := fun _ => Leaf G a n) (p.1 i.1) (p.2 i.1).1 i.2, (p.2 i.1).2 i.2)

def scatter (p : T.Arena a G) : Circle G a n := T.returnTo p ∘ T.mark.symm

lemma readings (u : Circle G a n) (i : T.Slot) : T.returnTo (harvest T u) i=u (T.mark i) := by
  have hv (k : Fin m) (j : Fin (T.Width k+1)) : Fin.cons (α := fun _ => Leaf G a n) (T.harvest u |>.1 k) ((T.harvest u).2 k).1 j = (u (T.mark ⟨k,j⟩)).1 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [harvest,row]
    simp [harvest,row]
  exact Prod.ext (hv _ _) rfl
@[simp] lemma roundTrip (p : T.Arena a G) (i) : scatter T p (T.mark i)=T.returnTo p i := by rw [scatter,comp_apply,Equiv.symm_apply_apply]

def pages : Circle G a n ≃* T.Arena a G where
  toFun := T.harvest
  invFun := T.scatter
  left_inv p := by
    funext i; obtain ⟨y,rfl⟩ := T.mark.surjective i
    rw [roundTrip, T.readings]
  right_inv v := by
    refine Prod.ext ?_ ?_
    · funext x
      change (scatter T v (T.start x)).1=v.1 x
      rw [show T.start x=T.mark ⟨x,0⟩ by rw [arrival]; simp [row], roundTrip, returnTo]; simp
    ext1 i; refine Prod.ext ?_ ?_
    · funext a; change (T.scatter v (_ : Per n)).1=_
      change (T.scatter v (T.mark ⟨i,a.succ⟩)).1=_; rw [roundTrip,returnTo]; simp
    funext x; change (T.scatter v (T.mark ⟨_,x⟩)).2=_; rw [roundTrip,returnTo]
  map_mul' _ _ := rfl

@[fun_prop] lemma cont_harvest : Continuous (T.harvest (G := G) (a := a)) := by unfold harvest; fun_prop
@[fun_prop] lemma cont_scatter : Continuous (T.scatter (G := G) (a := a)) := by unfold scatter returnTo; fun_prop

variable (a G)
def sea := (Measure.pi fun _ : Fin m => trans n G a).prod (Measure.pi fun i => middle n a G (T.window i))
instance : IsProbabilityMeasure (sea a G T) := by unfold sea;infer_instance
local instance (k : ℕ) : MeasurableMul (LinksIn k G a n) := by unfold LinksIn; infer_instance
instance : IsHaarMeasure (sea a G T) := by unfold sea; exact Measure.prod.instIsHaarMeasure ..

lemma books : MeasurePreserving (T.harvest (G := G) (a := a)) (spread n G a) (sea a G T) :=
  MonoidHom.measurePreserving (f := MulEquiv.toMonoidHom (pages (a := a) (G := G) T)) (μ := spread n G a) (ν := sea a G T) T.cont_harvest T.pages.surjective (by simp)

variable {G}
lemma feeds (F : Circle G a n) (i : Fin m) :
    let S := T.harvest F
    seed (S.1 i) (S.1 (finRotate _ i)) (S.2 i)=crop a (T.start i) (T.window i) F := by
  intro S
  refine Prod.ext ?_ rfl; ext1 j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [seed,packet, snoc_last,crop,harvest,S, val_last,T.steps]
  simp only [seed,packet,snoc_castSucc,crop,harvest,S,val_castSucc]; exact congr_arg Prod.fst (T.readings _ ⟨i,j⟩)

lemma identified (β) (F : Circle G a n) : ∏ i, weightFrame β (crop a (T.start i) (T.window i) F) =
    ((bare β (chain a F) : ℝ):ℂ) := by
  rw [totalWeight, Complex.ofReal_prod,← Equiv.prod_comp T.mark]
  unfold weightFrame; unfold Slot; rw [Fintype.prod_sigma]; simp [crop,row, add_assoc]

def tourProduct (B : ∀ i : Fin m, FieldTest (T.window i) G a n) (U : Config G n) :=
  ∏ i, B i (crop a (T.start i) (T.window i) (leaves a U))

theorem calculated (β) (B : ∀ i : Fin m, FieldTest (T.window i) G a n) (H : ∀ i, Continuous (B i)) :
    (partition G n β : ℂ)*moment β (tourProduct a T B) =
    ∫ v : Fin m → Leaf G a n, TimeKernel.cycle (fun i => testB β (B i)) v ∂(Measure.pi fun _ => trans n G a) := by
  have hv : Continuous (T.tourProduct a B) := continuous_finsetProd _ fun i _ =>
    (H i).comp ((crop_cont a (T.start i) _).comp (leaves_cont a))
  rw [moment_formula β _ (continuous_integrable β hv), ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (partition_pos β (G := G) (n := n)).ne'), one_mul]
  have hc : MeasurableEmbedding (chain (n := n) (G := G) a) := (Homeomorph.measurableEmbedding
    (show Circle G a n ≃ₜ Config G n from
      { toEquiv := (slice a).symm.toEquiv
        continuous_toFun := chain_cont _
        continuous_invFun := leaves_cont _ }))
  rw [← MeasurePreserving.integral_comp (chain_volume a) hc]
  let f (u : T.Arena a G) := ∏ i, evaluated β (B i) (seed (u.1 i) (u.1 (finRotate m i)) (u.2 i))
  have hi : MeasurableEmbedding (T.harvest (G := G) (a := a)) := Homeomorph.measurableEmbedding
    (show Circle G a n ≃ₜ T.Arena a G from
      { toEquiv := T.pages.toEquiv
        continuous_toFun := T.cont_harvest
        continuous_invFun := T.cont_scatter })
  have he (u : Circle G a n) : ↑(bare β (chain a u)) * T.tourProduct a B (chain a u)=f (T.harvest u) := by
    rw [← T.identified]; simp only [tourProduct,show leaves a (chain a u) = u from (slice a).apply_symm_apply _, f]
    simp_rw [T.feeds a u]; simp only [evaluated,Finset.prod_mul_distrib]; ring
  have hf : Integrable f (sea a G T) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_finsetProd; intro i _
    let z := fun p : T.Arena a G => ((p.1 i, p.1 (finRotate m i)), p.2 i)
    have hh : Continuous z := by unfold z;fun_prop
    exact (eval_cont β _ (H i)).comp (seed_cont.comp hh)
  simp_rw [he,(T.books a G).integral_comp hi,sea, integral_prod f hf]; apply integral_congr_ae
  filter_upwards with x; unfold TimeKernel.cycle testB
  exact integral_fintype_prod_eq_prod (μ := fun i => middle n a G (T.window i)) (fun i p => evaluated β (B i) (seed (x i) (x (finRotate m i)) p))

end Tour
end YM.Slice
