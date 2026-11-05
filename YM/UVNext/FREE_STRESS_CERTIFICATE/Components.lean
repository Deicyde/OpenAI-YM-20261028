import YM.Labels.Polynomial
import YM.Maxwell.Exterior
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color



/-! Equivariant color factorization of the actual radial jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Labels Tensor Maxwell Function
open scoped RealInnerProductSpace
variable {G : Gauge} {j l : ℕ}

def clone (L : G.Color →ₗ[ℝ] G.Color) : Taylor G j →ₗ[ℝ] Taylor G j where
  toFun A := ⟨fun i => L.toContinuousLinearMap.compContinuousMultilinearMap (A.val i), by
    refine ⟨fun i s r => congr_arg L (A.property.1 i s r),fun z => ?_⟩
    change ∑ i : Axis, z i • L (A.value i z) = _
    rw [← L.map_zero, ← A.radial_value z,map_sum]; simp only [map_smul]⟩
  map_add' := by intro x y; apply Subtype.ext; funext i; ext1; exact map_add L _ _
  map_smul' := by intro c x; apply Subtype.ext; funext i; ext1; exact map_smul L _ _

@[simp] theorem clone_value (L : G.Color →ₗ[ℝ] G.Color) (A : Taylor G j) (i x) :
    (clone L A).value i x = L (A.value i x) := rfl

def dye (x : G.Color) (A : Taylor G j) : G.Color →ₗ[ℝ] Taylor G j where
  toFun y := clone ((innerₛₗ ℝ x).smulRight y) A
  map_add' a b := by
    apply Taylor.value_ext; funext i v
    change (inner ℝ x (A.value i v)) • (a+b) = (inner ℝ x (A.value i v)) • a + (inner ℝ x (A.value i v)) • b
    rw [smul_add]
  map_smul' t a := by
    apply Taylor.value_ext; funext i v
    change (inner ℝ x (A.value i v)) • (t • a) = t • ((inner ℝ x (A.value i v)) • a)
    rw [smul_comm]

@[simp] theorem dye_value (x : G.Color) (A : Taylor G j) (y i z) :
    (dye x A y).value i z = (inner ℝ x (A.value i z)) • y := rfl

@[simp] theorem paint_dye (x : G.Color) (A : Taylor G j) (y) (u : G.El) :
    Taylor.paint u (dye x A y) = dye x A (G.adjoint u y) := by
  apply Taylor.value_ext; funext i v; simp

def valueAt (i : Axis) (z : E4) : Taylor G j →ₗ[ℝ] G.Color where
  toFun A := A.value i z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local notation "paintBasis" => EuclideanSpace.basisFun

theorem dye_sum (A : Taylor G j) : ∑ i, dye (paintBasis G.ColorIndex ℝ i) A
    (paintBasis G.ColorIndex ℝ i) = A := by
  apply Taylor.value_ext; funext a v
  change valueAt a v (∑ i, _) = _
  rw [map_sum]
  change ∑ i, inner ℝ _ (A.value a v) • _ = A.value a v
  simpa only [OrthonormalBasis.repr_apply_apply] using ((paintBasis G.ColorIndex ℝ).sum_repr (A.value a v))

def dyeJet (x : G.Color) (A : Jet G) : G.Color →ₗ[ℝ] Jet G := LinearMap.pi fun j => dye x (A j)

theorem no_jet_linear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (h : G.Simple) (f : Jet G →ₗ[ℝ] Y) (hi : ∀ u v, f (colored u v) = f v) : f=0 := by
  apply LinearMap.ext; intro A
  have he (x : G.Color) : f.comp (dyeJet x A) = 0 := no_linear h _ (fun u v => by
    change f (fun j => dye x (A j) (G.adjoint u v)) = _
    simp_rw [← paint_dye]; exact hi u _)
  change f A = 0
  conv_lhs => rw [show A = ∑ i, dyeJet (paintBasis G.ColorIndex ℝ i) A (paintBasis G.ColorIndex ℝ i)
      from funext fun j => by rw [Finset.sum_apply]; exact (dye_sum (A j)).symm]
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => LinearMap.congr_fun (he _) _

abbrev Place (j : ℕ) := (Axis × Axis) × (Fin j → Axis)

/-- Actual curl Taylor coefficient on the specified axes. -/
def component (p : Place j) : Taylor G j →ₗ[ℝ] G.Color where
  toFun A := Maxwell.takeCurl A p.1.1 p.1.2 (YM.basis ∘ p.2)
  map_add' A B := by simp [Maxwell.takeCurl, smul_sub, smul_add]; abel
  map_smul' u A := by simp [Maxwell.takeCurl, smul_sub, smul_comm u]

theorem component_clone (p : Place j) (L : G.Color →ₗ[ℝ] G.Color) (A : Taylor G j) :
    component p (clone L A) = L (component p A) := by
  simp [component, Maxwell.takeCurl, clone]

@[simp] theorem component_dye (p : Place j) (x y : G.Color) (A : Taylor G j) :
    component p (dye x A y) = (inner ℝ x (component p A)) • y := by
  change component p (clone _ A) = _
  rw [component_clone]; rfl

@[simp] theorem component_paint (p : Place j) (u : G.El) (A : Taylor G j) :
    component p (Taylor.paint u A) = G.adjoint u (component p A) :=
  component_clone ..

theorem captured : Injective (LinearMap.pi (component (G:=G) (j:=j))) := by
  intro A B he
  apply Maxwell.potential.injective; apply Subtype.ext
  funext i a
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin j => (paintBasis Axis ℝ).toBasis)
  intro v
  have ht := congr_fun he ((i,a),v)
  change Maxwell.takeCurl A i a (YM.basis ∘ v) = Maxwell.takeCurl B i a (YM.basis ∘ v) at ht
  change Maxwell.takeCurl _ _ _ _ = Maxwell.takeCurl _ _ _ _
  simpa [YM.basis, Function.comp_def] using ht

/-- Even though the components needn't be independent there is an exact
component expansion, with equivariant color legs. -/
theorem synth (h : G.Simple) (j : ℕ) :
    ∃ T : Place j → G.Color →ₗ[ℝ] Taylor G j,
      (∀ (A : Taylor G j), ∑ p, T p (component p A) = A) ∧
      (∀ p u x, Taylor.paint u (T p x) = T p (G.adjoint u x)) := by
  classical
  haveI := h.nontrivial_color
  have hz : 0 < G.lieDim := by
    rw [Gauge.lieDim, ← G.colorIso.finrank_eq]
    exact Module.finrank_pos
  let b := paintBasis G.ColorIndex ℝ
  let y := b ⟨0,hz⟩
  let E := LinearMap.pi (component (G:=G) (j:=j))
  obtain ⟨R,hR⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr captured)
  let S (p : Place j) : Taylor G j := R (Pi.single p y)
  refine ⟨fun p => dye y (S p),fun A => ?_,fun p u x => paint_dye ..⟩
  have hA (i) : dye (b i) A y = ∑ p, inner ℝ (b i) (component p A) • S p := by
    have he : dye (b i) A y = R (E (dye (b i) A y)) := (LinearMap.congr_fun hR _).symm
    rw [he]
    simp_rw [S, ← R.map_smul, ← map_sum R]
    congr 1; funext p
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    change component p (dye _ A y) = _
    simp [component_dye, smul_ite]
  apply Taylor.value_ext; funext a v
  change valueAt a v (∑ p, _) = _
  rw [map_sum]
  change ∑ p, inner ℝ y ((S p).value a v) • component p A = _
  calc
    _ = ∑ p, inner ℝ y ((S p).value a v) • ∑ i, inner ℝ (b i) (component p A) • b i := by
      simp only [← b.repr_apply_apply, b.sum_repr]
    _ = ∑ i, (∑ p, inner ℝ (b i) (component p A) * inner ℝ y ((S p).value a v)) • b i := by
      simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul, mul_comm (inner ℝ y _)]
      rw [Finset.sum_comm]
    _ = ∑ i, inner ℝ (b i) (A.value a v) • b i := by
      apply Finset.sum_congr rfl; intro i _
      congr 1
      have H := congr_arg (fun q => (innerₛₗ ℝ y) (valueAt a v q)) (hA i)
      simp only [map_sum,map_smul, smul_eq_mul] at H
      change inner ℝ y ((dye (b i) A y).value a v) = _ at H
      rw [dye_value, real_inner_smul_right] at H
      change inner ℝ (b i) (A.value a v) * inner ℝ y y = _ at H
      simpa [y, b.inner_eq_one,valueAt] using H.symm
    _ = A.value a v := by simp only [← b.repr_apply_apply,b.sum_repr]

theorem component_form (h : G.Simple) (B : Taylor G j →ₗ[ℝ] Taylor G l →ₗ[ℝ] ℂ)
    (hi : ∀ u x y, B (Taylor.paint u x) (Taylor.paint u y) = B x y) :
    ∃ c : Place j → Place l → ℂ, ∀ x y,
      B x y = ∑ i, ∑ k, inner ℝ (component i x) (component k y) • c i k := by
  classical
  obtain ⟨R,hR,hT⟩ := synth h j; obtain ⟨S,hS,hV⟩ := synth h l
  let f i k : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℂ := (((B.comp (R i)).flip.comp (S k)).flip)
  choose c hc using fun i k => complex_color_form h (f i k) (fun u x y => by
    change B (R i (G.adjoint u x)) (S k (G.adjoint u y)) = _
    rw [← hT, ← hV,hi]; rfl)
  refine ⟨c,fun x y => ?_⟩
  conv_lhs => rw [← hR x, ← hS y]
  simp only [map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hc i k _ _

end YM.UVNext.FreeStress
