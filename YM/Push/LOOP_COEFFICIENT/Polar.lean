import YM.Next.FOUNDATIONS.LinkBounds
import YM.Spark.Pile
import YM.Work.B09.Differential


/-!
# Complex multimode extension of real zero, first and mixed second derivatives

The complexified derivatives are multilinear, not conjugate-linear.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open LinearMap Function Matrix Filter Bloch
open scoped Topology ContDiff BigOperators ComplexConjugate Matrix.Norms.Frobenius

abbrev CSpace (n : Type) := n → ℂ

variable {m n : Type}

def cvec (x : m → ℝ) : CSpace m := fun i => (x i : ℂ)

@[ext]
structure Jet (m F : Type) [AddCommGroup F] [Module ℂ F] where
  base : F
  lin : CSpace m →ₗ[ℂ] F
  quad : CSpace m →ₗ[ℂ] CSpace m →ₗ[ℂ] F

variable [Fintype m] [DecidableEq m] {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

private lemma split_basis {𝕜 : Type} [Field 𝕜] (x : m → 𝕜) : x = ∑ i, x i • Pi.single i (1:𝕜) := by
  have he (i : m) : x i • Pi.single i (1:𝕜) = Pi.single i (x i) := by
    ext j; by_cases h : j=i <;> simp [h]
  simp_rw [he]; ext i; rw [Finset.sum_apply,Fintype.sum_pi_single]

omit [Fintype m] in
lemma cvec_single (i : m) : cvec (Pi.single i (1:ℝ)) = Pi.single i 1 := by
  ext j; by_cases h : j=i <;> simp [cvec,h]

lemma complex_ext {L T : CSpace m →ₗ[ℂ] F} (h : ∀ v : m → ℝ, L (cvec v) = T (cvec v)) : L = T := by
  apply LinearMap.ext; intro x
  rw [split_basis x,map_sum,map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [L.map_smul,T.map_smul,← cvec_single, h]

lemma complex_ext₂ {L T : CSpace m →ₗ[ℂ] CSpace m →ₗ[ℂ] F} (h : ∀ v w : m → ℝ, L (cvec v) (cvec w) = T (cvec v) (cvec w)) : L = T :=
  complex_ext fun _ => complex_ext (h _)

def color₁ (L : (m → ℝ) → F) : CSpace m →ₗ[ℂ] F where
  toFun x := ∑ i, x i • L (Pi.single i 1)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul,Finset.smul_sum]

def color₂ (B : (m → ℝ) → (m → ℝ) → F) : CSpace m →ₗ[ℂ] CSpace m →ₗ[ℂ] F := color₁ fun v => color₁ (B v)

variable [Module ℝ F] [IsScalarTower ℝ ℂ F]
lemma color₁_real (L : (m → ℝ) →ₗ[ℝ] F) (v : m → ℝ) : color₁ L (cvec v) = L v := by
  conv_rhs => rw [split_basis v, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_); rw [L.map_smul]; exact IsScalarTower.algebraMap_smul ℂ (v i) _

omit [Module ℝ F] [IsScalarTower ℝ ℂ F] in
lemma color₂_apply (B : (m → ℝ) → (m → ℝ) → F) (v w : CSpace m) :
    color₂ B v w = ∑ i, v i • ∑ j, w j • B (Pi.single i 1) (Pi.single j 1) := by
  change (∑ i, v i • color₁ (B (Pi.single i 1))) w = _
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]; rfl

lemma color₂_real (B : (m → ℝ) →ₗ[ℝ] (m → ℝ) →ₗ[ℝ] F) (v w : m → ℝ) :
    color₂ (fun x y => B x y) (cvec v) (cvec w) = B v w := by
  rw [color₂_apply]; calc
    _ = ∑ i, (cvec v i) • B (Pi.single i 1) w := Finset.sum_congr rfl (fun i _ => congr_arg _ (color₁_real (B _) w))
    _ = _ := color₁_real (B.flip w) v

section derivatives
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def actual (L : X →ₗ[ℝ] F) (f : (m → ℝ) → X) : Jet m F where
  base := L (f 0)
  lin := color₁ fun x => L (fderiv ℝ f 0 x)
  quad := color₂ fun x y => L (fderiv ℝ (fderiv ℝ f) 0 x y)

lemma actual_real₁ (L : X →ₗ[ℝ] F) (f : (m → ℝ) → X) (v : m → ℝ) : (actual L f).lin (cvec v) = L (fderiv ℝ f 0 v) :=
  color₁_real (L.comp (fderiv ℝ f 0).toLinearMap) v

lemma actual_real₂ (L : X →ₗ[ℝ] F) (f : (m → ℝ) → X) (v w : m → ℝ) : (actual L f).quad (cvec v) (cvec w) = L (fderiv ℝ (fderiv ℝ f) 0 v w) :=
  color₂_real ((fderiv ℝ (fderiv ℝ f) 0).toLinearMap₁₂.compr₂ L) v w

lemma actual_mixed (L : X →ₗ[ℝ] F) (f : (m → ℝ) → X) (v w : m → ℝ) : (actual L f).quad (cvec v) (cvec w) = L (iteratedFDeriv ℝ 2 f 0 ![v,w]) := by
  rw [actual_real₂, iteratedFDeriv_two_apply]; rfl

lemma actual_ext (L : X →ₗ[ℝ] F) (f : (m → ℝ) → X) (T : Jet m F) (h1 : L (f 0) = T.base)
    (h2 : ∀ v, L (fderiv ℝ f 0 v) = T.lin (cvec v))
    (h3 : ∀ v w, L (fderiv ℝ (fderiv ℝ f) 0 v w) = T.quad (cvec v) (cvec w)) : actual L f = T :=
  Jet.ext h1 (complex_ext fun v => (actual_real₁ ..).trans (h2 v)) (complex_ext₂ fun v w => (actual_real₂ ..).trans (h3 v w))

omit [IsScalarTower ℝ ℂ F] in
lemma actual_congr (L : X →ₗ[ℝ] F) {f g : (m → ℝ) → X} (h : f =ᶠ[𝓝 0] g) : actual L f = actual L g :=
  Jet.ext (congr_arg L h.self_of_nhds) (congr_arg (fun P : (m → ℝ) →L[ℝ] X => color₁ (L ∘ P)) h.fderiv_eq)
    (congr_arg (fun P : (m → ℝ) →L[ℝ] (m → ℝ) →L[ℝ] X => color₂ fun v w => L (P v w)) h.fderiv.fderiv_eq)
end derivatives

namespace Jet
variable {K : Type} [AddCommGroup K] [Module ℂ K]

def const (a : F) : Jet m F := ⟨a,0,0⟩

def add (A B : Jet m F) : Jet m F := ⟨A.base+B.base, A.lin+B.lin, A.quad+B.quad⟩

def push (A : Jet m E) (L : E →ₗ[ℂ] F) : Jet m F :=
  ⟨L A.base, L.comp A.lin, A.quad.compr₂ L⟩

def pre (A : Jet m E) (L : CSpace n →ₗ[ℂ] CSpace m) : Jet n E :=
  ⟨A.base,A.lin.comp L,A.quad.compl₁₂ L L⟩

def bilin (B : E →ₗ[ℂ] F →ₗ[ℂ] K) (A : Jet m E) (C : Jet m F) : Jet m K where
  base := B A.base C.base
  lin := (B A.base).comp C.lin + (B.flip C.base).comp A.lin
  quad := C.quad.compr₂ (B A.base) + (B.compl₁₂ A.lin C.lin) + (B.compl₁₂ A.lin C.lin).flip + A.quad.compr₂ (B.flip C.base)

omit [Fintype m] [DecidableEq m] [Module ℝ F] [IsScalarTower ℝ ℂ F] in
lemma bilin_lin (B : E →ₗ[ℂ] F →ₗ[ℂ] K) (A : Jet m E) (C : Jet m F) (v) :
    (bilin B A C).lin v = B A.base (C.lin v) + B (A.lin v) C.base := rfl

omit [Fintype m] [DecidableEq m] [Module ℝ F] [IsScalarTower ℝ ℂ F] in
lemma bilin_quad (B : E →ₗ[ℂ] F →ₗ[ℂ] K) (A : Jet m E) (C : Jet m F) (v w) :
    (bilin B A C).quad v w = B A.base (C.quad v w) + B (A.lin v) (C.lin w) + B (A.lin w) (C.lin v) + B (A.quad v w) C.base := rfl
end Jet

variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [Module ℝ E] [IsScalarTower ℝ ℂ E]
    {K : Type} [AddCommGroup K] [Module ℝ K] [Module ℂ K] [IsScalarTower ℝ ℂ K]

lemma actual_const (L : X →ₗ[ℝ] F) (x : X) : actual (m:=m) L (fun _ => x) = Jet.const (L x) :=
  actual_ext L _ _ rfl (fun v => by simp [Jet.const]) (fun v w => by simp [Jet.const])

lemma actual_push (A : X →ₗ[ℝ] E) (B : Y →ₗ[ℝ] F) (L : X →L[ℝ] Y) (T : E →ₗ[ℂ] F) {f : (m → ℝ) → X} (h : ContDiffAt ℝ ω f 0)
    (hs : ∀ x, B (L x) = T (A x)) : actual B (L ∘ f) = (actual A f).push T := by
  refine actual_ext B _ _ (hs _) (fun v => ?_) (fun v w => ?_)
  · rw [fderiv_comp 0 L.differentiableAt (h.differentiableAt (by simp)),L.fderiv,ContinuousLinearMap.comp_apply,hs]
    rw [Jet.push,LinearMap.comp_apply, actual_real₁]
  rw [show fderiv ℝ (fderiv ℝ (L ∘ f)) 0 v w = iteratedFDeriv ℝ 2 (L ∘ f) 0 ![v,w] by rw [iteratedFDeriv_two_apply]; rfl,
    L.iteratedFDeriv_comp_left h le_top, Jet.push, LinearMap.compr₂_apply, actual_mixed]; exact hs _

lemma actual_pre [Fintype n] [DecidableEq n] (A : X →ₗ[ℝ] E) {f : (m → ℝ) → X} (h : ContDiffAt ℝ ω f 0) (L : (n → ℝ) →L[ℝ] (m → ℝ))
    (T : CSpace n →ₗ[ℂ] CSpace m) (hs : ∀ x, cvec (L x) = T (cvec x)) : actual A (f ∘ L) = (actual A f).pre T := by
  refine actual_ext A _ _ (by simp [Jet.pre,actual]) (fun v => ?_) (fun v w => ?_)
  · rw [fderiv_comp 0 (L.map_zero.symm ▸ h.differentiableAt (by simp)) L.differentiableAt, L.fderiv, ContinuousLinearMap.comp_apply,L.map_zero,
      Jet.pre,LinearMap.comp_apply,← hs,actual_real₁]
  rw [show fderiv ℝ (fderiv ℝ (f ∘ L)) 0 v w = iteratedFDeriv ℝ 2 (f ∘ L) 0 ![v,w] by rw [iteratedFDeriv_two_apply]; rfl,
    Next.Foundations.jets_linear L (h.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,
    Jet.pre,LinearMap.compl₁₂_apply,← hs,← hs,actual_real₂]; rfl

lemma actual_add (A : X →ₗ[ℝ] E) {f g : (m → ℝ) → X} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    actual A (f+g) = (actual A f).add (actual A g) := by
  refine actual_ext A _ _ (A.map_add ..) (fun v => ?_) (fun v w => ?_)
  · rw [fderiv_add (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),_root_.add_apply,map_add, Jet.add,LinearMap.add_apply,
      actual_real₁,actual_real₁]
  rw [show fderiv ℝ (fderiv ℝ (f+g)) 0 v w = iteratedFDeriv ℝ 2 (f+g) 0 ![v,w] by rw [iteratedFDeriv_two_apply]; rfl,
    iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top), _root_.add_apply,map_add,Jet.add,LinearMap.add_apply,LinearMap.add_apply,actual_mixed,actual_mixed]

section calculus
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma prod_deriv (L : X →L[ℝ] Y →L[ℝ] Z) {f : H → X} {g : H → Y} {x v : H} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun z => L (f z) (g z)) x v = L (f x) (fderiv ℝ g x v) + L (fderiv ℝ f x v) (g x) := by
  rw [L.fderiv_of_bilinear hf hg]; rfl

lemma prod_second (L : X →L[ℝ] Y →L[ℝ] Z) {f : H → X} {g : H → Y} {x : H} (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) (v w : H) :
    fderiv ℝ (fderiv ℝ fun z => L (f z) (g z)) x v w =
      L (f x) (fderiv ℝ (fderiv ℝ g) x v w) + L (fderiv ℝ f x v) (fderiv ℝ g x w) +
        L (fderiv ℝ f x w) (fderiv ℝ g x v) + L (fderiv ℝ (fderiv ℝ f) x v w) (g x) := by
  have he : fderiv ℝ (fun z => L (f z) (g z)) =ᶠ[𝓝 x] fun z =>
      (L.precompR H (f z) (fderiv ℝ g z) + L.precompL H (fderiv ℝ f z) (g z)) := by
    filter_upwards [hf.eventually (by simp),hg.eventually (by simp)] with i hf hg
    exact L.fderiv_of_bilinear (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))
  have hf' := hf.differentiableAt (by simp); have hg' := hg.differentiableAt (by simp)
  have hf'' := (hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hg'' := (hg.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  rw [he.fderiv_eq, fderiv_fun_add (((L.precompR H).hasFDerivAt_of_bilinear hf'.hasFDerivAt hg''.hasFDerivAt).differentiableAt)
    (((L.precompL H).hasFDerivAt_of_bilinear hf''.hasFDerivAt hg'.hasFDerivAt).differentiableAt), _root_.add_apply,prod_deriv (L.precompR H) hf' hg'', prod_deriv (L.precompL H) hf'' hg',_root_.add_apply,_root_.add_apply,_root_.add_apply,add_assoc (_+_)]; rfl
end calculus

lemma actual_bilin (A : X →ₗ[ℝ] E) (B : Y →ₗ[ℝ] F) (C : Z →ₗ[ℝ] K) (L : X →L[ℝ] Y →L[ℝ] Z) (T : E →ₗ[ℂ] F →ₗ[ℂ] K)
    {f : (m → ℝ) → X} {g : (m → ℝ) → Y} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (hs : ∀ x y, C (L x y) = T (A x) (B y)) :
    actual C (fun z => L (f z) (g z)) = Jet.bilin T (actual A f) (actual B g) := by
  refine actual_ext C _ _ (hs ..) (fun v => ?_) (fun v w => ?_)
  · rw [prod_deriv L (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),map_add,hs,hs,
      Jet.bilin_lin,actual_real₁,actual_real₁]; rfl
  rw [prod_second L hf hg,Jet.bilin_quad]
  simp only [map_add,hs,actual_real₁,actual_real₂]; rfl
end YM.Push.Loops
