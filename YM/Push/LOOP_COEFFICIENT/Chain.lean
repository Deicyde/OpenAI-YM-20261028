import YM.Push.LOOP_COEFFICIENT.Coordinates

/-!
# Finite real calculus of left increment jets

In off-shell formulas keep the entire curvature correction. Analytic here
means a local statement with the parameters / period held fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Set Function Filter Lattice Exterior Precision Wilson
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m n k : Type} {E F H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma second_chain {f : E → F} {g : F → H} {x} (hg : ContDiffAt ℝ ω g (f x))
    (hf : ContDiffAt ℝ ω f x) (v w : E) :
    iteratedFDeriv ℝ 2 (g ∘ f) x ![v,w] =
      iteratedFDeriv ℝ 2 g (f x) ![fderiv ℝ f x v, fderiv ℝ f x w] +
      fderiv ℝ g (f x) (iteratedFDeriv ℝ 2 f x ![v,w]) := by
  have he : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] fun z => (fderiv ℝ g (f z)).comp (fderiv ℝ f z) := by
    filter_upwards [hf.eventually (by simp),hf.continuousAt.eventually (hg.eventually (by simp))] with z hf hg
    exact fderiv_comp z (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp))
  have hf' := hf.differentiableAt (by simp)
  have hd := (hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hg' := (hg.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, he.fderiv_eq,
    fderiv_clm_comp (show DifferentiableAt ℝ (fun z => fderiv ℝ g (f z)) x from hg'.comp x hf') hd,
    show fderiv ℝ (fun z => fderiv ℝ g (f z)) x = _ from fderiv_comp x hg' hf']
  simp [add_comm]

lemma partial_fd {f : E → F → H} {x : E} {y : F} (h : ContDiffAt ℝ ω (uncurry f) (x,y)) :
    ContDiffAt ℝ ω (uncurry fun v w => fderiv ℝ (f v) w) (x,y) :=
  ContDiffAt.fderiv (m:=ω) (x₀:=(x,y))
    (f := fun v : E × F => f v.1) (g := Prod.snd)
    (h.comp (f := fun v : (E × F) × F => (v.1.1, v.2)) ((x,y),y) (by fun_prop)) contDiffAt_snd
    (by simp)

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def grad (f : (n → ℝ) → ℝ) (x : n → ℝ) : n → ℝ := fun i => fderiv ℝ f x (Pi.single i 1)

lemma grad_dotProduct (f : (n → ℝ) → ℝ) (x v : n → ℝ) : grad f x ⬝ᵥ v = fderiv ℝ f x v := by
  let L := fderiv ℝ f x
  change ∑ i, L (Pi.single i 1) * v i = L v
  calc
    _ = ∑ i, L (Pi.single i (v i)) := Finset.sum_congr rfl fun i _ => by
      rw [show Pi.single i (v i) = (v i) • Pi.single i (1:ℝ) by
        ext j; by_cases h : j=i <;> simp [*,Pi.single_eq_of_ne], map_smul]; exact mul_comm ..
    _ = _ := by rw [← map_sum, show ∑ i, Pi.single i (v i) = v by ext i; rw [Finset.sum_apply, Fintype.sum_pi_single]]

lemma bilinearAt_dotProduct (f : (n → ℝ) → ℝ) (x v w : n → ℝ) :
    v ⬝ᵥ (bilinearAt f x *ᵥ w) = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [bilinearAt, ← Matrix.toLinearMap₂'_apply']
  change ((LinearMap.toMatrix₂' ℝ).symm ((LinearMap.toMatrix₂' ℝ) _) v w : ℝ) = _
  rw [LinearEquiv.symm_apply_apply, Work.F05.bend_apply]

def twist (f : (n → ℝ) → (m → ℝ)) (x : n → ℝ) (v : m → ℝ) : Matrix n n ℝ :=
  ∑ i, v i • bilinearAt (fun z => f z i) x

omit [DecidableEq m] in lemma twist_zero (f : (n → ℝ) → (m → ℝ)) (x : n → ℝ) : twist f x 0 = 0 := by simp [twist]

omit [DecidableEq m] in
lemma component_second {f : E → (m → ℝ)} {x : E} (hf : ContDiffAt ℝ ω f x) (i : m) (v w : E) :
    iteratedFDeriv ℝ 2 (fun y => f y i) x ![v,w] = iteratedFDeriv ℝ 2 f x ![v,w] i := by
  let P := ContinuousLinearMap.proj (φ:=fun _ : m => ℝ) (R:=ℝ) i
  change iteratedFDeriv ℝ 2 (P ∘ f) _ _ = _
  rw [second_chain P.contDiff.contDiffAt hf, iteratedFDeriv_two_apply]
  simp only [P.fderiv,show fderiv ℝ (P : (m → ℝ) → ℝ) = fun _ => P from funext fun _ => P.fderiv,
    fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,zero_add]; rfl

omit [DecidableEq m] in
lemma twist_dotProduct {f : (n → ℝ) → (m → ℝ)} {x : n → ℝ} (hf : ContDiffAt ℝ ω f x) (a : m → ℝ)
    (v w : n → ℝ) : v ⬝ᵥ (twist f x a *ᵥ w) = a ⬝ᵥ iteratedFDeriv ℝ 2 f x ![v,w] := by
  unfold twist
  rw [Matrix.sum_mulVec,dotProduct_sum]
  simp_rw [Matrix.smul_mulVec,dotProduct_smul, bilinearAt_dotProduct, component_second hf]; rfl

lemma pairing_ext {𝕜 : Type*} [CommRing 𝕜] {X Y : Matrix m n 𝕜}
    (h : ∀ x y, x ⬝ᵥ (X *ᵥ y) = x ⬝ᵥ (Y *ᵥ y)) : X = Y := by
  ext i j
  simpa using h (Pi.single i 1) (Pi.single j 1)

lemma bilinearAt_chain {f : (m → ℝ) → (n → ℝ)} {g : (n → ℝ) → ℝ} {x} (hg : ContDiffAt ℝ ω g (f x))
    (hf : ContDiffAt ℝ ω f x) :
    bilinearAt (g ∘ f) x = (linearAt f x).transpose * bilinearAt g (f x) * linearAt f x +
      twist f x (grad g (f x)) := by
  refine pairing_ext fun v w => ?_
  simp only [bilinearAt_dotProduct, second_chain hg hf, add_mulVec,dotProduct_add,twist_dotProduct hf,grad_dotProduct]
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    linearAt_mulVec,linearAt_mulVec, bilinearAt_dotProduct]

lemma bilinearAt_add {f g : (m → ℝ) → ℝ} {x} (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) :
    bilinearAt (fun x => f x + g x) x = bilinearAt f x + bilinearAt g x := by
  ext i j; simp only [Matrix.add_apply, bilinearAt_apply]
  -- local functions only
  change iteratedFDeriv ℝ 2 (f+g) x _ = _
  rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top)]; rfl

def localize (f : PatchField G m → PatchField G n) (U : PatchField G m) : Array G m → Array G n :=
  fun a => displacement (f U) (f (vary U a))

/-- Group-to-group derivative in left tangents. -/
def rate (f : PatchField G m → PatchField G n) (U : PatchField G m) := linearAt (localize f U) 0

def acceleration (f : PatchField G m → PatchField G n) (U : PatchField G m) (v : Array G n) := twist (localize f U) 0 v

def first (f : PatchField G m → ℝ) (U : PatchField G m) : Array G m := grad (f ∘ vary U) 0

def cost (f : PatchField G m → ℝ) (U : PatchField G m) := bilinearAt (f ∘ vary U) 0

omit [DecidableEq m] [DecidableEq n] in
lemma localize_diff {f : PatchField G m → PatchField G n} {U : PatchField G m} (hf : MatDiffAt (f ∘ vary U) 0) :
    ContDiffAt ℝ ω (localize f U) 0 := (matDiffAt_const _).displacement hf (by simp)

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
@[simp] lemma localize_zero (f : PatchField G m → PatchField G n) (U : PatchField G m) : localize f U 0 = 0 := by simp [localize]

omit [DecidableEq m] [DecidableEq n] in
lemma localized {f : PatchField G m → PatchField G n} {U : PatchField G m} (hf : MatDiffAt (f ∘ vary U) 0) :
    f ∘ vary U =ᶠ[𝓝 0] vary (f U) ∘ localize f U := by
  apply Filter.EventuallyEq.symm
  refine hf.continuousAt.tendsto.eventually (p := fun v => vary (f U) (displacement (f U) v)=v) ?_
  simpa only [Function.comp_apply, vary_zero] using! vary_displacement (f U)

lemma cost_comp {f : PatchField G m → PatchField G n} {g : PatchField G n → ℝ} {U}
    (hf : MatDiffAt (f ∘ vary U) 0) (hg : ContDiffAt ℝ ω (g ∘ vary (f U)) 0) :
    cost (g ∘ f) U = (rate f U).transpose * cost g (f U) * rate f U + acceleration f U (first g (f U)) := by
  rw [cost,bilinearAt_congr (show (g ∘ f) ∘ vary U =ᶠ[𝓝 0] (g ∘ vary (f U)) ∘ localize f U by
      exact (localized hf).mono (fun x hx => congr_arg g hx)),
    bilinearAt_chain (by simpa only [localize_zero] using hg) (localize_diff hf),localize_zero]; rfl

lemma cost_add {f g : PatchField G m → ℝ} {U : PatchField G m}
    (hf : ContDiffAt ℝ ω (f ∘ vary U) 0) (hg : ContDiffAt ℝ ω (g ∘ vary U) 0) :
    cost (f + g) U = cost f U + cost g U := bilinearAt_add hf hg

omit [DecidableEq m] in
lemma MatDiffAt.along {U : PatchField G m} {v : E → PatchField G m} {x} {g : PatchField G m → H}
    (hv : MatDiffAt v x) (h : v x = U) (hg : ContDiffAt ℝ ω (g ∘ Loops.vary U) 0) : ContDiffAt ℝ ω (g ∘ v) x := by
  rw [← show Loops.displacement U (v x) = 0 by rw [h, displacement_self]] at hg
  refine (hg.comp (f:=fun t => Loops.displacement U (v t)) x ((matDiffAt_const _).displacement hv h)).congr_of_eventuallyEq ?_
  have he := hv.continuousAt.tendsto; rw [h] at he
  exact (he.eventually (vary_displacement U)).mono fun i hi => congr_arg g hi.symm

-- useful when applying the jets on backgrounds
omit [DecidableEq m] [DecidableEq n] in
lemma matrix_diff {f : E → Matrix m n ℝ} {x} (h : ∀ i j, ContDiffAt ℝ ω (fun y => f y i j) x) :
    ContDiffAt ℝ ω f x := by
  have he : ContDiff ℝ ω (Matrix.of : (m → n → ℝ) ≃ Matrix m n ℝ) :=
    (Matrix.ofLinearEquiv ℝ (m:=m) (n:=n) (α:=ℝ)).toContinuousLinearEquiv.contDiff
  exact he.contDiffAt.comp (f:=fun y : E => fun i j => f y i j) x
    (contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (h i)))

omit [DecidableEq n] in
lemma linearAt_diff {f : E → (m → ℝ) → (n → ℝ)} {x : E} {y : m → ℝ} (hf : ContDiffAt ℝ ω (uncurry f) (x,y)) :
    ContDiffAt ℝ ω (uncurry fun v w => linearAt (f v) w) (x,y) := by
  apply matrix_diff; intro i j
  exact (contDiffAt_apply ℝ ℝ i _).comp (x,y) ((partial_fd hf).clm_apply (g:=fun _ => Pi.single j 1) contDiffAt_const)

lemma bilinearAt_diff {f : E → (m → ℝ) → ℝ} {x : E} {y : m → ℝ} (hf : ContDiffAt ℝ ω (uncurry f) (x,y)) :
    ContDiffAt ℝ ω (uncurry fun v w => bilinearAt (f v) w) (x,y) := by
  apply matrix_diff; intro i j
  exact ((partial_fd (partial_fd hf)).clm_apply (g:=fun _ => Pi.single i 1) contDiffAt_const).clm_apply (g:=fun _ => Pi.single j 1) contDiffAt_const

lemma grad_diff {f : E → (m → ℝ) → ℝ} {x : E} {y : m → ℝ} (hf : ContDiffAt ℝ ω (uncurry f) (x,y)) :
    ContDiffAt ℝ ω (uncurry fun v w => grad (f v) w) (x,y) :=
  contDiffAt_pi.mpr fun i => (partial_fd hf).clm_apply (g:=fun _ => Pi.single i 1) contDiffAt_const
end YM.Push.Loops
