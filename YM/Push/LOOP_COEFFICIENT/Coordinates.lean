import Mathlib.Analysis.Calculus.Deriv.Polynomial
import YM.Push.LOOP_COEFFICIENT.Color
import YM.Push.LOOP_COEFFICIENT.Tangent
import YM.Work.F05.Calculus


/-!
# Real counting coordinates for physical group arrays & left tangents
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Set Function Filter Lattice Exterior Precision Wilson
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m n k : Type} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Point (G : Gauge) (m : Type) := m × G.ColorIndex
abbrev Array (G : Gauge) (m : Type) := Point G m → ℝ
abbrev PatchField (G : Gauge) (m : Type) := m → G.El
-- local name only

def paint (G : Gauge) (m : Type) : Array G m ≃ₗ[ℝ] (m → G.Color) :=
  (LinearEquiv.curry ℝ ℝ m G.ColorIndex).trans
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ _).symm)

@[simp] lemma paint_apply (v : Array G m) i j : paint G m v i j = v (i,j) := rfl
@[simp] lemma paint_unapply (v : m → G.Color) (i j) : (paint G m).symm v (i,j) = v i j := rfl

variable [Fintype m] [Fintype n] [Fintype k]

def fromColor (G : Gauge) (m : Type) [Fintype m] : (m → G.Color) ≃L[ℝ] Array G m :=
  ((paint G m).symm).toContinuousLinearEquiv

lemma paint_diff {v : E → Array G m} {x} (h : ContDiffAt ℝ ω v x) (i) :
    ContDiffAt ℝ ω (fun t => paint G m (v t) i) x :=
  (contDiff_apply ℝ _ i).contDiffAt.comp (f := (fromColor G m).symm ∘ v) x
    ((fromColor G m).symm.contDiff.contDiffAt.comp x h)

def vary (U : PatchField G m) (v : Array G m) : PatchField G m :=
  fun x => bump (U x) (paint G m v x)

def displacement (U V : PatchField G m) := (paint G m).symm fun i => delta (U i) (V i)

omit [Fintype m] in
@[simp] lemma vary_zero (U : PatchField G m) : vary U 0 = U := by ext1 i; simp [vary]
omit [Fintype m] in
@[simp] lemma vary_one (v : Array G m) (i : m) : vary 1 v i = G.lieExp (paint G m v i) := by simp [vary,bump]
omit [Fintype m] in
@[simp] lemma displacement_self (U : PatchField G m) : displacement U U = 0 := by simp [displacement]; rfl

lemma vary_displacement (U : PatchField G m) : ∀ᶠ V in 𝓝 U, vary U (displacement U V) = V := by
  filter_upwards [eventually_all.mpr fun i => ((continuous_apply i).tendsto U).eventually (bump_delta (U i))]
    with V hv
  funext i
  simpa only [vary,displacement, LinearEquiv.apply_symm_apply] using! hv i

lemma displacement_vary (U : PatchField G m) : ∀ᶠ v in 𝓝 (0:Array G m), displacement U (vary U v) = v := by
  filter_upwards [eventually_all.mpr fun i =>
    (show Tendsto (fun v => paint G m v i) (𝓝 0) (𝓝 0) by
      simpa only [id_eq,map_zero, Pi.zero_apply] using! (paint_diff (contDiffAt_id (x:=(0 : Array G m))) i).continuousAt.tendsto).eventually
        (delta_bump (U i))] with v hv
  change (paint G m).symm _ = v
  rw [(paint G m).symm_apply_eq]; exact funext hv

/-- `SmoothAt` is a predicate about the actual group arrays, using Frobenius on matrices. -/
def MatDiffAt (v : E → PatchField G m) (x : E) := ∀ i, ContDiffAt ℝ ω (fun t => G.mat (v t i)) x

omit [Fintype m] in lemma MatDiffAt.continuousAt {v : E → PatchField G m} {x} (h : MatDiffAt v x) : ContinuousAt v x :=
  continuousAt_pi.mpr (fun i => tendsto_mat.mpr (h i).continuousAt)



omit [Fintype m] in lemma MatDiffAt.comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → E} {v : E → PatchField G m} {x : X} (hv : MatDiffAt v (f x)) (hf : ContDiffAt ℝ ω f x) :
    MatDiffAt (v ∘ f) x := fun i => (hv i).comp x hf

omit [Fintype m] in lemma matDiffAt_const {x : E} (v : PatchField G m) : MatDiffAt (fun _ => v) x := fun _ => contDiffAt_const

lemma MatDiffAt.vary {U : E → PatchField G m} {v : E → Array G m} {x} (h : MatDiffAt U x) (hv : ContDiffAt ℝ ω v x) :
    MatDiffAt (fun t => vary (U t) (v t)) x := fun i => mat_bump_diff (h i) (paint_diff hv i)

lemma MatDiffAt.displacement {U V : E → PatchField G m} {x} (hU : MatDiffAt U x) (hV : MatDiffAt V x)
    (h : V x = U x) : ContDiffAt ℝ ω (fun t => Loops.displacement (U t) (V t)) x :=
  (fromColor G m).contDiff.contDiffAt.comp (f := fun t i => delta (U t i) (V t i)) x
    (contDiffAt_pi.mpr (fun i => delta_diff (hU i) (hV i) (congr_fun h i)))

lemma vary_diff {x : Array G m} {U : PatchField G m} : MatDiffAt (vary U) x :=
  (matDiffAt_const _).vary contDiffAt_id

@[fun_prop] lemma vary_cont {U : PatchField G m} : Continuous (vary U) := continuous_iff_continuousAt.mpr
    (fun _ => vary_diff.continuousAt)

def Cohort (u : G.El) : Array G m →ₗ[ℝ] Array G m := (paint G m).symm.toLinearMap.comp <|
  (LinearMap.pi fun i => (G.adjoint u).comp <| (LinearMap.proj i).comp (paint G m).toLinearMap)

omit [Fintype m] in
@[simp] lemma paint_cohort (u : G.El) (a : Array G m) (i) : paint G m (Cohort u a) i = G.adjoint u (paint G m a i) := by
  change paint G m ((paint G m).symm _) i = _
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma cohort_null {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : G.Simple)
    (L : Array G m →ₗ[ℝ] V) (hv : ∀ u a, L (Cohort u a) = L a) : L = 0 := by
  classical
  let T := L.comp (paint G m).symm.toLinearMap
  have he (i : m) : T.comp (LinearMap.single ℝ _ i) = 0 := by
    refine invariant_null h _ (fun u x => ?_)
    change L ((paint G m).symm (Pi.single i (G.adjoint u x))) = L ((paint G m).symm (Pi.single i x))
    conv_rhs => rw [← hv u]
    congr 1; rw [(paint G m).symm_apply_eq]; ext1 j
    rw [paint_cohort, LinearEquiv.apply_symm_apply]; by_cases hj : j=i <;> simp [*,Pi.single_eq_of_ne]
  apply LinearMap.ext
  intro v; rw [← (paint G m).symm_apply_apply v]; change T _ = 0
  rw [show paint G m v = ∑ i, LinearMap.single ℝ _ i (paint G m v i) from ?_,map_sum]
  · exact Finset.sum_eq_zero fun i _ => DFunLike.congr_fun (he i) _
  ext1 i; rw [Finset.sum_apply]; exact (Fintype.sum_pi_single ..).symm

lemma cohort_flat {f : Array G m → ℝ} (h : G.Simple) (hd : DifferentiableAt ℝ f 0)
    (hi : ∀ u : G.El, f ∘ Cohort u =ᶠ[𝓝 0] f) : fderiv ℝ f 0 = 0 := by
  suffices (fderiv ℝ f 0).toLinearMap = 0 from ContinuousLinearMap.ext (fun v => DFunLike.congr_fun this v)
  refine cohort_null h _ fun u a => ?_
  let L := Cohort (m:=m) u |>.toContinuousLinearMap
  have hv := (hi u).fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp 0 (show DifferentiableAt ℝ f (Cohort u (0:Array G m)) by simpa only [map_zero] using hd)
    L.differentiableAt, map_zero, show fderiv ℝ (Cohort (m:=m) u) 0 = _ from L.fderiv] at hv
  exact DFunLike.congr_fun hv a

omit [Fintype m] in lemma vary_cohort (a : Array G m) (U : PatchField G m) (u : G.El) :
    vary (fun i => u * U i * u⁻¹) (Cohort u a) = fun i => u * vary U a i * u⁻¹ := by
  ext1 i; rw [vary, paint_cohort,bump_transform]; rfl

variable [DecidableEq m] [DecidableEq n]

def linearAt (f : (m → ℝ) → (n → ℝ)) (x : m → ℝ) : Matrix n m ℝ :=
  LinearMap.toMatrix' (fderiv ℝ f x).toLinearMap

def bilinearAt (f : (m → ℝ) → ℝ) (x : m → ℝ) : Matrix m m ℝ :=
  LinearMap.toMatrix₂' ℝ (Work.F05.bend f x)

lemma bilinearAt_apply (f : (m → ℝ) → ℝ) (x : m → ℝ) (i j : m) :
    bilinearAt f x i j = iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1] := by
  rw [← Work.F05.bend_apply]; rfl

lemma bilinearAt_congr {f g : (m → ℝ) → ℝ} {x : m → ℝ} (h : f =ᶠ[𝓝 x] g) : bilinearAt f x = bilinearAt g x := by
  rw [bilinearAt,bilinearAt, Work.F05.bend_congr h]

lemma bilinearAt_comp {f : (n → ℝ) → ℝ} {g : (m → ℝ) → (n → ℝ)} {x : m → ℝ} (hf : ContDiffAt ℝ ω f (g x))
    (hg : ContDiffAt ℝ ω g x) (hz : fderiv ℝ f (g x) = 0) :
    bilinearAt (f ∘ g) x = (linearAt g x).transpose * bilinearAt f (g x) * linearAt g x := by
  rw [bilinearAt, Work.F05.bend_comp_stationary hf hg hz, LinearMap.toMatrix₂'_compl₁₂]; rfl

omit [Fintype n] [DecidableEq n] in lemma linearAt_mulVec (f : (m → ℝ) → (n → ℝ)) (x u : m → ℝ) : linearAt f x *ᵥ u = fderiv ℝ f x u := by
  rw [linearAt, LinearMap.toMatrix'_mulVec]; rfl

lemma linearAt_det (f : (m → ℝ) → (m → ℝ)) (x) : (linearAt f x).det = (fderiv ℝ f x).det :=
  LinearMap.det_toMatrix' _

-- Common lattices
abbrev Bonds (c : Side) := Edge (Site c)
abbrev Links (G : Gauge) (c : Side) := Array G (Bonds c)
abbrev Nodes (G : Gauge) (c : Side) := Array G (Site c)
abbrev NodeField (G : Gauge) (c : Side) := PatchField G (Site c)
abbrev Joint (c f : Side) := Bonds f ⊕ Site c
abbrev Dual (G : Gauge) (c f : Side) := Array G (Joint c f)
abbrev Inputs (G : Gauge) (c f : Side) := PatchField G (Joint c f)

variable (G)

def chartEquiv (c : Side) : Links G c ≃L[ℝ] fieldDir G c 1 := (fromColor G (Bonds c)).symm.trans
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => G.Color) (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv))

variable {G} {c : Side}

@[simp] lemma chartEquiv_apply (v : Links G c) (i : Site c) (j : Axis) :
    chartEquiv G c v (i, coord j) = paint G _ v (i,j) := by
  exact Equiv.piCongrLeft_apply_apply (fun _ : Body 1 c => G.Color)
    (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv) (paint G _ v) (i,j)

@[simp] lemma represent_chart (v : Links G c) : represent (chartEquiv G c v) = vary 1 v := by
  funext ⟨i,j⟩; simp [Work.F03.represent_link]
end YM.Push.Loops
