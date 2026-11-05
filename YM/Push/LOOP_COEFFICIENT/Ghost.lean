import YM.Push.LOOP_COEFFICIENT.Joint

/-!
# Finite physical gauge completion

Unrestricted left increments. The relative Hessian `baseVector` is *not*
assumed to obey the on-shell law off-shell. We define the matrices of  explicitly (rooted coordinates); depth 9 rather than 3 in the allowed
range, for the subsequent summability with differentiated regulators. In
particular `mapDrift` is NOT set to zero. It will require its own Ward test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Set Filter Function Lattice RG Precision Exterior Wilson
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {c f n : Side} {G : Gauge} {S : StepData c f}

abbrev SiteKey (G : Gauge) (n : Side) := Point G (Site n)
abbrev BondKey (G : Gauge) (n : Side) := Point G (Bonds n)
abbrev JointKey (G : Gauge) (c f : Side) := Point G (Joint c f)

/-- Actual gauge tangent (rooted joint fields or just fine part). -/
def brace (U : Config G f) : Nodes G f →ₗ[ℝ] Loops.Links G f :=
  (paint G _).symm.toLinearMap.comp <| (LinearMap.pi fun i =>
    LinearMap.proj i.1 - (G.adjoint (U i)).comp (LinearMap.proj (R:=ℝ) (φ:=fun _ => G.Color) (i.1+step i.2))).comp (paint G _).toLinearMap

@[simp] lemma paint_brace (U : Config G f) (a : Nodes G f) (i : Bonds f) : paint G _ (brace U a) i =
    paint G _ a i.1 - G.adjoint (U i) (paint G _ a (i.1+step i.2)) := by
  unfold brace; rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]; rfl

def braceJoint (S : StepData c f) (U : Loops.Inputs G c f) : Nodes G f →ₗ[ℝ] Loops.Dual G c f :=
  (paint G _).symm.toLinearMap.comp <| LinearMap.pi fun i => Sum.elim
    (fun i : Bonds f => (LinearMap.proj i).comp <| (paint G _).toLinearMap.comp (brace (positions U)))
    (fun i : Site c => -((G.adjoint (auxiliaries U i)).comp <|
      (LinearMap.proj (S.ratio.embed i)).comp (paint G _).toLinearMap)) i

def R_g (U : Config G n) : Matrix (BondKey G n) (SiteKey G n) ℝ := LinearMap.toMatrix' (brace U)

def R_tot (S : StepData c f) (U : Loops.Inputs G c f) : Matrix (JointKey G c f) (SiteKey G f) ℝ :=
  LinearMap.toMatrix' (braceJoint S U)

@[simp] lemma paint_braceJoint_left (U : Loops.Inputs G c f) (a : Nodes G f) (i : Bonds f) :
    paint G _ (braceJoint S U a) (.inl i) = paint G _ (brace (positions U) a) i := by
  unfold braceJoint; rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply]; rfl
@[simp] lemma paint_braceJoint_right (U : Loops.Inputs G c f) (a : Nodes G f) (i : Site c) :
    paint G _ (braceJoint S U a) (.inr i) = -G.adjoint (auxiliaries U i) (paint G _ a (S.ratio.embed i)) := by
  unfold braceJoint; rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply]; rfl

lemma mat_vary_rate {m : Type} (U : PatchField G m) (a : Array G m) (i : m) : HasDerivAt
    (fun t : ℝ => G.mat (vary U (t • a) i)) (G.colorMat (paint G m a i) * G.mat (U i)) 0 := by
  let v := paint G m a i
  have he : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v))) (G.colorMat v) 0 :=
    (side _ G.expDiff_zero.differentiableAt v).congr_deriv (DFunLike.congr_fun G.expDiff_zero.fderiv v)
  simpa only [vary,bump,G.mat_mul,map_smul,Pi.smul_apply] using! he.mul_const (G.mat (U i))

lemma gaugeJoint_rate (U : Loops.Inputs G c f) (a : Nodes G f) : HasDerivAt
    (fun t : ℝ => displacement U (gaugeJoint S (vary 1 (t • a)) 1 U)) (braceJoint S U a) 0 := by
  let A (t : ℝ) := gaugeJoint S (vary 1 (t • a)) 1 U
  have ha : A (0:ℝ) = U := by simp [A]
  have he (x : Site f) : HasDerivAt (fun t : ℝ => G.mat (vary 1 (t • a) x)) (G.colorMat (paint G _ a x)) 0 := by
    simpa only [Pi.one_apply,G.mat_one,mul_one] using! mat_vary_rate 1 a x
  have hr (i) : HasDerivAt (fun t : ℝ => G.mat (A t i)) (G.colorMat (paint G _ (braceJoint S U a) i) * G.mat (U i)) 0 := by
    cases i with
    | inl e =>
      let x := e.1
      let y := e.1+step e.2
      let Z := U (.inl e)
      change HasDerivAt (fun t : ℝ => G.mat (vary _ (t • a) x * Z * (vary 1 (t • a) y)⁻¹)) _ _
      simp only [G.mat_mul, G.mat_inv]
      rw [paint_braceJoint_left,paint_brace,map_sub,G.mat_adjoint, Gauge.conjugate, sub_mul,
        positions, Function.comp_apply, Matrix.mul_assoc _ (star _), G.mat_star_mul,mul_one]
      simpa only [Pi.mul_apply,zero_smul,vary_zero,Pi.one_apply,G.mat_one,one_mul, mul_one,star_one,
        G.colorMat_skew,mul_neg,← sub_eq_add_neg] using! ((he x).mul_const (G.mat Z)).mul (he y).star
    | inr i =>
      change HasDerivAt (fun t : ℝ => G.mat ((1:G.El)*U _ * (vary 1 (t • a) (S.ratio.embed i))⁻¹)) _ _
      simp only [one_mul,G.mat_mul,G.mat_inv]
      rw [paint_braceJoint_right,map_neg, G.mat_adjoint,Gauge.conjugate,neg_mul,
        auxiliaries, Function.comp_apply, Matrix.mul_assoc _ (star _), G.mat_star_mul,mul_one]
      simpa only [G.colorMat_skew,mul_neg] using! ((he (S.ratio.embed i)).star.const_mul (G.mat (U (.inr i))))
  have hd (i) : HasDerivAt (fun t : ℝ => delta (U i) (A t i)) (paint G _ (braceJoint S U a) i) 0 := by
    have he := delta_rate (v:=fun t => A t i) (t:=0) (by rw [ha]; exact hr i)
    simpa only [ha] using! he
  convert! (fromColor G (Joint c f)).hasFDerivAt.comp_hasDerivAt (l:=fromColor G _) (0:ℝ)
    (hasDerivAt_pi.mpr hd) using 1

lemma joint_generator (U : Loops.Inputs G c f) :
    linearAt (fun v => displacement U (gaugeJoint S (vary 1 v) 1 U)) 0 = R_tot S U := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have ha := gaugeJoint_diff (S:=S) (matDiffAt_const U) (matDiffAt_const 1) (vary_diff (x:=0) (U:= (1 : NodeField G f)))
  have hd := (matDiffAt_const U).displacement ha (by simp)
  rw [linearAt_mulVec,R_tot,LinearMap.toMatrix'_mulVec]
  exact (side _ (hd.differentiableAt (by simp)) v).unique (gaugeJoint_rate U v)

def X₀ (t : S.Choices) (U : Loops.Inputs G c f) := rate (fun V => (Psi t V)⁻¹) U

lemma X₀_brace (h : S.patch.Branches S.kernel G) (t : S.Choices) (U : Loops.Inputs G c f)
    (hu : MatDiffAt (Psi t ∘ vary U) 0) : X₀ t U * R_tot S U = 1 := by
  let A := fun v => gaugeJoint S (vary 1 v) 1 U
  let T := fun v => displacement U (A v)
  let P := localize (fun V => (Psi t V)⁻¹) U
  have ha : MatDiffAt A 0 := gaugeJoint_diff (S:=S) (matDiffAt_const U) (matDiffAt_const 1) vary_diff
  have he : A 0 = U := by simp [A]
  have hd := (matDiffAt_const U).displacement ha he
  have hz : T 0 = 0 := by simp [T,he]
  have hp : ContDiffAt ℝ ω P (T 0) := by rw [hz]; exact localize_diff (fun i => mat_inv_diff (hu i))
  have hC := ha.continuousAt.tendsto; rw [he] at hC
  have he : P ∘ T =ᶠ[𝓝 0] id := by
    filter_upwards [hC.eventually (vary_displacement U),displacement_vary ((Psi t U)⁻¹)] with v hv hh
    dsimp only [Function.comp_apply,T,P,localize,id]
    rw [hv, ← hh]
    conv_lhs => rw [hh]

    congr 1
    ext1 i
    change (Psi t (gaugeJoint S (vary 1 _) 1 U) i)⁻¹ = _
    rw [Psi_gauge h,Pi.one_apply,one_mul]; simp [vary,bump]
  rw [← joint_generator, X₀,rate,linearAt,linearAt,← LinearMap.toMatrix'_comp]
  apply Matrix.toLin'.injective; rw [Matrix.toLin'_toMatrix', Matrix.toLin'_one]; apply LinearMap.ext; intro v
  have hf := fderiv_comp 0 (hp.differentiableAt (by simp)) (show DifferentiableAt ℝ T 0 from hd.differentiableAt (by simp))
  rw [he.fderiv_eq,fderiv_id,hz] at hf
  exact (DFunLike.congr_fun hf v).symm

def projectFine (G : Gauge) (c f : Side) : Matrix (BondKey G f) (JointKey G c f) ℝ :=
  LinearMap.toMatrix' (LinearMap.pi fun i => LinearMap.proj (Sum.inl i.1,i.2))

lemma projectFine_R (U : Loops.Inputs G c f) : projectFine G c f * R_tot S U = R_g (positions U) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v; rw [← Matrix.mulVec_mulVec, R_tot, R_g,projectFine,LinearMap.toMatrix'_mulVec,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]; ext1 ⟨i,k⟩
  exact congr_arg (fun y : G.Color => y k) (paint_braceJoint_left (S:=S) U v i)

/-- positive scalar mass retained in gauge as well as harmonic inverse. -/
def ghost (μ : ℝ) (U : Config G f) := (R_g U).transpose * R_g U + (μ^2) • (1 : Matrix _ _ ℝ)

def dressing (μ : ℝ) (U : Config G f) := (μ^2) • (ghost μ U)⁻¹

def depth : ℕ := 9

def tail {n : Type} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ) (j : ℕ) := ∑ i ∈ Finset.range (j+1), T^i

def regulation (μ : ℝ) (U : Config G f) := tail (dressing μ U) depth

def mu (S : StepData c f) : ℝ := (S.patch.L.val:ℝ)⁻¹

lemma mu_pos : 0 < mu S := inv_pos.mpr (Nat.cast_pos.mpr S.patch.L.pos)

/-- The map before forming the gauge square. -/
def completion (t : S.Choices) (U : Loops.Inputs G c f) :=
  regulation (mu S) (positions U) * (R_g (positions U)).transpose * projectFine G c f +
      (mu S)^2 • (dressing (mu S) (positions U)^depth * X₀ t U)

lemma ghost_pos (U : Config G f) (μ : ℝ) (hμ : 0<μ) : (ghost μ U).PosDef :=
  Matrix.PosDef.posSemidef_add (posSemidef_conjTranspose_mul_self _) (PosDef.one.smul (sq_pos_of_pos hμ))

private lemma tail_aux {n : Type} [Fintype n] [DecidableEq n] (T Q : Matrix n n ℝ) (a : ℝ) (j : ℕ)
    (h : T * Q = a • 1) : tail T j * (Q - a • 1) + a • T^j = Q := by
  induction j with
  | zero => simp [tail]
  | succ j ih =>
    simp only [tail, Finset.sum_range_succ (n:=j+1)] at *
    rw [Matrix.add_mul, Matrix.mul_sub (T^_), pow_succ, Matrix.mul_assoc _ T Q, h]
    simpa [Matrix.mul_smul,add_assoc] using ih

lemma completion_brace (h : S.patch.Branches S.kernel G) (t : S.Choices) (U : Loops.Inputs G c f)
    (hu : MatDiffAt (Psi t ∘ vary U) 0) : completion t U * R_tot S U = ghost (mu S) (positions U) := by
  rw [completion,Matrix.add_mul, Matrix.mul_assoc]
  rw [ projectFine_R,
    Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, X₀_brace h t U hu, Matrix.mul_one]
  let Q := ghost (mu S) (positions U)
  let T := dressing (mu S) (positions U)
  have hh := (ghost_pos (positions U) (mu S) mu_pos).isUnit
  have he : T * Q = (mu S)^2 • 1 := (Matrix.smul_mul ..).trans (by rw [Q.nonsing_inv_mul (Q.isUnit_iff_isUnit_det.mp hh)])
  simpa [Q,ghost,T,Matrix.mul_assoc,regulation] using tail_aux T Q ((mu S)^2) depth he
end YM.Push.Loops
