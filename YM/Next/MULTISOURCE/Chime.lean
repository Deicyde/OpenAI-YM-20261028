import YM.Marker.Console
import YM.Next.MULTISOURCE.Germs

/-!
# Smoothing by the coarse-link noise on the actual vacuum block

Functional calculus in uniform norm for *one fixed* volume, including outside all field masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice Function Filter Finset MeasureTheory Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)

abbrev Tests (G : Gauge) (c : Side) := BoundedContinuousFunction (Config G c) ℝ

def pieceL (e : Edge (Site c)) : World G c →ₗ[ℝ] Tests G c where
  toFun V := BoundedContinuousFunction.mkOfCompact ⟨fun x => (V e*G.mat (x e)⁻¹).trace.re / G.repDim,by fun_prop⟩
  map_add' V U := by
    ext v; change ((V e+U e)*G.mat _).trace.re / _= _+_; rw [add_mul,Matrix.trace_add,Complex.add_re,add_div]; rfl
  map_smul' x V := by
    ext v; change ((x • V e)*G.mat _).trace.re / _= x *_
    rw [smul_mul_assoc,Matrix.trace_smul,Complex.smul_re]
    rw [smul_eq_mul,mul_div_assoc]; rfl

def single (V : World G c) (e : Edge (Site c)) : Tests G c :=
    (-β * S.kernel.penalty) • (1 - pieceL e V)
def curve (V : World G c) : Tests G c :=
    ∏ i : Edge (Site c), (S.penaltyZ β G)⁻¹ • (NormedSpace.exp (single S β V i))

lemma point (R : Tests G c) (q : Config G c) : (NormedSpace.exp R) q= Real.exp (R q) := by
  let F : Tests G c →+* ℝ := { toFun := fun x => x q, map_zero' := rfl, map_one' := rfl,
                                map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.map_exp F (BoundedContinuousFunction.evalCLM ℝ q).cont _
lemma sunny (x : World G c) (V : Config G c) : 0 < curve S β x V := by
  rw [curve,BoundedContinuousFunction.prod_apply]; apply prod_pos; intro i _
  change 0 < _ * (NormedSpace.exp (single S β x i)) V
  rw [point]; exact mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)
lemma costs (V : Config G c) (x : Config G c) : curve S β (showU V) x = S.noise β x V := by
  simp only [curve,StepData.noise, BoundedContinuousFunction.prod_apply]; apply prod_congr rfl; intro i _
  change _ * (NormedSpace.exp (single S β (showU V) i)) x = _
  rw [point]; unfold StepData.penaltyWeight Gauge.price; rw [G.mat_mul]; rfl
lemma coated : ContDiff ℝ ∞ (curve S (G:=G) β) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Tests G c → Tests G c) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic x).contDiffAt
  unfold curve; apply contDiff_prod; intro i _
  apply ContDiff.const_smul; apply ContDiff.comp (g:=NormedSpace.exp) (f:=fun x => single S β x i) he
  unfold single; exact ContDiff.const_smul _ (contDiff_const.sub ((pieceL (G:=G) i).toContinuousLinearMap.contDiff))
end YM.Multi.Step
