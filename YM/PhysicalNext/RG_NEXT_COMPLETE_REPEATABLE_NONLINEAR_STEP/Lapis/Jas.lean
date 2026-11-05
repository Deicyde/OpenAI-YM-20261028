import YM.AnalyticNext.QUARTIC_MATCH.Range
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Peg
import YM.Planned.STATIONARY_JET_PORT.AtHome
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lapis
open Filter Function Metric Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Gauge Matrix Finset Set Push Push.Uniform Bid
open ConnectedActivityE6 Blaze Brush Lantern Planned.JetPort WithLp
open scoped Topology MatrixOrder ContDiff BigOperators Classical
section Linear
variable (κ : Type) [Fintype κ]
def weld : Poll.Body κ≃L[ℝ] Positions κ := (WithLp.linearEquiv 2 ℝ (κ → ℝ)).toContinuousLinearEquiv
lemma climb : ‖(weld κ).toContinuousLinearMap‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by
  rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro i; change ‖x i‖≤ _
  simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using! abs_real_inner_le_norm (EuclideanSpace.basisFun κ ℝ i) x
lemma transit1 {D : ℝ} (h : 1≤D) (hp : (Fintype.card κ:ℝ) ≤ D) : ‖(weld κ).symm.toContinuousLinearMap‖ ≤ D := by
  have ht:0<D:=zero_lt_one.trans_le h
  apply ContinuousLinearMap.opNorm_le_bound _ ht.le; intro v
  let w:= (weld κ).symm v
  have he i : w i=v i := rfl
  apply (sq_le_sq₀ (norm_nonneg _) (show 0≤ D*‖v‖ by positivity)).1
  rw [show (weld κ).symm.toContinuousLinearMap v=w from rfl, EuclideanSpace.real_norm_sq_eq,mul_pow]
  refine (Finset.sum_le_sum (f:=fun j=> w j^2) (g:=fun _=> ‖v‖^2) (fun i _ => ?_)).trans ?_
  · rw [← sq_abs,he]; exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) _
  simp only [sum_const,nsmul_eq_mul,card_univ]; exact mul_le_mul_of_nonneg_right (hp.trans (le_self_pow₀ h (by decide))) (sq_nonneg _)
end Linear
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (k : S.Choices) (p : PathData G) (b : Clip)
local notation "P" => Primary c G
local notation "K" => Precision.Key F G
local notation "X" => Positions P
local notation "Y" => Poll.Body K

def combineH : (X × Y) ≃L[ℝ] Positions (Joint F G) := ((ContinuousLinearEquiv.refl ℝ X).prodCongr (weld K)).trans (partSpace P K).symm
lemma feesComb : ‖(combineH (G:=G) F).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; change ‖meetVar i.1 _‖≤_; rw [norm_meet,one_mul]; exact max_le_max le_rfl (le_trans ((weld K).toContinuousLinearMap.le_opNorm _) ((mul_le_of_le_one_left (norm_nonneg _) (climb (Precision.Key F G)))))

def table (k : S.Choices) (p : PathData G) (b : Clip) := Uniform.priced F k b p ∘ combineH (G:=G) F
variable (ρ : Dir G c→AxisChart G F)
def orbit (ρ : Dir G c → AxisChart G F) := (weld K).symm ∘ Uniform.station (S:=S) ρ
abbrev glow (k : S.Choices) := hessian F k b p
abbrev gram (k : S.Choices) (x : X) := glow F p b k (tint G _ x) (ρ (tint G _ x))


lemma power (x : X) (y z : Y) (he : ContDiffAt ℝ ω (Uniform.priced F k b p) (meetVar x y.ofLp)) :
    dotProduct z.ofLp (glow F p b k (tint G _ x) (tint G _ y.ofLp) *ᵥ z.ofLp)=scratch (0,z) (table F k p b) (x,y) := by
  let g:=Uniform.priced F k b p; let A:= meetVar x y.ofLp
  -- explicit cost via Basis proof
  have hs : scratch (0,z) (table F k p b) (x,y)= iteratedFDeriv ℝ 2 (table F k p b) (x,y) ![(0,z),(0,z)] := by simp only [iteratedFDeriv_two_apply,scratch]; rfl
  have ht : (combineH (G:=G) F) (x,y)= A:= rfl
  let L:=(combineH (G:=G) F).toContinuousLinearMap
  let d:Positions K→L[ℝ] Positions (Joint F G):=lowerCol
  let v:= z.ofLp
  have hp : iteratedFDeriv ℝ 2 (table F k p b) (x,y)=((iteratedFDeriv ℝ 2 g A).compContinuousLinearMap (fun _=> L)) := linear_pull (k:=2) L (he.of_le (by simp))
  have hw := block_congr F k he; change block g A = glow F p b k (tint G _ x) (tint G _ y.ofLp) at hw
  rw [hs,hp,← hw]; let T:= block g A
  let U:= fderiv ℝ (fderiv ℝ g) A
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]
  change dotProduct v (T *ᵥ v)= U (d v) (d v)
  have hb (v: Positions K) : d v=∑ i:K, v i • bolt ((Sum.inr i):Joint F G):= by
    have hh:= @lower_bolt P K
    conv_lhs => arg 2; rw [← Uniform.combine v]
    simp only [map_sum,map_smul,d,lower_bolt] -- ambiguous
  rw [hb]; simp only [map_sum,_root_.sum_apply,map_smul,_root_.smul_apply]
  have hz (i j : K) : U (bolt ((Sum.inr j):Joint F G)) (bolt ((Sum.inr i):Joint F G))=T i j:= by dsimp only [T,block,of_apply,entry,U]; rw [iteratedFDeriv_two_apply]; rfl
  simp_rw [hz]; unfold dotProduct Matrix.mulVec; simp_rw [dotProduct,smul_eq_mul,mul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> by have ht : T j i=T i j:= (by simpa using congr_fun (congr_fun (block_hermitian (f:=g) he) i) j); rw [ht]; ring
end YM.PhysicalNext.Repeat.Lapis
