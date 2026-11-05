import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Caverns
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Misty

/-!
# Golf at authentication. Includes insertions of higher calculus
 support after Loop caps. Consumption all near central radius on auxiliary.
 use same Vote on the field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lapis
open Filter Function Metric Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Gauge Matrix Finset Set Push Push.Uniform Bid
open ConnectedActivityE6 Blaze Brush Lantern Planned.JetPort WithLp
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (p : PathData G) {b : Clip} (O : ChartRatio G) (k : S.Choices)
variable {n j : ℕ} {P : Patch} {Q : KernelChoices} {x : Positions (Primary c G)}
variable (ρ : Dir G c→ AxisChart G F) {σ C Λ D M X u v c' r : ℝ}
    (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (E : FiberFee O ((n+3)+1)) (hg : Larger (G:=G) S)
    (hp : p.Bounds b σ C Λ) (hr : A.Service F b p ρ) (hO : LocalRatio O)
local notation "T" => A.tables b S.patch

variable (D' : ℝ) (ha : 0 ≤ D') (hu : 0 < u) (hv : 0 < v) (h₁ : u ≤ 1) (h₂ : v ≤ 1) (hx : u ≤ (A.tables b S.patch).horizon)
include hp hg hr k
set_option linter.unusedSectionVars false in
lemma evacuated (x: Positions (Primary c G)) (h : ‖x‖ < (T).horizon) :
    ‖(weld (Precision.Key F G)) (orbit F ρ x)‖ ≤ Before.Service.trailCost T (n+3)*‖x‖ := by
  have hs := (hr.trail_lipschitz hp hg rfl rfl).2 x (mem_ball_zero_iff.mpr h) 0 (mem_ball_self hr.x_pos)
  simp only [show Uniform.station ρ 0 = _ from (show Uniform.station (S:=S) ρ 0=0 by unfold Uniform.station; simp [hr.critical.1]),sub_zero] at hs; exact hs

def pam {s C : ℝ} (n : ℕ) (O : ChartRatio G) (b : Clip) (P : Patch) (A : Push.Uniform.Before G s C P.J Q (n+3)) (D D' : ℝ) (E : FiberFee O ((n+3)+1)) (Λ : ℝ) :=
    let T' := A.tables b P
    D*lensT n T' D + mineshaft n T' D + (atomW G (n+4) A.Z s Λ D D'+D'*taxR (n+4) E.cost G) + thickness T' n D

include E hO ha hu hv h₁ h₂ hx
lemma illuminates (he : 1 ≤ D) (hD : (Fintype.card (Joint F G):ℝ)≤D) (ht : (Fintype.card (Site f):ℝ) ≤ c') (ht' : (Fintype.card F.Free:ℝ) ≤ c')
    (hm : Before.Service.trailCost T (n+3)*u+v*D' < (T).initial)
    (hS : Before.Service.trailCost T (n+3)*u+v*D' < 1) (hK : Uniform.shade G*(Before.Service.trailCost T (n+3)*u+v*D') ≤ O.radius/2) :
    Golf (table F k p b) (mist F O p) (orbit F ρ) (gram F p b ρ k) n D' u v (pam n O b _ A D c' E Λ) := by
  let R:= Uniform.Before.Service.trailCost T (n+3); let C':=D*lensT n T D; let m:=mineshaft n T D; let q:=atomW G (n+4) A.Z σ Λ D c'+c'*taxR (n+4) E.cost G; let t:=thickness T n D; let K0 := pam n O b _ A D c' E Λ
  have hh: 0<(T).horizon:=hr.x_pos; have hs' : 0<R:= (hr.trail_lipschitz hp hg rfl rfl).1
  have hhi : (T).horizon < (T).initial := lt_of_le_of_lt (hr.2.1.trans hr.2.2.2.1) hr.2.2.2.2.1
  have he₁ x (hx : ‖x‖ < (T).horizon) : Brush (n+2) C' 1 (orbit F ρ) x:= luminous F k p b ρ σ C Λ A hg hp hr D he hD x (mem_ball_zero_iff.mpr hx)
  let L:= combineH (G:=G) F
  have hl x (hx : ‖L x‖ < (T).initial) : Brush (n+3) m 1 (table F k p b) x:= trench F k p b σ C Λ A hg hp D he hD x (mem_ball_zero_iff.mpr hx)
  let w:= weld (Precision.Key F G)
  have hu₁ (x:Positions (Primary c G) × Poll.Body (Precision.Key F G)) (hx : ‖L x‖<1) (h : Uniform.shade G*‖w x.2‖ ≤ O.radius/2) : Brush (n+4) q 1 (mist F O p) x:= pen F O p (n+4) A.labels hp E he hD ht ht' x hx h
  have hz : 0≤ q:= (hu₁ 0 (by rw [map_zero,norm_zero]; norm_num) (by change Uniform.shade G*‖w 0‖ ≤ _; rw [map_zero,norm_zero,mul_zero]; linarith [hO.patch])).nonneg
  have hp₁ x (hx:‖x‖ < (T).horizon) := patented F k p b ρ σ C Λ A hg hp hr D he hD x hx
  have h₀ : ‖(0:Positions (Primary c G))‖< (T).horizon:= by rwa [norm_zero]
  have hc:= (he₁ 0 h₀).nonneg; have hm': 0 ≤ m :=(hl 0 (by rw [map_zero,norm_zero]; linarith only [hh,hhi])).nonneg; have ht: 0 ≤ t := (hp₁ 0 h₀).nonneg
  change Golf _ _ _ _ n _ _ _ (C'+m+q+t)
  refine ⟨hu,hv,h₁,h₂,ha,fun x h=>(he₁ x (h.trans_le hx)).climb (by linarith only [hz,hc,hm',ht]) le_rfl,
    fun z l x hxl hi hv' hu'=>?_,fun x h z=> ⟨heart F k p b ρ σ C Λ A hg hp hr _ (h.trans_le hx) z,(wakes F k p b ρ σ C Λ A hg hp hr x (h.trans_le hx)).2.2.2 z⟩,
    fun x h=> ⟨(wakes F k p b ρ σ C Λ A hg hp hr _ (h.trans_le hx)).1,((hp₁ x (h.trans_le hx)).smaller n.le_succ).climb (by linarith only [hc,hm',hz,ht]) le_rfl⟩⟩
  let p':=visit (orbit F ρ) z l x
  have h : ‖L p'‖ = max ‖x.2‖ ‖w p'.2‖ := norm_meet x.2 (w p'.2)
  have hp' : ‖w p'.2‖ ≤ R*u+v*D' := by
    unfold p' visit; dsimp only; rw [map_add,map_smul,map_smul]
    refine (norm_add_le _ _).trans (add_le_add ((evacuated F p k ρ A hg hp hr _ (hu'.trans_le hx)).trans (mul_le_mul_of_nonneg_left hu'.le hs'.le)) ?_); rw [norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg hi.1]; exact hi.2)).trans
    rw [norm_smul]; apply mul_le_mul hv'.le _ (norm_nonneg _) hv.le
    exact (w.toContinuousLinearMap.le_opNorm z).trans ((mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb _)).trans hxl)
  exact ⟨((hl p' (by rw [h]; exact max_lt (lt_trans (hu'.trans_le hx) hhi) (hp'.trans_lt hm))).smaller (by omega)).climb (by linarith only [hz,hc,hm',ht]) le_rfl,
    ((hu₁ p' (by rw [h]; exact max_lt (hu'.trans_le h₁) (hp'.trans_lt hS)) ((mul_le_mul_of_nonneg_left hp' (Uniform.shade_pos G).le).trans hK)).smaller (by omega)).climb (by linarith only [hz,hc,hm',ht]) le_rfl⟩
end YM.PhysicalNext.Repeat.Lapis
