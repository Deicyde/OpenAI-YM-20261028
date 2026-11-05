import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Jas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Lapses
import YM.Push.RELAY_DIFFERENCE.Dictionary
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lapis
open Filter Function Metric Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Gauge Matrix Finset Set Push Push.Uniform Bid
open ConnectedActivityE6 Blaze Brush Lantern Planned.JetPort WithLp
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (p : PathData G) {b : Clip} (O : ChartRatio G)
variable {n j : ℕ}
local notation "P" => Primary c G
local notation "K" => Precision.Key F G
local notation "X" => Positions P
local notation "Y" => Poll.Body K

variable {p} {σ C Λ D : ℝ}
def perch (p : PathData G) := Precision.loop p ∘ fine G F
def sumAt (x : Y) := ∑ i:F.Free, Real.log (O.J (tint G F.Free x.ofLp i))
def mist (p : PathData G) (x : X × Y) := perch F p (combineH (G:=G) F x) - sumAt F O x.2
lemma plume (p : PathData G) (x : X) (y : Y) :
    mist F O p (x,y) = Precision.loop p (lifting F (represent (tint G _ x)) (tint G F.Free y.ofLp))-sumAt F O y := rfl

def atomW (G : Gauge) (n : ℕ) (Z μ Λ D r : ℝ) := r*tollS D n (Λ*atomCost G Z μ n 2)
lemma pebbles (p : PathData G) (n : ℕ) (Z : ℝ) (he : PaintSupply G n Z) (hp : p.Bounds b σ C Λ)
    (x : Positions (Joint F G)) (hx : ‖x‖<1) (hD : 1 ≤ D) (ht : (Fintype.card (Joint F G):ℝ) ≤ D) (W : ℝ) (hW : (Fintype.card (Site f):ℝ) ≤ W) : Brush n (atomW G n Z σ Λ D W) 1 (perch F p) x := by
  let M s (i:Site f) y:= ∑' j, (p.loop j).unmasked (signedFine F y s) i
  let k:= entryWidth n S.patch.L σ; let V:=atomCost G Z σ n 2; let r:=tollS D n (Λ*V)
  replace hx:= mem_ball_zero_iff.mpr hx
  have hr : 0< k:= width_positive hp.width _ _
  have hΛ : 0 ≤ Λ:= hasInheritance hp
  have hv : 0 ≤ V:= atomCost_nn he hp.width 2
  have hc s i: Brush n r 1 (M s i) x := by
    -- use actual Beacon cost without root deterioration here
    refine Brush.offer.2 ⟨(label_analytic F _ hp.width hp.two s he _ _ hx).of_le le_top,fun j hj=>raises hD ht (mul_nonneg hΛ hv) hj (fun q => ?_)⟩
    have hh := (atom_beacon F s hp.width hp.two he x hx i) j hj q
    exact hh.trans (mul_le_of_le_one_right (mul_nonneg hΛ hv) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (Nat.cast_nonneg _))))
  let S' : ℝ := Fintype.card Signed; have hS : 0 < S':= by unfold S'; positivity
  have hx:= (Brush.spree (Finset.univ:Finset Signed) _ _ zero_le_one (fun s _=> Brush.spree Finset.univ _ _ zero_le_one (fun i _=> hc s i))).smul S'⁻¹
  simp only [sum_const,nsmul_eq_mul,card_univ, Real.norm_of_nonneg (inv_pos.mpr hS).le] at hx
  refine hx.climb ?_ le_rfl
  rw [show (Fintype.card Signed:ℝ)=S' from rfl,inv_mul_cancel_left₀ hS.ne']; exact mul_le_mul_of_nonneg_right hW (hc 1 0).nonneg

-- map constants. D projection beyond aux already paid; sumAt uses only small ∥ϱ‖.
def Hmap (G : Gauge) (i : F.Free) := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:F.Free=>G.Color) i) ∘L ((tint G F.Free).toContinuousLinearMap)
lemma carries (i:F.Free) (x:Y) : ‖tint G _ x.ofLp i‖ ≤ Uniform.shade G*‖weld K x‖ := le_trans (norm_le_pi_norm (tint G _ x.ofLp) _) (Uniform.tint_le x.ofLp)
lemma rights_map (i:F.Free) : ‖Hmap F G i‖ ≤ Uniform.shade G := ContinuousLinearMap.opNorm_le_bound _ (Uniform.shade_pos G).le fun x=> le_trans (norm_le_pi_norm (tint G F.Free x) i) (Uniform.tint_le x)

def taxR (k:ℕ) (p:ℝ) (G:Gauge) := p*(1+1*(Uniform.shade G))^k
lemma pen (p : PathData G) (n : ℕ) {Z M C' : ℝ} (he : PaintSupply G n Z) (hp : p.Bounds b σ C Λ) (hQ : FiberFee O n)
    (ha : 1 ≤ D) (hd : (Fintype.card (Joint F G):ℝ) ≤ D) (hm : (Fintype.card (Site f):ℝ) ≤ M) (hC : (Fintype.card F.Free:ℝ) ≤ C')
    (x : X × Y) (hx : ‖combineH (G:=G) F x‖ < 1) (hu : Uniform.shade G*‖weld K x.2‖ ≤ O.radius/2) :
    Brush n (atomW G n Z σ Λ D M+C'*taxR n hQ.cost G) 1 (mist F O p) x := by
  let L:= combineH (G:=G) F
  have hr:= Brush.reading L.toContinuousLinearMap (pebbles F p _ _ he hp (L x) hx ha hd _ hm) (feesComb ..)
  rw [one_mul] at hr
  apply hr.separating
  let f i (x:X×Y):= Real.log (O.J (tint G _ x.2.ofLp i))
  have he (i:F.Free) : Brush n (taxR n hQ.cost G) 1 (f i) x := by
    let g := (ContinuousLinearMap.snd ℝ X Y)
    have he := hQ.invoice _ (mem_closedBall_zero_iff.mpr ((carries F i x.2).trans hu))
    have hb : Brush n hQ.cost 1 (fun i=>Real.log (O.J i)) _ := Brush.offer.2 ⟨he.analytic.of_le le_top, he.norm_le⟩
    let t := (Hmap F G i) ∘L (weld K).toContinuousLinearMap ∘L g
    refine (Brush.trim (Brush.reading t hb (le_trans (ContinuousLinearMap.opNorm_comp_le ..) ?_)))
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) (rights_map F i)
    exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ..)).trans (Lapis.climb _))
  refine ((Brush.spree Finset.univ f (fun _=> taxR n hQ.cost G) zero_le_one (fun i _=> he i)).climb ?_ le_rfl); rw [sum_const,nsmul_eq_mul,card_univ]; exact mul_le_mul_of_nonneg_right hC (by unfold taxR; have := hQ.positive; have h:=Uniform.shade_pos G; positivity)
end YM.PhysicalNext.Repeat.Lapis
