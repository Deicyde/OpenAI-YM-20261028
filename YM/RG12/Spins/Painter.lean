import YM.RG12.Spins.Centroid
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Canvas
/-! launching prices for the unscaled calorimeter. Work with lists,
 not commuting. Keep the full P.threshold^j power from Canvas. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice Wilson RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies
open Pressure PhysicalNext.JointLoad.Heir Next Next.SectorChange
open Finset Planned.AtomRegular
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{t:ℝ}{p n:ℕ}{P:BudgetPoint}{c f:Side}{o: Site c}{A:ℝ}
noncomputable def instill (G:Gauge)(c f:Side)(o:Site c)(n:ℕ)(j:ℕ)(v:Slab G c j)(z:Panels j): Deck G c f:=(PhysicalNext.JointLoad.Heir.launch 1 o n 1 v z,0)
lemma floor_rate (h:Canvas P o n (1:Config G c) 1 p A)(he:1≤A){j:ℕ}(v:Slab G c j)(hv:∀ i,P.dirBound o (v i))(hj:j≤p):
    instill G c f o n j v 0=0 ∧ ContDiffAt ℝ j (instill G c f o n j v) 0 ∧ ∀ k:ℕ,1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k (instill G c f o n j v) 0‖ ≤ A*((1+n:ℝ)^(P.power*p))*P.threshold^k :=by
    let Y:= PhysicalNext.JointLoad.Heir.launch (1:Config G c) o n 1 v
    have hT:=(h.ready v).of_le (m:=(j:ℕ∞ω)) (Nat.cast_le.mpr hj)
    refine ⟨Prod.ext (by change Y 0=_; unfold Y; rw [launch_zero, PhysicalNext.Repeat.Cub.blankBirth]; rfl) rfl,hT.prodMk contDiffAt_const,fun k hk hkv=> ?_⟩
    unfold instill; rw [iteratedFDeriv_prodMk hT contDiffAt_const (Nat.cast_le.mpr hkv)]
    have hQ:=P.threshold_pos
    refine op_le_of_unit (by positivity) (fun u hu=>?_)
    change ‖((iteratedFDeriv ℝ k Y 0 u),(iteratedFDeriv ℝ k (fun _:Panels j=>(0:Directions G f)) 0 u))‖ ≤ _
    refine max_le ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=> ?_) ?_
    swap; · rw [iteratedFDeriv_const_of_ne (by omega)]; change ‖(0:Directions G f)‖ ≤ _; rw [norm_zero]; positivity
    let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bond c=>G.Color) i
    change ‖iteratedFDeriv ℝ k Y 0 u i‖ ≤ _
    rw [show iteratedFDeriv ℝ k Y 0 u i = iteratedFDeriv ℝ k (fun t=>Y t i) 0 u from (by rw [show iteratedFDeriv ℝ k (fun t=>Y t i) 0 u= _ from congrArg (fun T=> (T:Panels j [×k]→L[ℝ] G.Color) u) (L.iteratedFDeriv_comp_left hT (Nat.cast_le.mpr hkv))];rfl)] -- stub
    have hS:= h.derivatives v o hj hv k hk (hkv.trans hj) i
    apply le_trans (ContinuousMultilinearMap.le_opNorm ..); apply (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _ => hu _))).trans hS |>.trans; split; swap; · positivity
    next H => rw [mul_pow,pow_mul]; have he := (pow_le_pow_left₀ (show 0≤1+(separation o i.1:ℝ) from by positivity) (add_le_add_right (Nat.cast_le.mpr H) _) P.power); unfold spine; rw [← separation_comm]; rw [mul_comm (P.threshold^k),← mul_assoc]; gcongr; first | simp | exact_mod_cast H | linarith | exact (pow_le_pow_left₀ (by positivity) he k).trans (pow_le_pow_right₀ (one_le_pow₀ (by simp)) (hkv.trans hj))
end YM.RG12.Spins
