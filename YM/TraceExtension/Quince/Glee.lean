import YM.TraceExtension.Quince.Quart
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Opals
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Stores Precision
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Exterior Bloch Planned.AtomRegular JointLoad JointLoad.Heir
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Coat Brim Cub Extra.Iteration Extra.Iteration.Scales Malachite
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{L:Side}{a:ℝ}{f v:ℝ→ℝ}
abbrev bankP (G:Gauge)(L:Side) := Delay.fineMonitor G L
def coinP (G:Gauge)(L:Side)(x:ℝ):= Real.sqrt (bankP G L x)
lemma coinP_pos (G:Gauge)(L:Side)(x:ℝ):0<coinP G L x:=Real.sqrt_pos.mpr (Delay.monitor_pos ..)
def fRate (G:Gauge)(L:Side)(f:ℝ→ℝ):= Tendsto (fun x=> coinP G L x*f x) atTop (𝓝 0)
lemma rate_sum {I:Type} {w:I→ℝ→ℝ}(s:Finset I)(h:∀ i∈s,Rate G L a (w i)):Rate G L a (fun x=>∑ i∈s,w i x):=by
   induction s using Finset.induction with
   | empty=> simp only[Finset.sum_empty]; exact Rate.power.compare (Eventually.of_forall fun x=> by simp)
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact Rate.add (h i (Finset.mem_insert_self ..)) (ih fun i hi=>h _ (Finset.mem_insert_of_mem hi))
lemma costzero (h:Rate G L a f)(hx:a<0): Tendsto f atTop (𝓝 0):=Metric.tendsto_nhds.mpr fun e he=> (h.below hx (e/2) (half_pos he)).mono (fun x hx=>by rw [Real.dist_eq,sub_zero]; exact hx.trans_lt (half_lt_self he))
lemma coin_rate (G:Gauge)(L:Side): Rate G L 0 (coinP G L):=by unfold coinP; simp_rw [Real.sqrt_eq_rpow]; exact Rate.rpow_monitor _
lemma fGood (h:Rate G L a f)(hx:a<0): fRate G L f := costzero (by simpa only [zero_add] using (coin_rate G L).mul h) hx
lemma fRate.inn (h:fRate G L f)(hy:fRate G L v): fRate G L (fun x=> f x+v x):=by simp only [fRate,mul_add]; exact add_zero (0:ℝ) ▸ h.add hy
lemma fRate.reign (h:fRate G L f)(c:ℝ): fRate G L (fun x=> c*f x):=by unfold fRate; simp_rw [mul_left_comm _ c]; exact mul_zero c ▸ Tendsto.const_mul c h
lemma wire (G:Gauge)(L:Side): Tiny (bankP G L) (fun x=> (1+(radiusB x:ℝ))):= Tiny.cover (G.slopeConstant*Real.log (L.val:ℝ))
lemma swell (G:Gauge) (L:Side): Tendsto (bankP G L) atTop atTop:= Tiny.grow (G.slopeConstant*Real.log (L.val:ℝ))
lemma fum (h:Tiny (bankP G L) f): fRate G L (fun x=> f x/(bankP G L x)):=by
   unfold fRate; let g:=bankP G L; have hf:= h (1/4) (by norm_num)
   have hv:Tendsto (fun x=>(g x)^(-(1/4):ℝ)) atTop (𝓝 0):= by simp_rw [show ∀ x:ℝ,g x^(-(1/4):ℝ)=(g x ^ (1/4:ℝ))⁻¹ from fun x=>Real.rpow_neg (Delay.monitor_pos G L x|>.le) _]; exact tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (show (0:ℝ)<1/4 by norm_num)).comp (swell G L))
   refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv (hf.mono fun x hx=>mul_nonneg (coinP_pos ..|>.le) (div_nonneg hx.1 (Delay.monitor_pos ..|>.le))) ?_
   filter_upwards [hf] with x hx; have hP:= Delay.monitor_pos G L x; apply le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hx.2 hP.le) (coinP_pos _ _ _ |>.le))
   unfold coinP; rw[Real.sqrt_eq_rpow,← mul_div_assoc,← Real.rpow_add hP]; change (g x)^((1/2:ℝ)+1/4)/g x ≤ (g x)^(-(1/4):ℝ); rw[div_le_iff₀ hP]; change _ ≤ (g x)^(-(1/4):ℝ)*(g x); nth_rw 3 [← Real.rpow_one (g x)]; rw[← Real.rpow_add (show 0<g x from hP)]; norm_num
lemma hRate {p:ℕ}: Rate G L 0 (fun x=> (1+(Malachite.radiusD x:ℝ))^p):=by
    simpa only [zero_mul] using (((Rate.const 1).add (Brim.spanDO G L)).pow p)
def packing (L:Side)(x:ℝ):=(depthW L (Malachite.radiusD x)*2+1)^4
lemma stacking (G:Gauge)(L:Side): Tiny (bankP G L) (fun x=> (packing L x:ℝ)):=by
    let B:= bankP G L; have hp:=wire G L; have ht:=swell G L; let r:=fun x:ℝ=> ((radiusB x):ℝ); have hv:Tiny B r:=by
       intro ε he; filter_upwards [hp _ he] with x hx; exact ⟨by unfold r; positivity,(le_add_of_nonneg_left (by positivity : (0:ℝ)≤1)).trans hx.2⟩
    let l:=radiusD; have hx:Tiny B (fun x=> (l x:ℝ)):=by
       unfold l radiusD; push_cast
       exact ((hv.mul ((((Tiny.const ht 4 (by positivity)).mul hv ht).add (Tiny.const ht 2 (by positivity)) ht)) ht).add ((Tiny.const ht 2 (by positivity)).mul hv ht) ht)
    unfold packing depthW; simp_rw [show ∀ x:ℝ, ((((L.val*(Malachite.radiusD x+2)*2+1)^4:ℕ):ℝ))= ((L.val:ℝ)*(l x+ (2:ℝ))*2+1)^4 from fun x=>by unfold l; push_cast; rfl] ; apply Tiny.pow _ ht 4; exact ((((Tiny.const ht L.val (by positivity)).mul (hx.add (Tiny.const ht 2 (by positivity)) ht) ht).mul (Tiny.const ht 2 (by positivity)) ht).add (Tiny.const ht 1 (by positivity)) ht)
lemma stackingW (G:Gauge)(L:Side): Rate G L 0 (fun x=> (packing L x:ℝ)):=by
    have hp:=(Brim.spanDO G L); unfold packing depthW; simp_rw [show ∀ x:ℝ, ((((L.val*(Malachite.radiusD x+2)*2+1)^4:ℕ):ℝ))= ((L.val:ℝ)*(Malachite.radiusD x+ (2:ℝ))*2+1)^4 from fun x=>by push_cast; rfl]; simpa only [zero_mul] using ((((hp.add (Rate.const 2)).mul_left _).mul_right 2 |>.add (Rate.const 1)).pow 4)
end YM.PhysicalNext.Repeat.Quince
