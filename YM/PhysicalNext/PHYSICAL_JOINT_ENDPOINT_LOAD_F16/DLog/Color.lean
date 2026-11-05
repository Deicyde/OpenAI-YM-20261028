import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Exponent
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Deck
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.Precision


/-!
# Same slot charges -> Tickets for Fsct letters

Through *ordered*, including tests in the log-thickness with geometry
still fixed. Keep the direction cost even for terms not reading H/R link
variables. Stage surcharge from the complete cast log derivatives, NO
relabeling inputs through repainting in a rotated/changed gauge. Separate
radius growing with support shift for pricing under the same BudgetPoint
as the held kernel. Use through at the chosen BudgetPoint.power. This is
not a supBounds conclusion including E's analytically profiled short
parent valuations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Lattice RG Wilson Pressure Tree Matrix
open FreeResolvent FreeResolvent.TestD FreeResolvent.Affine FreeResolvent.Mark
open SelectedOrderedKernels AnalyticBridge AnalyticBridge.RelativeLogdet Physical Differential
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c : Side} {B : Directions G c} {V : Config G c} {bp : BudgetPoint}
  {k p : ℕ} {C δ : ℝ} {f : Config G c → ℝ} {o y : Site c}

def scales (G : Gauge) (p k : ℕ) (δ : ℝ) := 1+timeCost G p k (narrow k δ) 1
lemma scales_pos (G : Gauge) (p k : ℕ) (δ : ℝ) : 0 < scales G p k δ := add_pos_of_pos_of_nonneg zero_lt_one (timeCost_pos ..)

def arc (y o : Site c) (p : ℕ) := hill (native c) o p y
lemma arc_pos (y o : Site c) (p : ℕ) : 0 < arc y o p := hill_pos ..

/-- `marked` payments by rank, eventually for our explicit letter domains. -/
theorem publish (hB : ∀ i,‖B i‖ < SelectedOrderedKernels.radius G k) (hd : 0<δ) (hp : bp.power=p) (hc : 0≤C)
    (hF : ContDiffAt ℝ k (SelectedOrderedKernels.over f V) ((paint G c).symm B))
    (h : ∀ L : List (raw G c), L.length≤k → (marked G c δ).pay L y * |jet (ray G c) (SelectedOrderedKernels.over f V) L ((paint G c).symm B)|≤ C) :
    Ticket (bp.dirBound o) k (increment V B) (scales G p k δ*C) (arc y o p) f := by
  subst p
  let d := narrow k δ
  have hf : WardBin.Lies.Germ k f (increment V B) := germ_at_field hB hF
  refine ⟨hf,mul_nonneg (scales_pos ..).le hc, (arc_pos ..).le,fun L hL hx=> ?_⟩
  let j := L.length
  let M := offFee G j * C
  let P := bp.power
  have he : 0 < d/2 := half_pos (narrow_pos k hd)
  let N := normSeminorm ℝ ℝ
  have hP w : due (native c) Prod.fst d y w * N (ordered f (increment V B) (w:Pins G c j)) ≤ M :=
    offCenter_pay hB hF w N hL (narrow_nn k hd.le) (narrow_use hd.le hL) hc
      (fun p w => h (List.ofFn w) (List.length_ofFn.trans_le (p.length_le.trans hL)))
  let Y := torusPay (PAC G 1) (d/2)
  have hm : 0≤ M := mul_nonneg (offFee_nn ..) hc
  have hr t : admitted (native c) Prod.fst o P bp.threshold (L.get t) := hx (L.get t) (L.get_mem t)
  have ha := field_pay (M:=M) L.get N (hf.prod hL) hP hr he (le_of_eq (by ring)) bp.threshold_pos.le hm
    (volume c (PAC G 1) (d/2) he)
  have he' : fieldFee (d/2) bp.power bp.threshold Y j * M ≤ SelectedOrderedKernels.tender G j P (d/2) 1 M := tender_le (by linarith [bp.threshold_le]) he hm
  have ht := ha.trans he'
  rw [payment,List.ofFn_get,inv_mul_eq_div,div_le_iff₀ (pow_pos (hill_pos ..) _), show SelectedOrderedKernels.tender G j P (d/2) 1 M=SelectedOrderedKernels.tender G j P (d/2) 1 (offFee G j*1)*C by unfold SelectedOrderedKernels.tender M; ring] at ht
  refine ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc) (pow_nonneg (arc_pos ..).le _))
  exact (timeEnough G P k j d 1 hL).trans (le_add_of_nonneg_left zero_le_one)

end YM.PhysicalNext.EndpointLoadF16.DetLong
