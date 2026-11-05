import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Jets
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Frame



/-!
# Entry-amplitude and radial order-cost for the joint endpoint invoice

To use the normalized coordinate prices of `SECTOR_AFFINE_JETS` in this
invoice (in particular at the cancellation `Aμ₀ + b`), convert by the true
log-chart partition formula at that link. Here need only *one scalar entry*
at a time but at ANY requested positions, and must preserve both the small
factor and uniformity in the periods. Buy through each part size and pay the
corresponding growth powers BEFORE using a Leibniz/product estimate. No tag or
geometry variation, and only derivatives of the chosen extension. Not prices
of mapped tables or a scalar/mean derivative service on other conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.SectorAffine
open FreeResolvent.TestD SelectedOrderedKernels
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Side} {V : Config G c} {F : Config G c → ℝ}
  {j k power : ℕ} {t M s : ℝ} {o i : Site c} {bp : BudgetPoint}

def grade (k : ℕ) (o i : Site c) : ℝ := (1+(separation i o:ℝ))^k
lemma grade_one (k : ℕ) (o i : Site c) : 1 ≤ grade k o i := one_le_pow₀ (by simp)
lemma grade_pos (k : ℕ) (o i : Site c) : 0 < grade k o i := zero_lt_one.trans_le (grade_one k o i)

structure Coupon (V : Config G c) (k power : ℕ) (t M : ℝ) (i : Site c) (F : Config G c → ℝ) : Prop where
  smooth : ContDiffAt ℝ k (F ∘ increment V) 0
  costs {j : ℕ} (o : Site c) (A : Fin j → Directions G c) : j ≤ k → Afford t power o (List.ofFn A) →
    ‖iteratedFDeriv ℝ j (F ∘ increment V) 0 A‖ ≤ M*(grade power o i)^j

def panelCost (G : Gauge) {j : ℕ} (p : OrderedFinpartition j) (b : Fin p.length) :=
  1+‖iteratedFDeriv ℝ (p.partSize b) (SelectedOrderedKernels.frame G j) 0‖
lemma panelCost_pos (G : Gauge) {j : ℕ} (p : OrderedFinpartition j) (b : Fin p.length) : 0 < panelCost G p b :=
  add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)

def partitionCost (G : Gauge) (j : ℕ) := ∑ p : OrderedFinpartition j, ∏ b, panelCost G p b
lemma partitionCost_nn (G : Gauge) (j : ℕ) : 0 ≤ partitionCost G j := Finset.sum_nonneg fun p _ =>
  Finset.prod_nonneg fun b _ => (panelCost_pos G p b).le

def lieCost (G : Gauge) (k : ℕ) : ℝ := ∑ j∈Finset.range (k+1), partitionCost G j
lemma lieCost_nn (G : Gauge) (k : ℕ) : 0 ≤ lieCost G k := Finset.sum_nonneg fun j _ => partitionCost_nn G j

private def normalized (p : OrderedFinpartition j) (A : Fin j → Directions G c) (b : Fin p.length) :=
  (panelCost G p b)⁻¹ • (term (fun _ => SelectedOrderedKernels.frame G j) p A b)

private lemma affords (A : Fin j → Directions G c) (p : OrderedFinpartition j)
    (h : ∀ m, bp.dirBound o (A m)) (hk : j ≤ k) (ht : bp.threshold = t) :
    Afford t (bp.power*k) o (List.ofFn (normalized p A)) := by
  have ht' : 0 < t := ht ▸ bp.threshold_pos
  unfold Afford; rw [List.forall_mem_ofFn_iff]
  intro b i
  let H : ℝ := 1+(separation i.1 o:ℝ)
  have hH : 1 ≤ H := by unfold H; simp
  have he := Finset.prod_le_prod (s:=Finset.univ) (g:=fun (_:Fin (p.partSize b)) => t*H^bp.power)
    (f:=fun r => ‖A (p.emb b r) i‖) (fun r _ => norm_nonneg _) (fun r _ => ht ▸ h _ i)
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,← pow_mul] at he
  have hv : t^(p.partSize b) ≤ t^1 := pow_le_pow_of_le_one ht'.le (ht ▸ bp.threshold_le) (p.partSize_pos b)
  rw [pow_one] at hv
  have hg := term_cost (fun _ => SelectedOrderedKernels.frame G j) p A b i
  change ‖(panelCost G p b)⁻¹ • term (fun _ => SelectedOrderedKernels.frame G j) p A b i‖ ≤ t * H^(bp.power*k)
  rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (panelCost_pos G p b)).le,inv_mul_eq_div,div_le_iff₀ (panelCost_pos G p b),mul_comm _ (panelCost G p b)]
  exact hg.trans (mul_le_mul (le_add_of_nonneg_left zero_le_one) (he.trans (mul_le_mul hv
    (pow_le_pow_right₀ hH (Nat.mul_le_mul_left _ (p.partSize_le b |>.trans hk))) (by positivity) ht'.le))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (panelCost_pos G p b).le)

lemma Coupon.ticket (h : Coupon V k (bp.power*k) t M i F) (o : Site c) (ht : bp.threshold=t) (hM : 0 ≤ M) :
    Ticket (bp.dirBound o) k V (lieCost G k*M) (grade (bp.power*k) o i) F := by
  let r := grade (bp.power*k) o i
  have hr : 1 ≤ r := grade_one ..
  refine ⟨h.smooth,mul_nonneg (lieCost_nn ..) hM,zero_le_one.trans hr, fun l hl he => ?_⟩
  let j := l.length; let A := l.get
  have hx : ∀ m,bp.dirBound o (A m) := fun m => he _ (List.get_mem ..)
  have hp (p : OrderedFinpartition j) : ‖iteratedFDeriv ℝ p.length (F ∘ increment V) 0
      (term (fun _ => SelectedOrderedKernels.frame G j) p A)‖ ≤ (∏ b,panelCost G p b)*(M*r^j) := by
    rw [show term (fun _ => SelectedOrderedKernels.frame G j) p A = fun b => panelCost G p b • normalized p A b from
      funext fun b => by simp only [normalized,smul_smul,mul_inv_cancel₀ (panelCost_pos G p b).ne',one_smul]]
    have hh : 0 ≤ ∏ b,panelCost G p b := Finset.prod_nonneg fun b _ => (panelCost_pos G p b).le
    rw [ContinuousMultilinearMap.map_smul_univ,norm_smul,Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left ((h.costs o (normalized p A) (p.length_le.trans hl) (affords A p hx hl ht)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr p.length_le) hM)) hh
  rw [← (show List.ofFn A=l from List.ofFn_get l),expand ((show WardBin.Lies.Germ k F V from h.smooth).prod hl),List.length_ofFn]
  apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun p _ => hp p)).trans ?_)
  rw [← Finset.sum_mul]
  change partitionCost G j * (M*r^j) ≤ lieCost G k * M * r^j
  rw [← mul_assoc]; gcongr
  exact Finset.single_le_sum (fun n _ => partitionCost_nn G n) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

section suppliers
variable {I : Type} [Fintype I] {p : I → Site c}
open AnalyticBridge.SectorAffine (Weighted)
open FreeResolvent (native)
open Wisps (rate)

omit [Fintype I] in
private lemma uncart (Q : Config G c → Matrix I I ℝ) : cart (Q ∘ field V) = Q ∘ increment V :=
  funext fun y => congr_arg Q (reader_field V y)

lemma matrixCoupon {Q : Config G c → Matrix I I ℝ} (h : Weighted p p (0:PriceCoords G c) k power s (fun _ => M) (Q ∘ field V))
    (i j : I) (ht : 0<t) (h1 : t ≤ 1) (hm : 0≤M) :
    Coupon V k power t (M*rate (-s) (separation (p i) (p j))) (p i) (fun v => Q v i j) := by
  have h0 : tape (0:PriceCoords G c) = 0 := gaugeCount.map_zero
  have hh := h.smooth; rw [uncart,h0] at hh
  refine ⟨(evaluate i j).contDiff.contDiffAt.comp (0:Directions G c) hh,?_⟩
  intro n o A hn hA
  let L := List.ofFn A
  have hL := List.length_ofFn (f:=A)
  let d := separation (p i) (p j)
  let r := grade power o (p i)
  have hr := grade_pos power o (p i)
  have he := (h.each o ht.le L (hL.trans_le hn) hA).row.entry i j
  rw [FreeResolvent.Mark.payment,uncart,h0, ← entry _ _ (smooth_of_le hh (hL.trans_le hn)), FreeResolvent.Stars.list_result] at he
  rw [show L.length=n from hL] at he
  change (r^n)⁻¹ * (rate s d * |iteratedFDeriv ℝ n ((fun v : Config G c => Q v i j) ∘ increment V) 0 (id ∘ A)|) ≤ M * t^n at he -- length L still
  rw [inv_mul_eq_div,div_le_iff₀ (pow_pos hr _)] at he
  have hi : t^n ≤ 1 := pow_le_one₀ ht.le h1
  have hx := mul_le_mul_of_nonneg_left hi hm
  rw [mul_one] at hx
  have he := he.trans (mul_le_mul_of_nonneg_right hx (pow_pos hr _).le)
  rw [← le_div_iff₀' (Wisps.rate_pos ..)] at he
  unfold Wisps.rate
  rw [neg_mul, Real.exp_neg,Real.norm_eq_abs]
  exact he.trans_eq (by unfold Wisps.rate d; ring)

lemma pointCoupon {H : Config G c → I → ℝ} (h : Offset.Stipulates power p k t M V H) (i : I) :
    Coupon V k power t M (p i) (fun v => H v i) := by
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => ℝ) i
  refine ⟨L.contDiff.contDiffAt.comp (0:Directions G c) h.1,?_⟩
  intro j o A hj hA
  have he := h.2 o (List.ofFn A) (List.length_ofFn.trans_le hj) hA i
  change ((grade power o (p i))^(List.ofFn A).length)⁻¹ * |_| ≤ M at he
  rw [inv_mul_eq_div,div_le_iff₀ (pow_pos (grade_pos power o (p i)) _),List.length_ofFn] at he
  change _ ≤ M * _
  convert! he using 1
  rw [show jet id (H ∘ increment V) (List.ofFn A) 0 i = _ from (jet_linear id (List.ofFn A) L (smooth_of_le h.1 (List.length_ofFn.trans_le hj))).symm,
    FreeResolvent.Stars.list_result, id_comp]; rfl
end suppliers
end YM.PhysicalNext.JointLoad
