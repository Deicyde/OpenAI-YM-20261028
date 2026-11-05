import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Pricing
import YM.Next.SCHEDULE.Postal

/-!
# Arbitrary-output-field costs (clipping / selectors)

In particular can't bound both remote slots by θ just because a row
at one site is kept. Support for these corrections DO count where V
must be read for the decision. `literal` and all functions consuming it
keep the equality branch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Set MeasureTheory Filter Lattice RG PathData Wilson Next.Scheduling.Wages UVNext.PricedKernels Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical
variable {G : Gauge} {n : Side} (P : PathData G) (c : Clip) (b : BudgetPoint)

lemma select_sees (h : Selector c b) {U V : Config G n} (he : Agrees (halo (n:=n) b.B {0}) U V) :
    kept c b.threshold 0 U → kept c b.threshold 0 V := by
  intro H F; by_cases hx : b.B ≤ separation 0 F.1
  · exact outside_kept c b h F V hx
  have ht : touched F ⊆ halo b.B {0} := fun i hi => by
    have hh : i∈ringlet F.1 := local_square F hi
    have hv : separation F.1 i≤1 := by simpa [ringlet,halo_spec] using hh
    simp only [halo_spec, Finset.mem_singleton,exists_eq_left]; exact (separation_triangle _ F.1 i).trans (by omega)
  rw [← show faceValue U F=faceValue V F from travel_local _ _ _ _ fun e hx hy => he e (ht (List.mem_toFinset.mpr hx)) (ht (List.mem_toFinset.mpr hy))]; exact H F

lemma literal_local (h : Selector c b) (j : Sequence) : LocalOn (imageOf (n:=n) P b j) (literal (n:=n) P c b j) := by
  intro U V he; have hh := raw_local P c b j U V he
  rcases j with ⟨x,_ |⟨i,k⟩⟩
  · simp only [literal,Sum.elim_inl, link_price x U V he]
  have hv : Agrees (halo (n:=n) b.B {0}) U V := agrees_mono he (Finset.coe_subset.mpr (by
    change halo _ _ ⊆ _∪_∪_; exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left))
  have hu : kept c b.threshold 0 U↔kept c b.threshold 0 V := ⟨select_sees c b h hv,select_sees c b h fun i hi he => (hv i hi he).symm⟩
  simp only [literal, Sum.elim_inr, hu,hh]

lemma literal_symm (j : Sequence) : GaugeInvariant (literal (n:=n) P c b j) := by
  intro u U
  have hh : kept c b.threshold 0 (gauge u U)↔kept c b.threshold 0 U := by simp only [kept,face_gauge,G.chord_conj]
  have he:=raw_symm P c j u U
  rcases j with ⟨x,_|d⟩
  · simp only [literal,Sum.elim_inl,face_gauge,G.chord_conj]
  simp only [literal,Sum.elim_inr,hh,he]

lemma literal_meas (j : Sequence) : Measurable (literal (n:=n) P c b j) := by
  rcases j with ⟨x,_|d⟩
  · have hh : Measurable fun U : Config G n => G.chord (faceValue U (directWord x)) := by unfold faceValue; fun_prop
    refine measurable_const.mul ?_
    exact Measurable.ite (measurableSet_le hh measurable_const)
      ((measurable_const.mul (hh.pow_const (2:ℕ))).div_const _) (measurable_const.mul hh)
  exact Measurable.ite (kept_closed c _ _).measurableSet (raw_cont ..|>.measurable) measurable_const

private lemma slot_pays (s : Slot) {U : Config G n} (h : kept c b.threshold 0 U) :
    ‖s.atSite U 0‖ ≤ b.threshold * Real.exp (s.length/c.relaxation) := by
  rw [F03.atSite_path,G.norm_adjoint]; refine ((G.curvature_norm _).trans (h _)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ c.radius_pos.le)) b.threshold_pos.le
  exact_mod_cast E04.slot_separation (n:=n) s 0

def priceClip (j : Sequence) := j.2.elim
  (fun _ => weight*(c.direct/2+c.linear*2) * b.threshold)
  (fun d => |copper P j.1 d| * Real.exp (((first P j.1 d.1).length:ℝ)/c.relaxation + (first P j.1 d.2).length/c.relaxation)* b.threshold^2)

lemma clip_claim (j : Sequence) (U : Config G n) : ‖literal P c b j U‖ ≤ priceClip P c b j := by
  rcases j with ⟨x,_|d⟩
  · simp only [literal, priceClip,Sum.elim_inl,norm_mul,Real.norm_of_nonneg weight_pos.le,mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ weight_pos.le
    let r:= G.chord (faceValue U (directWord x)); have hr : 0≤r := G.chord_nonneg _
    have hx := b.threshold_pos; have hv := c.tail_pos; have hh:= c.quadratic_pos
    change ‖clipped c b.threshold r‖≤_
    unfold clipped; split
    next hu =>
      rw [Real.norm_of_nonneg (by positivity)]; refine le_trans (b:=c.direct * b.threshold^2/2) (by gcongr) ?_
      have ht : b.threshold^2 ≤ b.threshold := by simpa using pow_le_pow_of_le_one hx.le b.threshold_le (by decide : 1 ≤ 2)
      linarith only [mul_le_mul_of_nonneg_left ht hh.le, mul_pos hx hv]
    next =>
      rw [Real.norm_of_nonneg (by positivity)]
      apply le_trans (b:=c.linear*b.threshold*2) (mul_le_mul_of_nonneg_left (G.chord_le_two _) (by positivity))
      linarith only [mul_pos hx hh]
  simp only [literal,priceClip,Sum.elim_inr]; split
  next hu =>
    simp only [raw,Sum.elim_inr,Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ ≤ |copper P x d| * ((b.threshold*Real.exp ((first P x d.1).length/c.relaxation)) *
              (b.threshold* Real.exp ((first P x d.2).length/c.relaxation))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (slot_pays c b _ hu) (slot_pays c b _ hu) (norm_nonneg _)
          (by positivity [b.threshold_pos])) (abs_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  rw [norm_zero]; positivity
end YM.AnalyticBridge.CouplingShape
