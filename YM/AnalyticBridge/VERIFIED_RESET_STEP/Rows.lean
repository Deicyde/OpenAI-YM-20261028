import YM.AnalyticBridge.VERIFIED_RESET_STEP.Residual
import YM.Extra.ITERATION_NO_LOSS.TermNorm
import YM.Extra.WILSON_STARTUP.Ownership
import YM.Next.SCHEDULE.Circuit
import YM.Next.SCHEDULE.Postal




/-! Uncut quadratic presentation: one plaquette and all (i,j) path
labels of *this* real row, not a new square completion. Chosen hard
indicator for the early alpha term includes the kept-test aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux UVNext.PricedKernels Next.Scheduling Work.F03 WilsonStartup
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side} {p : BudgetPoint}

abbrev Duo := Unit ⊕ (ℕ × ℕ)
abbrev Low := PlaqAxes × Duo
namespace Low
variable (R : PathData G) (c : Clip) (d : Low)

def left (j : ℕ × ℕ) := (R.row d.1 j.1).2
def right (j : ℕ × ℕ) := (R.row d.1 j.2).2
def length := d.2.elim (fun _ => 0) (fun j => (d.left R j).length + (d.right R j).length)
def mark := d.2.elim (fun _ => c.direct) (fun j => (R.row d.1 j.1).1*(R.row d.1 j.2).1)

def plain (o : Site n) : Pot G n := fun U => d.2.elim (fun _ => G.price (faceValue U (o,d.1)))
    (fun j => inner ℝ ((d.left R j).atSite U o) ((d.right R j).atSite U o) / 2)
def analogue (w : Flux G) := d.2.elim (fun _ => inner ℝ (w d.1) (w d.1)/2)
    (fun j => inner ℝ (w (d.left R j).plaq) (w (d.right R j).plaq)/2)
def proxy (o : Site n) : Pot G n := fun U => d.analogue R (petals U o)
def live (p : BudgetPoint) (o : Site n) (U : Config G n) := d.2.elim (fun _ => PathData.clipped c p.threshold (G.chord (faceValue U (o,d.1))))
    fun _ => if PathData.kept c p.threshold o U then d.mark R c * d.plain R o U else 0

def home (p : BudgetPoint) (o : Site n) := d.2.elim (fun _ => halo p.B {o})
    fun j => (halo p.B {o} ∪ Wages.walkCuts (d.left R j) o) ∪ Wages.walkCuts (d.right R j) o
lemma halo_home (p : BudgetPoint) (o : Site n) : halo p.B {o} ⊆ d.home R p o := by
  cases e : d.2 <;> simp only [home,e,Sum.elim_inl,Sum.elim_inr]
  · exact Finset.Subset.refl _
  exact fun i h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
lemma walk_home (p : BudgetPoint) (o : Site n) {j} (hj : d.2 = .inr j) :
    Wages.walkCuts (d.left R j) o ⊆ d.home R p o ∧ Wages.walkCuts (d.right R j) o ⊆ d.home R p o := by
  rw [home,hj]; exact ⟨fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h),Finset.subset_union_right⟩
lemma small_home (p : BudgetPoint) (o : Site n) : o ∈ d.home R p o := d.halo_home R p o (halo_subset p.B {o} (Finset.mem_singleton_self _))
lemma clover_home {p : BudgetPoint} (hB : 2 ≤ p.B) (o : Site n) : halo 2 {o} ⊆ d.home R p o :=
  (Corona.halo_mono hB (Finset.Subset.refl _)).trans (d.halo_home R p o)
lemma face_home {p : BudgetPoint} (hB : 2 ≤ p.B) (o : Site n) : touched (o,d.1) ⊆ d.home R p o :=
  fun _ h => d.clover_home R hB o (halo_spec.mpr ⟨_,Finset.mem_singleton_self _, (separation_comm o _).trans_le (visit_near _ h)⟩)
end Low

open RG.PathData Next.Scheduling

lemma slot_reads (s : Slot) (o : Site n) : LocalOn (Wages.walkCuts s o) (fun U : Config G n => s.atSite U o) := fun U V h =>
    s.covered.expandAt _ _ o U V (agrees_mono h (by rintro _ ⟨i,hi,rfl⟩; exact Finset.mem_image_of_mem _ hi))
lemma root_in (s : Slot) (o : Site n) : o ∈ Wages.walkCuts s o :=
    Finset.mem_image.mpr ⟨0,Finset.mem_union_left _ (List.mem_toFinset.mpr (by cases s.walk <;> simp [visits])),by simp⟩
lemma offset_inside (s : Slot) (o : Site n) : (slotFace s o).1 ∈ Wages.walkCuts s o :=
    Finset.mem_image.mpr ⟨_,Finset.mem_union_right _ (List.mem_toFinset.mpr (by simp [square, visits])),rfl⟩
lemma slot_length (s : Slot) (o : Site n) {y : Site n} (hy : y ∈ Wages.walkCuts s o) : separation y o ≤ s.length := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
  rw [separation,add_sub_cancel_right]; apply Finset.sup_le; intro i _
  apply (Corona.lap ..).trans (le_trans (Finset.single_le_sum (f:=fun i => (z i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    (Extra.Iteration.Derivs.stencil_length s z hz))
lemma kept_gauge (c : Clip) (t : ℝ) (k : Site n → G.El) (o : Site n) (U : Config G n) :
    kept c t o (Lattice.gauge k U) ↔ kept c t o U := by simp only [kept, face_gauge,G.chord_conj]
lemma kept_local (c : Clip) {p : BudgetPoint} (h : Decent c p) (o : Site n) {U V : Config G n} (he : Agrees (halo p.B {o}) U V) :
    kept c p.threshold o U ↔ kept c p.threshold o V := by
  refine forall_congr' fun q => ?_
  by_cases hx : p.B-2 ≤ separation o q.1
  · exact iff_of_true (too_far c p h _ _ o hx) (too_far c p h _ _ o hx)
  rw [show faceValue U q = faceValue V q from face_local q U V (agrees_mono he ?_)]
  intro z hz; apply (halo_spec (y:=z)).mpr ⟨o,Finset.mem_singleton_self _,?_⟩
  apply (separation_triangle o q.1 z).trans
  have hl := visit_near q (show z∈touched q from hz); rw [separation_comm] at hl; omega

lemma kept_small_halo {c : Clip} (h : Decent c p) {o : Site n} {U : Config G n} (hh : Healthy p.threshold (halo p.B {o}) U) :
    kept c p.threshold o U := by
  intro q
  by_cases hx : separation o q.1 ≤ p.B
  · have ht := Finset.disjoint_left.mp hh (halo_spec.mpr ⟨o,Finset.mem_singleton_self _,hx⟩)
    have he : G.chord (faceValue U q) ≤ p.threshold := le_of_not_gt fun H => ht ((flags_spec ..).mpr ⟨q,anchor_visit q,H⟩)
    exact he.trans (le_mul_of_one_le_right p.threshold_pos.le (Real.one_le_exp (div_nonneg (by positivity) c.radius_pos.le)))
  exact too_far _ _ h _ _ o (by omega)
lemma kept_slot {c : Clip} {o : Site n} {U : Config G n} (s : Slot) (hh : kept c p.threshold o U) :
    ‖s.atSite U o‖ ≤ p.threshold * Real.exp (s.length/c.relaxation) := by
  rw [atSite_path,G.norm_adjoint]; have := c.radius_pos; have := p.threshold_pos
  apply ((G.curvature_norm _).trans (hh _)).trans; gcongr
  exact_mod_cast (separation_comm _ _).trans_le (slot_length s o (offset_inside s o))

namespace Low
variable (R : PathData G) (c : Clip) (d : Low)
lemma plain_cont (o : Site n) : Continuous (plain R d o) := by
  unfold plain; cases e : d.2 <;> simp only [Sum.elim_inl,Sum.elim_inr]
  · unfold faceValue; fun_prop
  unfold Slot.atSite expandAt; fun_prop
lemma plain_local (p : BudgetPoint) (hB : 2 ≤ p.B) (o : Site n) : LocalOn (d.home R p o) (d.plain R o) := by
  intro U V h; unfold plain; cases he : d.2
  · exact congrArg G.price (face_local (o,d.1) U V (agrees_mono h (Finset.coe_subset.mpr (d.face_home R hB o))))
  · exact congrArg₂ (fun (x y : G.Color) => inner ℝ x y / 2)
      (slot_reads (d.left R _) o U V (agrees_mono h (Finset.coe_subset.mpr (d.walk_home R p o he).1)))
      (slot_reads (d.right R _) o U V (agrees_mono h (Finset.coe_subset.mpr (d.walk_home R p o he).2)))
lemma plain_gauge (o : Site n) : GaugeInvariant (plain R d o) := by
  intro k U; simp only [plain,Work.F05.slot_gauge,inner_adjoint,face_gauge,G.price_conj]
lemma proxy_cont (o : Site n) : Continuous (proxy R d o) := by
  unfold proxy analogue; cases e : d.2 <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
lemma proxy_local (o : Site n) : LocalOn (halo 2 {o}) (d.proxy R o) := by intro U V he; simp only [proxy,analogue, petals_reads o _ U V he]
lemma proxy_gauge (o : Site n) : GaugeInvariant (proxy R d o) := by intro k U; simp only [proxy,analogue, petals_gauge,inner_adjoint]
@[fun_prop] lemma live_meas (p : BudgetPoint) (o : Site n) : Measurable (live R c d p o) := by
  unfold live; cases e : d.2
  · dsimp only [Sum.elim_inl,clipped]; apply Measurable.ite (isClosed_le (by unfold faceValue; fun_prop) continuous_const).measurableSet <;> unfold faceValue <;> fun_prop
  dsimp only [Sum.elim_inr]; exact Measurable.ite (kept_closed c _ _).measurableSet (measurable_const.mul (d.plain_cont R o).measurable) measurable_const
lemma live_local (h : Decent c p) (o : Site n) : LocalOn (d.home R p o) (live R c d p o) := by
  intro U V he
  have hl := face_local (o,d.1) U V (agrees_mono he (Finset.coe_subset.mpr (d.face_home R h.radius o)))
  unfold live; dsimp only at hl; rw [hl,d.plain_local R p h.radius o U V he, kept_local c h o (agrees_mono he (Finset.coe_subset.mpr (d.halo_home R p o)))]
lemma live_gauge (o : Site n) : GaugeInvariant (d.live R c p o) := by intro k U; simp only [live,face_gauge,G.chord_conj, kept_gauge,d.plain_gauge R o k U]
lemma live_plain (h : Decent c p) {U : Config G n} (o : Site n) (hu : Healthy p.threshold (d.home R p o) U) :
    d.live R c p o U = d.mark R c * d.plain R o U := by
  have hl := kept_small_halo h (healthy_mono (halo_home ..) hu)
  unfold live; cases he : d.2
  · simp only [Sum.elim_inl,clipped, if_pos (kept_small c p U (o,d.1) hl), plain,mark,he,G.chord_price]; ring
  exact if_pos hl
lemma shapeBound (o : Site n) (U : Config G n) : ‖d.live R c p o U‖ ≤
    |d.mark R c| * (2 * p.threshold * Real.exp ((d.length R)/c.relaxation)) := by
  unfold live mark length; cases he : d.2 with
  | inl _ =>
    have ht := p.threshold_le; have hc := c.kink; have hd := c.quadratic_pos; have hp := p.threshold_pos; have hC := c.tail_pos
    simp only [Sum.elim_inl,abs_of_pos hd,Nat.cast_zero,zero_div,Real.exp_zero,mul_one]; unfold clipped; split
    next h => rw [Real.norm_of_nonneg (by positivity)]
              have hi:=G.chord_nonneg (faceValue U (o,d.1)); linarith only [mul_le_mul_of_nonneg_left (show G.chord (faceValue U (o,d.1))^2 ≤ 4 * p.threshold by nlinarith) hd.le]
    rw [Real.norm_of_nonneg (by exact mul_nonneg (by positivity) (G.chord_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (G.chord_le_two _) (by positivity)).trans (by nlinarith only [mul_le_mul_of_nonneg_right (show c.linear≤c.direct by linarith) hp.le])
  | inr j =>
    have hp := p.threshold_pos
    dsimp only [Sum.elim_inr]; split
    next h =>
      simp only [he, Sum.elim_inr, norm_mul,Real.norm_eq_abs,plain,abs_div]; push_cast
      rw [← abs_mul]
      refine mul_le_mul_of_nonneg_left ((div_le_self (abs_nonneg _) (by norm_num : 1≤ |(2:ℝ)|)).trans ((abs_real_inner_le_norm ..).trans
        ((mul_le_mul (kept_slot (left R d j) h) (kept_slot (right R d j) h) (norm_nonneg _) (by positivity)).trans ?_))) (abs_nonneg _)
      rw [add_div,Real.exp_add]; nlinarith only [p.threshold_le, hp, mul_nonneg (Real.exp_nonneg ((d.left R j).length/c.relaxation))
        (Real.exp_nonneg ((d.right R j).length/c.relaxation)),mul_le_mul_of_nonneg_right (show p.threshold*p.threshold≤2*p.threshold by nlinarith [p.threshold_le])
        (mul_nonneg (Real.exp_nonneg ((d.left R j).length/c.relaxation)) (Real.exp_nonneg ((d.right R j).length/c.relaxation)))]
    rw [norm_zero]; positivity
end Low
end YM.AnalyticBridge.VerifiedReset
