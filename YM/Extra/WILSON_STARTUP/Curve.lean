import YM.Extra.WILSON_STARTUP.Ink

/-!
# Fixed-address continuity at given period and coupling band

Using pointwise bounds even for varying K at genuine flag configurations; not
an assertion about weak equivalence of densities. Finite costs of this
continuity test needn't be uniform in volume.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Function Filter RG Wilson Lattice Design Work Ac Padded Ovens Ovens.Pipes Shoot
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {c : Clip} {x y : ℝ} {X : Set ℝ}

private theorem exp_dist {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : ‖Real.exp a - Real.exp b‖ ≤ ‖a-b‖ := by
  have h := (convex_Iic (0:ℝ)).norm_image_sub_le_of_norm_deriv_le (f:=Real.exp)
    (fun _ _ => Real.differentiableAt_exp) (fun x hx => by
      rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr hx) hb ha
  simpa using h

def total (n : Side) := share * ((Fintype.card (Key n) : ℝ)*2)
theorem total_pos (n : Side) : 0 < total n := mul_pos share_pos (by positivity)

theorem paid_dist (hc : c.direct ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (i : Foot n) (U : Config G n) :
    ‖paid c b i x U - paid c b i y U‖ ≤ ‖x-y‖*total n := by
  unfold paid; split
  next _ =>
    obtain ⟨hh,h⟩ := charge_range c b hc U i.val.2
    refine (exp_dist (by nlinarith) (by nlinarith)).trans ?_
    rw [← sub_mul, norm_mul, Real.norm_of_nonneg hh, show -x - -y = -(x-y) by ring, norm_neg]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg (x-y))
  simp only [sub_zero,norm_zero]; exact mul_nonneg (norm_nonneg _) (total_pos n).le

theorem forced_dist (hc : c.direct ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (i : ℕ) (U : Config G n) :
    ‖(payload c b G n x).forced i U - (payload c b G n y).forced i U‖ ≤ ‖x-y‖*total n := by
  simp only [payload]; split
  · exact paid_dist hc hx hy  _ U
  simp only [sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) (total_pos n).le

lemma posed (hc : c.direct ≤ 1) (hX : ∀ x∈X, 0 ≤ x) : invariantJet b (payload c b G n) X := by
  intro x hx j ε he
  let f (y : ℝ) := ‖y-x‖*total n
  have hf := (show Continuous f by unfold f; fun_prop).tendsto' x 0 (by simp [f])
  filter_upwards [(hf.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds he),self_mem_nhdsWithin] with y hy hy' U
  cases j
  · exact (forced_dist hc (hX y hy') (hX x hx) _ U).trans hy.le
  simp [reach,payload,he.le]

lemma differenceE (ht : b.threshold ≤ threshold G b.order b.power) (i : Sheet n) :
    variesRegular (G:=G) b (eInfo i) (written c i x) (written c i y) (‖weight c x - weight c y‖*item G b) := by
  have hp := item_pos G b
  refine ⟨by positivity,?_⟩
  intro U hU l hl hD
  cases i with
  | inr i => simp [written,hp.le, mul_nonneg]
  | inl i =>
    change ‖leftDerivs (weight c x • i.accrual) l U - leftDerivs (weight c y • i.accrual) l U‖ ≤ _
    rw [left_mult,left_mult,← sub_mul,norm_mul]; gcongr
    exact (accrual_fit i ht).2 U hU l hl hD

def totalE (n : Side) (c : Clip) (G : Gauge) (b : BudgetPoint) (x y : ℝ) := ∑ i : Sheet n, b.mass (eInfo i).support (‖weight c x - weight c y‖*item G b)
def totalK (n : Side) (b : BudgetPoint) (x y : ℝ) := ∑ i : Foot n, b.mass i.val.1 (‖x-y‖ * total n)

lemma curve (ht : b.threshold ≤ threshold G b.order b.power) (hc : c.direct ≤ 1) (hX : ∀ x∈X, 0 ≤ x) :
    Curve b (Bid.Cake (payload c b G n) (dictionary G n) (top G c) c b) X := by
  refine ⟨continuousOn_id,continuousOn_const, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,fun ε he x hx => ?_⟩
  have hf := (show Continuous (totalE n c G b x) by unfold totalE BudgetPoint.mass weight; fun_prop).tendsto' x 0
    (by simp [totalE,BudgetPoint.mass])
  have hg := (show Continuous (totalK n b x) by unfold totalK BudgetPoint.mass; fun_prop).tendsto' x 0 (by simp [totalK,BudgetPoint.mass])
  filter_upwards [(hf.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds he), (hg.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds he),self_mem_nhdsWithin] with y hy hy' hyx
  let p := ‖weight c x-weight c y‖ * item G b
  let q := ‖x-y‖ * total n
  have hp : 0 ≤ p := mul_nonneg (norm_nonneg _) (item_pos ..).le
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) (total_pos ..).le
  refine ⟨fun i => if fixed (Sheet n) i then p else 0, fun i => if fixed (Foot n) i then q else 0, fun i => ?_,fun i => ?_,
    Padded.budget (α:=Sheet n) (fun i => ?_) (fun i => mul_nonneg (Real.exp_pos _).le hp) hy.le,
    Padded.budget (α:=Foot n) (fun i => ?_) (fun i => mul_nonneg (Real.exp_pos _).le hq) hy'.le⟩
  · simp only [Bid.Cake,pours,dictionary,payload]; split
    · exact differenceE ht _
    exact ⟨le_rfl,fun _ _ _ _ _ => by simp⟩
  · simp only [Bid.Cake,pours,dictionary,payload]; split
    · exact ⟨hq,paid_dist hc (hX x hx) (hX y hyx) _⟩
    exact ⟨le_rfl,fun _ => by simp⟩
  · dsimp only; split <;> first | rfl | exact mul_zero _
  · dsimp only; split <;> first | rfl | exact mul_zero _
end YM.WilsonStartup.Start
