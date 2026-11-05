import YM.Extra.WILSON_STARTUP.Labels

/-!
# Initial E ink: atom residuals on the hard good footprints
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Start
open Function Filter RG Wilson Lattice Design Work Ac Padded
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {c : Clip}
        {p : Cell n} {i : Key n} {o : Site n} {X : Support n} {v β C δ : ℝ} {f : Config G n → ℝ}

lemma zero_reg : b.Regular X (0 : Config G n → ℝ) :=
  ⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun _ _ => contDiffAt_const,
    fun _ _ a _ he => Next.Foundations.left_has (f:=0) a he contDiffAt_const⟩

lemma times_reg (β : ℝ) (h : b.Regular X f) : b.Regular X (β • f) := by
  refine ⟨fun U V he => congr_arg (β • ·) (h.sites U V he),h.borel.const_smul _,
    fun k U => congr_arg (β • ·) (h.symmetry k U), fun U he => (h.smooth U he).const_smul β,fun U he a l hl => ?_⟩
  exact Next.Foundations.left_has a hl ((h.smooth U he).const_smul β)

lemma left_mult (β : ℝ) (l : List (Directions G n)) (U : Config G n) : leftDerivs (β • f) l U = β * leftDerivs f l U := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih => simp_rw [leftDerivs,ih,deriv_const_mul_field]

lemma zero_bound : b.supBounds o X (0 : Config G n → ℝ) 0 := by
  refine ⟨le_rfl,fun U _ l _ _ => ?_⟩; change ‖leftDerivs (fun _ => (0:ℝ)) l U‖ ≤ 0; simp [G07.left_const]

lemma times_bound (β : ℝ) (h : b.supBounds o X f C) : b.supBounds o X (β • f) (‖β‖*C) :=
  ⟨mul_nonneg (norm_nonneg _) h.1,fun U hu l hl ha => by rw [left_mult,norm_mul]; exact mul_le_mul_of_nonneg_left (h.2 U hu l hl ha) (norm_nonneg _)⟩

lemma accrual_regular (i : Key n) : b.Regular i.skin i.accrual (G:=G) := by
  rw [Key.accrual_def,Key.skin_positive]; exact residual_regular ..

lemma accrual_null (i : Key n) (β : ℝ) : (β • i.accrual) (1:Config G n) = 0 ∧ ∀ x y,
      logHessian (β • i.accrual (G:=G)) x y = 0 := by
  rw [Key.accrual_def]; refine ⟨by simp [residual_one], fun x y => ?_⟩
  change iteratedFDeriv ℝ 2 (β • (residual G i.positive ∘ increment 1)) 0 ![x,y] = 0
  rw [iteratedFDeriv_const_smul_apply ((residual_smooth _ _).contDiffAt.of_le le_top),smul_apply]
  exact (congr_arg (β • ·) (residual_hess i.positive x y)).trans (smul_zero ..)

lemma regularFamily (β : ℝ) : (raw G n c b β).RegularFamily b := by
  have he (i : ℕ) : b.Regular ((dictionary G n).reg i).support ((raw G n c b β).E i) ∧
      ((raw G n c b β).E i) 1=0 ∧ ∀ x y,logHessian ((raw G n c b β).E i) x y = 0 := by
    change b.Regular (eInfo _).support _ ∧ _
    simp only [raw,Ovens.Pipes.pours,payload]; split
    · rcases name (Sheet n) i with p|s
      · exact ⟨times_reg _ (accrual_regular ..),accrual_null ..⟩
      exact ⟨zero_reg,rfl,fun x y => by simp [written,logHessian]⟩
    exact ⟨zero_reg,rfl,fun x y => by simp [logHessian]⟩
  exact ⟨fun i => (he i).1,fun i => (he i).2.1,fun i _ x y _ _ => (he i).2.2 x y⟩

def price (G : Gauge) (k P : ℕ) := (residual_price G k P).choose
def threshold (G : Gauge) (k P : ℕ) := (residual_price G k P).choose_spec.choose

theorem constants (G : Gauge) (k P : ℕ) : 0 < price G k P ∧ 0 < threshold G k P ∧ threshold G k P ≤ 1 :=
  let h := (residual_price G k P).choose_spec.choose_spec; ⟨h.1,h.2.1,h.2.2.1⟩

def item (G : Gauge) (b : BudgetPoint) := price G b.order b.power * b.threshold^5

lemma item_pos (G : Gauge) (b : BudgetPoint) : 0 < item G b := mul_pos (constants ..).1 (pow_pos b.threshold_pos _)

theorem accrual_fit (i : Key n) (ht : b.threshold ≤ threshold G b.order b.power) : b.supBounds i.native i.skin (i.accrual (G:=G)) (item G b) := by
  rw [Key.accrual_def,Key.skin_positive]
  exact ((residual_price G b.order b.power).choose_spec.choose_spec.2.2.2 b rfl rfl ht n i.positive i.native (i.skin_positive ▸ i.native_mem))

lemma weight_le (β : ℝ) (h : c.direct ≤ 1) : ‖weight c β‖ ≤ ‖β‖ := by
  have hs := share_pos
  have hs' : share ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α:=Signed))
  have hc : bulk c ≤ 1 := sub_le_self _ c.quadratic_pos.le
  rw [weight,norm_mul,norm_mul,Real.norm_of_nonneg hs.le,Real.norm_of_nonneg (r:=bulk c) (sub_nonneg.mpr h)]
  exact (mul_le_of_le_one_right (by positivity) hc).trans (mul_le_of_le_one_right (by positivity) hs')

def overhead (b : BudgetPoint) := Real.exp (b.supportExponent*5^4)
def book (G : Gauge) (b : BudgetPoint) (β : ℝ) := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(overhead b*(β*item G b))

theorem pad_cost (i : Site n) : coverNumber b.B (pad b i) ≤ 5^4 := Corona.tile i 2 b.B b.B_pos

theorem skin_cost (i : Key n) : coverNumber b.B i.skin ≤ 5^4 := by
  apply le_trans _ (pad_cost (b:=b) i.native)
  apply Corona.cover_mono
  intro z hz; exact (mem_pad ..).mpr (le_trans (i.nearby hz) (Nat.mul_le_mul_left 2 b.B_pos))

lemma mass_item (i : Key n) (y : ℝ) (hy : ‖β‖ ≤ y) (hc : c.direct ≤ 1) :
    b.mass i.skin (‖weight c β‖ * item G b) ≤ overhead b * (y * item G b) := by
  unfold BudgetPoint.mass overhead
  have h := item_pos G b; have hs := b.exponent_pos
  have he : (coverNumber b.B i.skin : ℝ) ≤ 5^4 := by exact_mod_cast skin_cost i
  gcongr; exact (weight_le β hc).trans hy

theorem sum_items (o : Site n) {y : ℝ} (hy : ‖β‖ ≤ y) (hc : c.direct ≤ 1) : (∑ i : Sheet n,
      if (eInfo i).site = o then b.mass (eInfo i).support (i.elim (fun _ => ‖weight c β‖ * item G b) (fun _ => 0)) else 0) ≤ book G b y := by
  rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,BudgetPoint.mass,mul_zero,ite_self,Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _ : Cell n => _)]
  unfold book
  rw [show (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(overhead b*(y*item G b)) = ∑ _s : Signed, ∑ x : Site n,
      ∑ _i : PlaqAxes, (if x=o then overhead b*(y*item G b) else 0) from by simp; ring]
  gcongr ∑ _, ∑ _, ∑ _, ?_ with s _ x _ i _
  change (if x=o then _ else _) ≤ _
  split <;> first | exact mass_item (s,x,i) _ hy hc | exact le_rfl

theorem ink (ht : b.threshold ≤ threshold G b.order b.power) (hc : c.direct ≤ 1) {q : ℝ} (hy : ‖β‖ ≤ v)
    (hp : book G b v ≤ q) : (raw G n c b β).EBound b q := by
  let E := fun i : Sheet n => i.elim (fun _ => ‖weight c β‖*item G b) (fun _ => (0:ℝ))
  let T := fun i : ℕ => if fixed (Sheet n) i then E (name (Sheet n) i) else 0
  have he : ∀ i, b.supBounds ((raw G n c b β).reg i).site ((raw G n c b β).reg i).support ((raw G n c b β).E i) (T i) := by
    intro i
    simp only [T,raw,Ovens.Pipes.pours,payload,dictionary]; split
    · cases h : name (Sheet n) i with
      | inl p => exact times_bound _ (accrual_fit p ht)
      | inr s => exact zero_bound
    exact zero_bound
  refine ⟨T,he,fun x => Padded.budget (α:=Sheet n) ?_ (fun i => ?_) ((sum_items x hy hc).trans hp)⟩
  · intro i; change (if _ then b.mass _ (ite ..) else _) = _; by_cases h : fixed (Sheet n) i
    · rw [if_pos h,if_pos h]; rfl
    rw [if_neg h,if_neg h]; simp [BudgetPoint.mass]
  split
  · apply mul_nonneg (Real.exp_pos _).le
    simpa only [T,E,name_index,fixed_index,if_true] using (show 0 ≤ T (index i) from (he _).1)
  exact le_rfl

lemma masked_zero (t : ℝ) (s : Support n) (U : Config G n) : masked t s (0 : Config G n → ℝ) U = 0 := by
  by_cases h : Healthy t s U; exact masked_eq _ _ _ _ h; exact masked_ne _ _ _ _ h

lemma written_sum (β : ℝ) (U : Config G n) : (raw G n c b β).additive b U = weight c β * ∑ i : Key n, masked b.threshold i.skin i.accrual U := by
  unfold Activities.additive
  rw [totals (α:=Sheet n) (g:=fun i => masked b.threshold (eInfo i).support (written c i β) U) (fun i => ?_),Fintype.sum_sum_type]; swap
  · unfold Activities.regularOccurrence; simp only [raw,Ovens.Pipes.pours,dictionary,payload]
    split; rfl; exact masked_zero ..
  have he (q : Blank n) : written c (Sum.inr q) β (G:=G) = 0 := rfl
  simp_rw [he,masked_zero,Finset.sum_const_zero,add_zero,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change masked b.threshold i.skin (weight c β • i.accrual) U = _
  by_cases h : Healthy b.threshold i.skin U
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero]
end YM.WilsonStartup.Start
