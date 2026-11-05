import YM.AnalyticBridge.VERIFIED_RESET_STEP.Projection
import YM.Next.FOUNDATIONS.Regular
import YM.Next.FREE_KERNELS.Lifts
import YM.Progress.DIRECTED_RECIPE.Germs
import YM.Push.BETA_TRANSPORT.Margins
import YM.UVNext.PRICED_KERNELS.Costed


/-!
# Prices through scalar operations

Extending the fixed-label calculus to reset residuals. Left derivatives on
healthy closed sets; full neighborhoods even at the boundary of a mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG Next.Foundations UVNext.PricedKernels Work.G07 Topology
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X Y : Support n}

section Bills
variable {o : Site n} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Bill (p : BudgetPoint) (o : Site n) (Z : Config G n → Prop) (a : ℝ) (f : Config G n → E) := bill p.order (p.dirBound o) Z a f
variable {Z Z' : Config G n → Prop} {a b : ℝ} {f g : Config G n → E}
namespace Bill
lemma le (h : Bill p o Z a f) (he : a ≤ b) : Bill p o Z b f := bill.le h he
lemma norm (h : Bill p o Z a f) {l} (hl : l.length ≤ p.order) (hd : ∀ i∈l,p.dirBound o i) {U} (hU : Z U) : ‖leftDerivs f l U‖ ≤ a :=
    bill.norm h l hl hd U hU
lemma sup (h : Bill p o Z a f) (hz : ∀ U,Healthy p.threshold X U → Z U) : 0 ≤ a ∧ ∀ U : Config G n,
    Healthy p.threshold X U → ∀ l : List (Dir G n), l.length ≤ p.order → (∀ i∈l,p.dirBound o i) → ‖leftDerivs f l U‖ ≤ a :=
  ⟨h.nonneg,fun _ he _l hl hd => Bill.norm h hl hd (hz _ he)⟩
lemma const (p : BudgetPoint) (x : E) : Bill p o Z ‖x‖ fun _ => x := LeftBound.const zero_le_one x
lemma sum {ι : Type*} {a : ι → ℝ} {f : ι → Config G n → E} (I : Finset ι) (h : ∀ i∈I, Bill p o Z (a i) (f i)) :
    Bill p o Z (∑ i ∈ I,a i) (fun U => ∑ i ∈ I,f i U) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; simpa only [norm_zero] using const (o:=o) (Z:=Z) p (0:E)
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

lemma scale (c : ℝ) (h : Bill p o Z a f) : Bill p o Z (|c| *a) fun U => c • f U := by
  have hL : ∀ l U, leftDerivs (fun U => c • f U) l U = c • leftDerivs f l U := by
    intro l; induction l with
    | nil => exact fun _ => rfl
    | cons A l ih => simp_rw [leftDerivs,ih]; intro U; exact deriv_const_smul_field c _
  refine ⟨h.smooth.postcomp (c • ContinuousLinearMap.id ℝ _),mul_nonneg (abs_nonneg _) h.nonneg, ?_⟩
  intro l hl hd U hU
  rw [hL,one_pow,mul_one,norm_smul]; exact mul_le_mul_of_nonneg_left (Bill.norm h hl hd hU) (abs_nonneg _)
lemma mul_left (c : ℝ) {f : Pot G n} (h : Bill p o Z a f) : Bill p o Z (|c| *a) fun U => c*f U := scale c h
lemma sub (h : Bill p o Z a f) (h' : Bill p o Z b g) : Bill p o Z (a+b) fun U => f U - g U := by
  simpa only [sub_eq_add_neg,abs_neg,abs_one,one_mul,neg_one_smul] using h.add (scale (-1) h')
end Bill
end Bills

def pairingCost (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) := 2^m * ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖
lemma pairing_nonneg (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) : 0 ≤ pairingCost E m := by unfold pairingCost; positivity
lemma Bill.pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {o : Site n} {Z a b} {f g : Config G n → E}
    (h : Bill p o Z a f) (h' : Bill p o Z b g) : Bill p o Z (pairingCost E p.order * a*b) fun U => inner ℝ (f U) (g U) := by
  rw [pairingCost, mul_assoc (2^p.order:ℝ) _ a]
  exact bill.times h' (h.postcomp (innerSL ℝ))

variable {f g : Pot G n} {o : Site n} {a b : ℝ}
lemma reg_bill {Z : Config G n → Prop} (h : Bill p o Z a f) (hc : Measurable f) (hl : LocalOn X f) (hg : GaugeInvariant f) :
    p.Regular X f := ⟨hl,hc,hg,fun _ _ => ((h.smooth [] (by simp) _).of_le (by exact_mod_cast (le_top : (p.order:ℕ∞) ≤ ⊤))).contDiffAt,
      fun U _ A l hl => h.smooth.has hl.le U A⟩
lemma reg_larger (h : p.Regular X f) (hs : X ⊆ Y) : p.Regular Y f :=
  ⟨fun _ _ hv => h.sites _ _ (agrees_mono hv (Finset.coe_subset.mpr hs)), h.borel,h.symmetry,
    fun U hU => h.smooth U (Finset.disjoint_of_subset_left hs hU),fun U hU => h.hasDerivs U (Finset.disjoint_of_subset_left hs hU)⟩
lemma sup_larger (h : p.supBounds o X f a) (hs : X ⊆ Y) : p.supBounds o Y f a :=
  ⟨h.1, fun U hu => h.2 U (Finset.disjoint_of_subset_left hs hu)⟩
lemma sup_le (h : p.supBounds o X f a) (e : a ≤ b) : p.supBounds o X f b :=
  ⟨h.1.trans e,fun U hU l hl hL => (h.2 U hU l hl hL).trans e⟩

lemma reg_const (x : ℝ) : p.Regular X fun _ : Config G n => x := reg_bill (Bill.const (o:=0) (Z:=Healthy p.threshold X) p x) measurable_const (fun _ _ _ => rfl) (fun _ _ => rfl)
lemma sup_const (x : ℝ) : p.supBounds o X (fun _ : Config G n => x) |x| := Bill.sup (Bill.const p x) (fun _ h => h)
lemma reg_sub (h : p.Regular X f) (h' : p.Regular X g) : p.Regular X (f-g) :=
  ⟨fun _ _ hv => congrArg₂ (·-·) (h.sites _ _ hv) (h'.sites _ _ hv), h.borel.sub h'.borel,
    fun _ _ => congrArg₂ (·-·) (h.symmetry _ _) (h'.symmetry _ _),fun U hU => (h.smooth U hU).sub (h'.smooth U hU),
    fun U hU A _l hl => left_has A hl ((h.smooth U hU).sub (h'.smooth U hU))⟩

private lemma near {U : Config G n} {k : ℕ}
    (he : ContDiffAt ℝ k (f ∘ increment U) 0) (A : Dir G n) :
    ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ k (f ∘ increment (increment U (t • A))) 0 := by
  obtain ⟨c,hc,hC,hcc⟩ := Progress.DirectedRecipe.shifted (u:=Prod.fst (α:=Dir G n) (β:=Dir G n)) (v:=Prod.snd)
    (x:=0) (m:=↑k) rfl rfl contDiffAt_fst contDiffAt_snd
  have hb := (((hc.symm ▸ he).comp (f:=c) 0 hC).congr_of_eventuallyEq ((hcc U).fun_comp f)).eventually (by simp)
  let q (t : ℝ) := (t • A, (0:Dir G n))
  have ht : Tendsto q (𝓝 0) (𝓝 0) := by
    rw [← show q 0=0 by simp [q, Prod.zero_eq_mk]]; exact (show Continuous q by unfold q; fun_prop).tendsto _
  filter_upwards [ht.eventually hb] with i hi
  exact hi.comp 0 (f:=fun x => (i • A,x)) (contDiffAt_const.prodMk contDiffAt_id)
lemma left_sub {k : ℕ} {U} (h : ContDiffAt ℝ k (f ∘ increment U) 0) (h' : ContDiffAt ℝ k (g ∘ increment U) 0)
    {l : List (Dir G n)} (hl : l.length ≤ k) : leftDerivs (f-g) l U = leftDerivs f l U - leftDerivs g l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    have hb : l.length < k := hl
    refine (((left_has A hb h).sub (left_has A hb h')).congr_of_eventuallyEq (f₁:=fun t => leftDerivs (f-g) l (increment U (t • A))) ?_).deriv
    filter_upwards [near h A,near h' A] with t h₁ h₂ using ih h₁ h₂ hb.le
lemma sup_sub (h : p.Regular X f) (h' : p.Regular X g) (ha : p.supBounds o X f a) (hb : p.supBounds o X g b) :
    p.supBounds o X (f-g) (a+b) := by
  refine ⟨add_nonneg ha.1 hb.1,fun U hu l hl hD => ?_⟩; rw [left_sub (h.smooth U hu) (h'.smooth U hu) hl]; exact
    (norm_sub_le ..).trans (add_le_add (ha.2 _ hu _ hl hD) (hb.2 _ hu _ hl hD))
lemma sup_varies {d : RegularAddress n} (h : p.Regular d.support f) (h' : p.Regular d.support g) :
    Shoot.variesRegular p d f g a ↔ p.supBounds d.site d.support (f-g) a :=
  and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hu => forall_congr' fun _ => forall_congr' fun hl => by
    rw [left_sub (h.smooth U hu) (h'.smooth U hu) hl]
lemma hessian_sub (h : p.Regular X f) (h' : p.Regular X g) (u v : Dir G n) :
    logHessian (f-g) u v = logHessian f u v - logHessian g u v := by
  change (iteratedFDeriv ℝ 2 (germ f - germ g) 0) _ = _
  rw [iteratedFDeriv_sub_apply (germ_diff h) (germ_diff h')]; rfl
lemma hessian_zero (a : ℝ) (u v : Dir G n) : logHessian (fun _ => a) u v = 0 := by simp [hessian_eq,germ,Function.comp_def]
lemma projection_sub (d : RegularAddress n) (h : p.Regular X f) (h' : p.Regular X g) (i j : PlaqAxes) :
    projection d (f-g) i j = projection d f i j - projection d g i j := by
  simp only [projection]; split
  · exact hessian_sub h h' _ _
  simp
end YM.AnalyticBridge.VerifiedReset
