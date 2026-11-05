import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Canonical

/-!
# The old E surplus at the shape-reset entrance

Work even at an output argument which is off the indicated good sets. Correction
in the E address, what is removed, what has to multiply the *gas* (including on
a failed indicator) are three different local numbers. Earlier integral estimates
acquiring the input costs at this anchor scale not here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice Wilson RG Finset Push.AbsoluteSums WardBin
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {G : Gauge} {n : Side} (P : Activities G n) (b : BudgetPoint)

def sprouts (X : RegularAddress n) : RegularAddress n := ⟨X.site,X.support∪ringlet X.site,mem_union_left _ X.anchor⟩

def heart (i : ℕ) := P.E i 1

def remain (i : ℕ) : Config G n → ℝ := P.E i - (fun _ => heart P i) - cut (P.E i) (P.reg i).site (P.reg i).support

def reap (i : ℕ) := masked b.threshold (sprouts (P.reg i)).support (remain P i)
def pinch (i : ℕ) := masked b.threshold (ringlet (P.reg i).site) (cut (P.E i) (P.reg i).site (P.reg i).support)

def requireLog (i : ℕ) (U : Config G n) := heart P i + reap P b i U + pinch P b i U - P.regularOccurrence b i U

lemma for_cover (i U) (h : Healthy b.threshold (sprouts (P.reg i)).support U) : requireLog P b i U=0 := by
  rw [requireLog, reap,masked_eq _ _ _ _ h,pinch,
    masked_eq _ _ _ _ (Disjoint.mono_left subset_union_right (show Healthy _ ((P.reg i).support ∪ ringlet _) U from h)),
    Activities.regularOccurrence,masked_eq _ _ _ _ (Disjoint.mono_left subset_union_left (show Healthy _ ((P.reg i).support ∪ ringlet _) U from h))]
  change _+(P.E i U-heart P i-_)+_-_=0; ring

def paysLive (G : Gauge) (b : BudgetPoint) := 2+cutPrice G b
def paysAttach (G : Gauge) (b : BudgetPoint) := 2+paysLive G b+cutPrice G b
lemma paysLive_pos : 0<paysLive G b := by unfold paysLive; linarith [cutPrice_nonneg G b]
lemma paysAttach_pos : 0<paysAttach G b := by unfold paysAttach; linarith [cutPrice_nonneg G b,paysLive_pos (G:=G) b]

lemma hints (hs : G.Simple) (hn : 2 ≤ n.val) (i) (h : b.Regular (P.reg i).support (P.E i)) {c : ℝ}
    (hy : b.supBounds (P.reg i).site (P.reg i).support (P.E i) c) : let X := sprouts (P.reg i)
    let L := requireLog P b i
    b.Regular X.support (remain P i) ∧ b.supBounds X.site X.support (remain P i) (paysLive G b*c) ∧
    remain P i 1=0 ∧ (Nonwrapping X.support X.site → ∀ A B, IsAffineDirection X.site A → IsAffineDirection X.site B →
      logHessian (remain P i) A B=0) ∧ GaugeInvariant L ∧ Measurable L ∧ UsesFinal b.threshold X.support L ∧
         ∀ U, |L U| ≤ paysAttach G b*c := by
  intro X L
  let x:= (P.reg i).site; let e:= P.E i; let u:= (P.reg i).support
  have hk : ringlet x⊆X.support:=subset_union_right; have he : u⊆X.support:=subset_union_left
  have hv : |heart P i| ≤ c := hy.2 1 (clear_one b u) [] (Nat.zero_le _) (by simp)
  obtain ⟨h₁,h₂⟩:= cut_billed hs h x hy
  have hr := reg_extend h he; have ha:= reg_const (n:=n) (p:=b) (X:=X.support) (G:=G) (heart P i)
  have hc : b.Regular X.support (remain P i) := reg_sub (reg_sub hr ha) (reg_extend h₁ hk)
  have hh := sup_sub (reg_sub hr ha) (reg_extend h₁ hk)
    (sup_sub (o:=x) hr ha (sup_extend hy he) (sup_const _)) (sup_extend h₂ hk)
  have hR : b.supBounds x X.support (remain P i) (paysLive G b*c) := sup_larger hh (by unfold paysLive; linarith)
  refine ⟨hc,hR,?_,?_,fun k U=>?_,?_,fun U V hD hF=>?_,fun U=>?_⟩
  · simp only [remain, Pi.sub_apply, heart, sub_self,cut_nil]
  · intro hX A B hA hB; obtain ⟨c,d,hA⟩:=onStencil_of_affine hA X.support; obtain ⟨c',d',hB⟩:=onStencil_of_affine hB X.support
    rw [log_eq_H,remain,sub_jet (reg_sub hr ha) (reg_extend h₁ hk),sub_jet hr ha,const_horizontal,sub_zero,
      cut_jet hn hs he (o:=x) hX hk (h:=h) h₁ hA hB, sub_self]
  · simp only [L,requireLog, reap,pinch,Activities.regularOccurrence,stencil_gi h.symmetry _ _ k U,
      stencil_gi (f:=remain P i) hc.symmetry _ _ k U, stencil_gi (f:=cut (P.E i) (P.reg i).site _) h₁.symmetry _ _ k U]
  · exact (((measurable_const.add (masked_measurable _ _ _ hc.borel)).add (masked_measurable _ _ _ h₁.borel)).sub
      (masked_measurable _ _ _ h.borel))
  · change requireLog P b i U = requireLog P b i V
    rw [requireLog,requireLog,show reap P b i U=reap P b i V from stencil_reads _ hc.sites _ U V hD hF,
      show pinch P b i U=pinch P b i V from Work.H03.reads_larger hk (stencil_reads _ h₁.sites _) U V hD hF,
      show P.regularOccurrence b i U=P.regularOccurrence b i V from Work.H03.reads_larger he (stencil_reads _ h.sites _) U V hD hF]
  calc
    |L U| ≤ _ := abs_sub ..
    _ ≤ (((|heart P i| + |reap P b i U|)+|pinch P b i U|)+|P.regularOccurrence b i U|) := by
      apply add_le_add_left; apply le_trans (abs_add_le ..); exact add_le_add_left (abs_add_le ..) _
    _ ≤ ((c+paysLive G b*c)+cutPrice G b*c)+c := add_le_add (add_le_add (add_le_add hv (mask_cost hR U)) (mask_cost h₂ U)) (mask_cost hy U)
    _ = paysAttach G b*c := by unfold paysAttach; ring

lemma shiftSeed (s : Signed) (z : Site n) (hs : G.Simple) (hn : 10<n.val) {δ : ℝ} (he : Profiled P b δ)
    (J : P.Moves s z) (i : ℕ) : let j := J.ep i
    let X := sprouts (P.reg i); let Y := sprouts (P.reg j)
    Y.site=affine s z X.site ∧ Y.support=X.support.image (affine s z) ∧ ∀ U,
      remain P j U=remain P i (pull s z U) ∧ requireLog P b j U=requireLog P b i (pull s z U) := by
  intro j X Y; let x := (P.reg i).site
  have h₁ : (P.reg j).site=affine s z (P.reg i).site := J.reg_site i
  have h₂ : (P.reg j).support=(P.reg i).support.image (affine s z) := J.reg_support i
  have h₃ := ringlet_turn s z (P.reg i).site
  have hx : Y.support = X.support.image (affine s z) := by simp only [Y,X,sprouts,h₂,h₁,image_union,h₃]
  refine ⟨h₁,hx,fun U=>?_⟩
  let V:= pull s z U
  have hV : P.E j=P.E i ∘ pull s z := funext (J.valuesE i)
  have hv : heart P j=heart P i := by simp [heart,hV,pull_empty]
  have hu : cut (P.E j) (P.reg j).site (P.reg j).support U=cut (P.E i) x (P.reg i).support V := by
    rw [cut,cut,h₁,h₂,hV]; congr 1
    rw [strip_via_pull s z hn hs (he.smooth i) (by rw [← h₂,← hV]; exact he.smooth j),show V=pull s z U from rfl,spins]
  have hP := J.valuesE i U
  have hR : remain P j U=remain P i V := by
    change P.E j U-_-_ = P.E i V-_-_; rw [hv,hu]; exact congr_arg₂ (·-·) (congr_arg₂ (·-·) hP rfl) rfl
  refine ⟨hR,?_⟩
  unfold requireLog
  rw [hv,show reap P b j U=reap P b i V from (by unfold reap; rw [hx]; exact mask_cov _ _ _ _ hR.symm),
    show pinch P b j U=pinch P b i V from (by
      unfold pinch
      generalize hj : cut (P.E j) (P.reg j).site (P.reg j).support=cJ at *
      rw [h₁,h₃]; exact mask_cov _ s z U hu.symm),
    show P.regularOccurrence b j U=P.regularOccurrence b i V from (by unfold Activities.regularOccurrence; rw [h₂]; exact mask_cov _ _ _ _ hP.symm)]

-- because the support of the clover only costs one B. Don't lose a factor in A per step.
lemma boost_stamp (a : ℝ) (ha : 0 ≤ a) {f : ℕ → ℝ} {δ : ℝ} (h : Sealed b P.reg f δ) (hh : ∀ i,0≤f i) :
    Sealed b (sprouts ∘ P.reg) (fun i=> a*f i) ((Real.exp b.supportExponent*a)*δ) := by
  intro x
  refine budget_mono (budget_scale (mul_nonneg (Real.exp_pos _).le ha) (h x)) (fun i=> ?_) (fun i=>?_)
  · split <;> first | exact le_rfl | exact mul_nonneg (Real.exp_pos _).le (mul_nonneg ha (hh _))
  change (if (sprouts (P.reg i)).site=x then b.mass _ _ else 0)≤_
  by_cases he : (P.reg i).site=x
  · simp only [sprouts, if_pos he]; unfold BudgetPoint.mass
    calc
      _ ≤ Real.exp (b.supportExponent * (1+↑(coverNumber b.B (P.reg i).support))) * (a*f i) := by
        gcongr
        · exact mul_nonneg ha (hh _)
        · exact b.exponent_pos.le
        exact_mod_cast (Corona.meets_sum (P.reg i).anchor (central ..) b.B).trans (by have := ringPaid b (P.reg i).site; omega)
      _ = _ := by simp only [mul_add,mul_one,Real.exp_add]; ring
  have hu : ¬(sprouts (P.reg i)).site=x:= he; simp [hu,he]

variable {P b}
lemma flat_income {δ : ℝ} (hh : P.EBound b δ) :
    SumBudget (fun i => |heart P i|) (Fintype.card (Site n) * δ) := by
  obtain ⟨c,hc,h⟩:=hh
  exact budget_mono (totalBooked (fun i=> (hc i).1) h) (fun i=>abs_nonneg _) (fun i => (hc i).2 1 (clear_one ..) [] (Nat.zero_le _) (by simp))

lemma live_budget (hs : G.Simple) (hn : 2 ≤ n.val) {δ : ℝ} (hh : Profiled P b δ) :
    Dominated (pinch P b) ∧ Dominated (reap P b) ∧ Dominated (requireLog P b) ∧ Dominated (P.regularOccurrence b) := by
  obtain ⟨c,hc,h⟩:=hh.bound
  have hf := (totalBooked (u:=P.reg) (fun i=> (hc i).1) (p:=b) h).2.1
  refine ⟨⟨_,hf.mul_left (cutPrice G b),fun i U=>mask_cost (cut_billed hs (hh.smooth i) (P.reg i).site (hc i)).2 U⟩,
    ⟨_,hf.mul_left (paysLive G b),fun i U=>mask_cost (hints P b hs hn i (hh.smooth i) (hc i)).2.1 U⟩,
    ⟨_,hf.mul_left (paysAttach G b),fun i U=>(hints P b hs hn i (hh.smooth i) (hc i)).2.2.2.2.2.2.2 U⟩,
    ⟨c,hf,fun i U=>mask_cost (hc i) U⟩⟩

lemma measured_site (hs : G.Simple) (hn : 10<n.val) {δ : ℝ} (hh : Profiled P b δ) (u : G.Color) (hu : ‖u‖=1)
    (x : Site n) (U : Config G n) :
    (∑' i, if (P.reg i).site=x then pinch P b i U else 0) = delta P u*short b U x := by
  by_cases ht : Healthy b.threshold (ringlet x) U
  · let w:=needles x U
    have he (i : ℕ) : (if (P.reg i).site=x then pinch P b i U else 0) = (1/2:ℝ)*shelf P x i w w := by
      unfold shelf; by_cases hc : (P.reg i).site=x
      · rw [if_pos hc, if_pos hc.symm, pinch, hc,masked_eq _ _ _ _ ht]; rfl
      simp [hc,Ne.symm hc]
    rw [short,masked_eq _ _ _ _ ht]; simp_rw [he,tsum_mul_left,← shelf_read hs hh,screen_trace hs hn hh x u hu]
    unfold curlValue squareNorm; unfold w; rw [← sum_div]; ring
  have he (i : ℕ) : (if (P.reg i).site=x then pinch P b i U else 0)=0 := by
    by_cases hc : (P.reg i).site=x
    · rw [if_pos hc,pinch,hc,masked_ne _ _ _ _ ht]
    exact if_neg hc
  rw [short, masked_ne _ _ _ _ ht,mul_zero]; simp only [he, tsum_zero]

lemma measured (hs : G.Simple) (hn : 10<n.val) {δ : ℝ} (hh : Profiled P b δ) (u : G.Color) (hu : ‖u‖=1)
    (U : Config G n) :
    (∑' i, pinch P b i U) = delta P u * ∑ x : Site n, short b U x := by
  let f (x : Site n) (i : ℕ) := if (P.reg i).site=x then pinch P b i U else 0
  have ht (x) : Summable (f x) := ((live_budget hs (by omega) hh).1.absolute U).of_norm_bounded fun i => by
    unfold f; split <;> first | rfl | (rw [norm_zero];exact norm_nonneg _)
  rw [show (fun i=> pinch P b i U)=fun i=>∑ x,f x i from funext fun i => by simp [f],Summable.tsum_finsetSum fun x _ => ht x, mul_sum]
  exact sum_congr rfl fun i _ => measured_site hs hn hh u hu i U
end YM.AnalyticBridge.CouplingShape
