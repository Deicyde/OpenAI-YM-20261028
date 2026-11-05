import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Infinitesimal
import YM.Next.WARD_BIN.Lies
import YM.UVNext.PRICED_KERNELS.Costed
import YM.UVNext.PRICED_KERNELS.Echo



/-!
# Local bills

All uses at a fixed output threshold. Bounded physical left directions,
Wheels orientation for the real torus. No assumption off the closure of the
good region except what `Regular` itself carries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Set Filter Function Lattice Wilson RG UVNext.PricedKernels Work Work.G07 WardBin
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X Y : Support n} {o : Site n} {a b : ℝ}

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : Config G n → E} {g : Config G n → F}

lemma bill_scalar (u : ℝ) {k D Z} (H : bill k D Z a f) : bill k D Z (|u| *a) fun U => u • f U := by
  let L : E→L[ℝ] E:= u • ContinuousLinearMap.id ℝ E
  have h : ‖L‖≤|u| := by
    rw [show |u|= ‖u‖ from rfl]; unfold L; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  exact bill.le (H.postcomp L) (mul_le_mul_of_nonneg_right h H.nonneg)

lemma bill_pair {k D Z} (hv : bill k D Z a f) (hh : bill k D Z b g) (q : E →L[ℝ] F →L[ℝ] ℝ) :
    bill k D Z (2^k*(‖q‖*a)*b) fun U => q (f U) (g U) := bill.times hh (hv.postcomp q)

lemma sup_of_bill (h : bill p.order (p.dirBound o) (Healthy p.threshold X) a f) : p.supBounds o X f a :=
  ⟨h.nonneg,fun U hU l hl hA => by simpa using h.bound l hl hA U hU⟩

lemma mask_cost (h : p.supBounds o X f a) (U : Config G n) : ‖masked p.threshold X f U‖ ≤ a := by
  by_cases hc : Healthy p.threshold X U
  · rw [masked_eq _ _ _ _ hc]; exact h.2 U hc [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hc,norm_zero]; exact h.1
end

section
variable {f g : Config G n → ℝ}
lemma stencil_gi (Hf : GaugeInvariant f) (t : ℝ) (X : Support n) : GaugeInvariant (masked t X f) := by
  intro k U
  have hv : Healthy t X (gauge k U)↔Healthy t X U := by simp [Healthy]
  by_cases h : Healthy t X U
  · rw [masked_eq _ _ _ _ (hv.mpr h), masked_eq _ _ _ _ h]; exact Hf k U
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt hv.mp h)]

lemma stencil_reads (X : Support n) (Hf : LocalOn (X:Set (Site n)) f) (t : ℝ) : UsesFinal t X (masked t X f) := by
  intro U V hu he
  have hv : Healthy t X U↔Healthy t X V := by simp [Healthy,Finset.disjoint_iff_inter_eq_empty,he]
  by_cases hh : Healthy t X U
  · rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ (hv.mp hh)]; exact Hf U V hu
  rw [masked_ne _ _ _ _ hh,masked_ne _ _ _ _ (mt hv.mpr hh)]

lemma reg_bill (p : BudgetPoint) (X : Support n) {o a} (hl : LocalOn (X:Set (Site n)) f)
    (hf : Continuous f) (he : GaugeInvariant f) (ht : bill p.order (p.dirBound o) (Healthy p.threshold X) a f) :
    p.Regular X f :=
  ⟨hl,hf.measurable,he,fun U _ => (ht.smooth [] (Nat.zero_le _) U).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top),
    fun U _ A _ h => ht.smooth.has h.le U A⟩

lemma reg_extend (Hf : p.Regular X f) (he : X⊆Y) : p.Regular Y f :=
  ⟨fun U V h => Hf.sites _ _ (agrees_mono h (by exact he)), Hf.borel, Hf.symmetry,
    fun U hh => Hf.smooth _ (Disjoint.mono_left he hh),fun U hh => Hf.hasDerivs _ (Disjoint.mono_left he hh)⟩
lemma sup_extend (Hf : p.supBounds o X f a) (he : X⊆Y) : p.supBounds o Y f a :=
  ⟨Hf.1,fun U hh => Hf.2 U (Disjoint.mono_left he hh)⟩
lemma sup_larger (h : p.supBounds o X f a) (he : a≤b) : p.supBounds o X f b :=
  ⟨h.1.trans he, fun U hu l hl hg => (h.2 U hu l hl hg).trans he⟩

lemma reg_const (a : ℝ) : p.Regular X (fun _ : Config G n => a) :=
  reg_bill _ _ (fun _ _ _ => rfl) continuous_const (fun _ _ => rfl) (o:=(0:Site n)) (LeftBound.const zero_le_one a)
lemma sup_const (a : ℝ) : p.supBounds o X (fun _ : Config G n => a) |a| := sup_of_bill (LeftBound.const zero_le_one a)

lemma reg_sub (ha : p.Regular X f) (hb : p.Regular X g) : p.Regular X (f-g) := by
  have h U (hu : Healthy p.threshold X U) := (show Lies.Germ p.order f U from ha.smooth _ hu).sub (g:=g) (hb.smooth _ hu)
  exact ⟨fun U V hu => congr_arg₂ (·-·) (ha.sites U V hu) (hb.sites U V hu), ha.borel.sub hb.borel,
    fun k U => congr_arg₂ (·-·) (ha.symmetry k U) (hb.symmetry k U), h, fun U hu A l hl => (h U hu).has l A hl⟩
lemma sup_sub (ha : p.Regular X f) (hb : p.Regular X g) (he : p.supBounds o X f a) (hu : p.supBounds o X g b) :
    p.supBounds o X (f-g) (a+b) := by
  refine ⟨add_nonneg he.1 hu.1,fun U hh l hl ht => ?_⟩
  rw [Lies.left_sub ha hb hl hh]; exact (norm_sub_le ..).trans (add_le_add (he.2 U hh l hl ht) (hu.2 U hh l hl ht))

private lemma left_scale (f : Config G n → ℝ) (c : ℝ) (l) (U : Config G n) : leftDerivs (c • f) l U=c • leftDerivs f l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs,ih]; exact deriv_fun_const_smul_field ..

lemma reg_scale (c : ℝ) (Hf : p.Regular X f) : p.Regular X (c • f) := by
  have h (U : Config G n) (hu : Healthy p.threshold X U) : Lies.Germ p.order (c • f) U := (Hf.smooth U hu).const_smul c
  exact ⟨fun U V h => congr_arg (c • ·) (Hf.sites U V h), Hf.borel.const_smul _,fun i U => congr_arg (c • ·) (Hf.symmetry i U),h,
    fun U hu A l hl => (h U hu).has l A hl⟩
lemma sup_scale (c : ℝ) (Hf : p.supBounds o X f a) : p.supBounds o X (c • f) (|c| *a) := by
  refine ⟨mul_nonneg (abs_nonneg _) Hf.1,fun U hh l hl hg => ?_⟩
  rw [left_scale,norm_smul]; exact mul_le_mul_of_nonneg_left (Hf.2 U hh l hl hg) (abs_nonneg _)

lemma const_horizontal (c : ℝ) (A B : Directions G n) : H (fun _ => c) A B=0 := by
  rw [← log_eq_H]; simp [logHessian,iteratedFDeriv_const_of_ne two_ne_zero]
lemma sub_jet (ha : p.Regular X f) (hb : p.Regular X g) (A B) : H (f-g) A B=H f A B-H g A B := by
  rw [← log_eq_H,← log_eq_H,← log_eq_H]; unfold logHessian
  change iteratedFDeriv ℝ 2 ((f∘increment 1) - g ∘ increment 1) 0 _= _
  rw [iteratedFDeriv_sub_apply (i:=2) (flat_C2 ha) (flat_C2 hb)]; rfl
lemma scalar_jet (ha : p.Regular X f) (c : ℝ) (A B) : H (c • f) A B = c*H f A B := by
  rw [← log_eq_H,← log_eq_H]; unfold logHessian
  change iteratedFDeriv ℝ 2 (c • (f∘increment 1)) 0 _ = _
  rw [iteratedFDeriv_const_smul_apply (i:=2) (flat_C2 ha)]; rfl

lemma shrink_smooth (p : BudgetPoint) (X : Support n) (h : p.Regular X f) (A) : ContDiffAt ℝ 2 (fun t : ℝ => f (increment 1 (t • A))) 0 :=
  ((show ContDiffAt ℝ 2 (f ∘ increment 1) ((0:ℝ) • A) by simpa using flat_C2 h).comp 0 (f:=fun t : ℝ => t • A) (by fun_prop))

lemma from_ray (hs : G.Simple) {A : Directions G n} (h : p.Regular X f) {r : ℝ}
    (he : Tendsto (fun t : ℝ => f (increment 1 (t • A)) / t^2) (𝓝[≠] (0:ℝ)) (𝓝 r)) : H f A A=2*r := by
  have hc:=shrink_smooth p X h A; rw [diagonal hs h]; obtain ⟨hv,hv'⟩:=F03.value_slope_of_sq_limit hc.continuousAt he
  have ht := tendsto_nhds_unique he (F03.taylor_limit_two hc hv hv'.deriv); linarith
end
end YM.AnalyticBridge.CouplingShape
