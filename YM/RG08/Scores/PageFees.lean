import YM.RG08.Scores.Pages
import YM.RG08.Scores.Seats
/-!
# Taylor of the pullback test, operator estimate in the same complete budget
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Scores.Pages
open Function Filter Set Tensor Metric
open scoped Topology ContDiff BigOperators
variable {D k : ℕ} {R : ℝ} {c : E4} {δ : ℝ}

def mental (D i : ℕ) : Tensor.T E4 ℝ i →ₗ[ℝ] Exam D where
  toFun x := ⟨Tensor.diagonal x, diag_smooth x D⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def planL (D i : ℕ) (R : ℝ) := ((sheet D R).comp (mental D i)).toContinuousLinearMap
lemma reflect_cost (hc : c∈examinable R) (h:k≤D) : ∃ A : Sight D R →L[ℝ] (Tensor.T E4 ℝ k),
    ‖A‖ ≤ ((k.factorial:ℝ)⁻¹*(4:ℝ)^k) ∧ ∀ g, A (sheet D R g)=coeff g.val k c := by
  let T : Exam D→ₗ[ℝ] Tensor.T E4 ℝ k := {
    toFun g := coeff g.val k c
    map_add' g w:= coeff_add ((score D g).of_le (Nat.cast_le.mpr h)|>.contDiffAt) ((score D w).of_le (Nat.cast_le.mpr h)|>.contDiffAt)
    map_smul' t g:= coeff_smul t ((score D g).of_le (Nat.cast_le.mpr h)|>.contDiffAt) }
  let x : Close R := ⟨c,hc⟩
  have hv (φ : Exam D) : ‖T φ‖≤ (k.factorial:ℝ)⁻¹ * 4^k * ‖sheet D R φ‖ := by
    change ‖coeff _ _ _‖ ≤ (k.factorial:ℝ)⁻¹*4^k* _
    unfold coeff; rw [norm_smul,Real.norm_of_nonneg (by positivity),mul_assoc]; exact mul_le_mul_of_nonneg_left (jet_budget D R φ k h x) (by positivity)
  obtain ⟨w,hW,hE⟩:= port (sheet D R) (doors D R) T (by positivity) hv
  exact ⟨w,hW,fun g=>LinearMap.congr_fun hE g⟩
def window (hc : c∈examinable R) (h:k≤D) : Sight D R →L[ℝ] Tensor.T E4 ℝ k := (reflect_cost hc h).choose
def mirror (hc : c∈examinable R) (h:k≤D) := (planL D k R).comp (window hc h)
lemma mirror_rule (hc : c∈examinable R) (h:k≤D) : ‖mirror hc h‖ ≤ ‖planL D k R‖*((k.factorial:ℝ)⁻¹*4^k) ∧ ∀ g:Exam D,mirror hc h (sheet D R g)=sheet D R (crop c g k) := by
  obtain ⟨hb,he⟩:= (reflect_cost hc h).choose_spec
  constructor
  · exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  intro g; unfold mirror window; rw [ContinuousLinearMap.comp_apply,he]; rfl

private lemma falling (g : Exam D) {χ : ℝ} (hχ:0≤χ) (h : k ≤ D) (hc : c ∈ examinable R) :
    ∀ j i, i+j=k → ∀ y, y∈ examinable R∩closedBall c χ → ‖iteratedFDeriv ℝ i (voided c g k).val y‖ ≤ (4:ℝ)^k*‖sheet D R g‖*χ^j := by
  intro j; induction j with
  | zero =>
    rintro i hi; rw [add_zero] at hi; subst i
    intro y hy; rw [(void_cost c g k k h).2 le_rfl,pow_zero,mul_one]; exact jet_budget D R g _ h ⟨_,hy.1⟩
  | succ j ih =>
    intro i hi y hy
    let F := iteratedFDeriv ℝ i (voided c g k).val
    let X := examinable R∩closedBall c χ
    have he x : DifferentiableAt ℝ F x := (ContDiff.differentiable_iteratedFDeriv (Nat.cast_lt.mpr (show i<D by omega)) (score D _)) x
    have hv : c∈X := ⟨hc,mem_closedBall_self hχ⟩
    have hx := ((grounds R).2.inter (convex_closedBall c χ)).norm_image_sub_le_of_norm_fderiv_le (f:=F) (fun x _=> he x) (fun x hx=> by rw [show ‖fderiv ℝ F x‖=_ from norm_fderiv_iteratedFDeriv]; exact ih (i+1) (by omega) x hx) hv hy
    have he' : F c=0 := (void_cost c g k i (by omega)).1 (by omega); rw [he',sub_zero] at hx
    have ht : ‖y-c‖≤χ := by simpa [dist_eq_norm] using (mem_closedBall.mp hy.2)
    rw [pow_succ,← mul_assoc]; exact hx.trans (mul_le_mul_of_nonneg_left ht (by positivity))

lemma inflated (D k : ℕ) (R : ℝ) (h : k ≤ D) : ∃ A:ℝ, 1≤A ∧ ∀ (c : E4) (δ : ℝ), Stays c δ R → ∀ g,
    ‖sheet D R (roll c δ (voided c g k))‖ ≤ A*δ^k * ‖sheet D R g‖ := by
  obtain ⟨χ,hχ,hh⟩:= affordable R
  refine ⟨(4:ℝ)^D*χ^k,one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hχ),fun c δ hm g=>?_⟩
  let q := voided c g k
  have hu := hm.nonneg; have hχ' :0≤χ := zero_le_one.trans hχ
  apply (bound D R (roll c δ q) (by positivity)).mpr; rintro ⟨⟨i,hi⟩,v⟩ x
  have hx : i≤D := by omega
  let y := c+δ•x.val
  have hy : y ∈ examinable R := hm.covers x.property
  change ‖iteratedFDeriv ℝ i (roll c δ q).val x.val (basis ∘ v)‖ ≤ _
  rw [facades _ _ _ i hx, smul_apply,norm_smul, Real.norm_of_nonneg (by positivity)]
  have he : ∀ (A : Tensor.T E4 ℝ i), ‖A (basis ∘ v)‖≤‖A‖ := fun A=>by
    simpa [comp_apply] using A.le_opNorm (basis ∘ v)
  grw [he]
  let w := ‖sheet D R g‖; have hw : 0 ≤ w := norm_nonneg _
  rcases le_total i k with hk|hk
  · have ha : y∈ examinable R∩closedBall c (δ*χ) := ⟨hy, by rw [mem_closedBall,dist_eq_norm]; unfold y; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hu]; exact mul_le_mul_of_nonneg_left (hh x.val x.property) hu⟩
    grw [falling (D:=D) g (show 0≤ δ*χ from by positivity) h hm.here (k-i) i (by omega) y ha]
    calc
      _ = (4:ℝ)^k*χ^(k-i)*δ^k*w := by rw [mul_pow]; rw [show δ^k=δ^i*δ^(k-i) from by rw [←pow_add,Nat.add_sub_of_le hk]]; ring
      _ ≤ _ := by gcongr <;> simp
  have hb : ‖iteratedFDeriv ℝ i q.val y‖ ≤ (4:ℝ)^i*‖sheet D R g‖ := by
    unfold q; rw [(void_cost _ _ _ _ hx).2 hk]; exact jet_budget D R g _ hx ⟨_,hy⟩
  grw [hb]
  change δ^i*((4:ℝ)^i*w)≤_
  have ht : (4:ℝ)^i≤4^D*χ^k := le_trans (pow_le_pow_right₀ (by norm_num) hx) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hχ))
  apply (mul_le_mul (pow_le_pow_of_le_one hu hm.short hk) (mul_le_mul_of_nonneg_right ht hw) (by positivity) (by positivity)).trans_eq; unfold w; ring

def padded (hm : Stays c δ R) (h:k≤D) := ∑ i:Fin k, δ^i.val • mirror hm.here (i.isLt.le.trans h)
lemma rolls (hm : Stays c δ R) (h:k≤D) (g : Exam D) : scroll c δ D hm (sheet D R (cache c g k))=padded hm h (sheet D R g) := by
  rw [(scroll_leaf ..).2]; change sheet D R (scoreL c δ D (cache ..)) = _
  rw [cache, map_sum,map_sum,padded,sum_apply]; apply Finset.sum_congr rfl; intro i _
  rw [smul_apply, (mirror_rule ..).2,← map_smul]; congr 1
  apply Subtype.ext; funext x
  change (crop c g i.val).val ((-c)+ (1:ℝ)•(c+δ•x))=_; rw [one_smul,neg_add_cancel_left]; exact homogeneous ..
lemma refrain (h:k≤D) (R:ℝ) : ∃ A:ℝ,1≤A ∧ ∀ (c : E4) (δ : ℝ) (hm : Stays c δ R), ‖scroll c δ D hm-padded hm h‖ ≤ A*δ^k := by
  obtain ⟨A,hA,hh⟩ := inflated D k R h
  refine ⟨A,hA,fun c δ hm=>ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (zero_le_one.trans hA) (pow_nonneg hm.nonneg _)) fun x=>?_⟩
  obtain ⟨g,rfl⟩:= doors D R x
  rw [sub_apply,← rolls hm h,← map_sub,←map_sub,(scroll_leaf c δ hm).2]; exact hh _ _ hm g
end YM.RG08.Scores.Pages
