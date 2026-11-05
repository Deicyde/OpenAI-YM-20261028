import YM.Next.EXTRACTION.Base
import YM.Next.FOUNDATIONS.Regular
import YM.Work.H03

/-!
`C.factory` entries, including shifts used without recalibrating. Translate
regular jets *before* masking. Uniform prices on arbitrary finite collections
of copies of bounded labels at any queried weights. O itself can be complex
and always uses the terminal inverse of this N,p, including off-center. This
part consumes `C.Makes`, does not extend the one-source transfer identity to
mixtures on its own.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Filter Function Lattice RG Wilson Source Overlay Marker Labels Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side}

namespace BasisCost

def slots (F : Labels.Frame G d) : ℕ := Finset.univ.sup fun i => (F.grades i).2

def extent (T : SectionData F) : ℕ := T.stencil.sup fun z => univ.sup fun i => (z i).natAbs

lemma small_footprint (T : SectionData F) (o : Site n) {B : ℕ} (he : extent T ≤ B) :
    coverNumber B (T.footprint o) ≤ 1 := by
  have hx : T.footprint o ⊆ halo (0+B) {o} := by
    intro x hx; obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    apply halo_spec.mpr; refine ⟨_,mem_singleton_self _,?_⟩
    rw [separation_comm,separation, add_sub_cancel_right]
    apply Finset.sup_le; intro i _
    exact (Corona.lap ..).trans ((le_sup_of_le hz (le_sup (f:=fun i => (z i).natAbs) (mem_univ i)) : _ ≤ extent T).trans (by change extent T ≤ _; omega))
  rw [← card_singleton o]; apply Corona.list_cost; refine ⟨by simpa only [zero_add] using hx, Corona.ship_halo _ ?_⟩
  intro x hx y hy; obtain rfl := mem_singleton.mp hx; obtain rfl := mem_singleton.mp hy; exact .refl

lemma coeff_nonneg (v : F.Coeff) : 0 ≤ F.coeffSize v := sum_nonneg fun _ _ => norm_nonneg _

lemma coeff_le (v : F.Coeff) : F.coeffSize (F.core v) ≤ F.coeffSize v := by
  apply sum_le_sum; intro i (_ : i∈univ)
  change ‖update v 0 0 i‖ ≤ ‖v i‖
  by_cases h : i=0 <;> simp [h]

lemma coord_le (v : F.Coeff) (i) : ‖v i‖ ≤ F.coeffSize v := single_le_sum (fun _ _ => norm_nonneg _) (mem_univ i)

lemma placed_columns (T : SectionData F) (v : F.Coeff) (o : Site n) :
    T.places v o = ∑ i : F.Index, v i • T.places (Pi.single i 1) o := by
  let L : F.Coeff →ₗ[ℂ] Config G n → ℂ := {
    toFun v := T.places v o
    map_add' _ _ := funext fun U => congr_fun (T.eval_linear.map_add ..) (expandAt o U)
    map_smul' _ _ := funext fun U => congr_fun (T.eval_linear.map_smul ..) (expandAt o U) }
  change L v = ∑ i, v i • L _
  simp_rw [← map_smul, ← map_sum]; congr 1
  ext1 i; simp [Pi.single_apply]

lemma exists_price (T : SectionData F) : ∃ C : ℝ, 1 ≤ C ∧ ∀ i : F.Index,
    ∀ n : Side, ∀ o : Site n, ∀ U : Config G n, ‖T.places (Pi.single i 1) o U‖ ≤ C := by
  choose b hb using fun i : F.Index => ((isCompact_range (T.continuous_evaluate (Pi.single i 1)).norm).bddAbove).exists_ge (1:ℝ)
  refine ⟨1+∑ i, |b i|, le_add_of_nonneg_right (sum_nonneg fun i _ => abs_nonneg _),fun i n o U => ?_⟩
  have he : b i ≤ ∑ j, |b j| := (le_abs_self _).trans (single_le_sum (f:=fun j => |b j|) (fun _ _ => abs_nonneg _) (mem_univ i))
  exact ((hb i).2 _ ⟨expandAt o U,rfl⟩).trans (he.trans (le_add_of_nonneg_left zero_le_one))

def price (T : SectionData F) : ℝ := (exists_price T).choose
lemma price_pos (T : SectionData F) : 1 ≤ price T := (exists_price T).choose_spec.1

lemma full (T : SectionData F) (v : F.Coeff) (o : Site n) (U : Config G n) :
    ‖T.places v o U‖ ≤ price T * F.coeffSize v := by
  rw [placed_columns, Finset.sum_apply,Frame.coeffSize,mul_sum]
  refine (norm_sum_le ..).trans (sum_le_sum fun i _ => ?_)
  rw [Pi.smul_apply, norm_smul, mul_comm (price T)]
  exact mul_le_mul_of_nonneg_left ((exists_price T).choose_spec.2 i n o U) (norm_nonneg _)

lemma full_scaled (T : SectionData F) (v : F.Coeff) (o : Site n) {t g : ℝ} (hg : 0<g)
    (hgt : g ≤ t) (h : g ≤ 1) (U : Config G n) :
    ‖T.places (F.scaled t⁻¹ v) o U‖ ≤ price T * (g⁻¹)^slots F * F.coeffSize v := by
  apply (full ..).trans; rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (price_pos T))
  rw [Frame.coeffSize,Frame.coeffSize,mul_sum]; refine sum_le_sum fun i _ => ?_
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (hg.trans_le hgt).le) _)]
  refine mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_nonneg.mpr (hg.trans_le hgt).le) (inv_anti₀ hg hgt) _).trans ?_)
    (norm_nonneg _)
  exact pow_le_pow_right₀ ((one_le_inv₀ hg).mpr h) (le_sup (f:=fun i => (F.grades i).2) (mem_univ i))

/-- Cost on an actual BudgetPoint, using `Family.Makes.priced` if supplied,
with the genuine linear-combination derivative theorem (incl. equality at a
flag boundary). -/
lemma analytic (T : SectionData F) (P : BudgetPoint) (v : F.Coeff) (o : Site n) {C : ℝ}
    (hc : ∀ i : F.Index, P.Regular (T.footprint o) (T.places (Pi.single i 1) o) ∧
      P.supBounds o (T.footprint o) (T.places (Pi.single i 1) o) (C * P.threshold^(F.grades i).2)) :
    P.Regular (T.footprint o) (T.places (F.scaled P.threshold⁻¹ v) o) ∧
      P.supBounds o (T.footprint o) (T.places (F.scaled P.threshold⁻¹ v) o) (C * F.coeffSize v) := by
  nth_rw 3 [← F.scaled_inv P.threshold_pos.ne' v]
  let w := F.scaled P.threshold⁻¹ v
  have hu (i) : C * ‖F.scaled P.threshold w i‖ = ‖w i‖ * (C * P.threshold^(F.grades i).2) := by
    rw [F.scaled_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg P.threshold_pos.le _)]
    ring
  rw [placed_columns T w o,Frame.coeffSize,mul_sum]; change _ ∧ P.supBounds o _ _ (∑ i, C * ‖F.scaled P.threshold w i‖); simp_rw [hu]
  exact Next.Foundations.regular_bound_sum _ _ _ fun i _ =>
    ⟨Next.Foundations.regular_smul _ (hc i).1,Next.Foundations.bound_smul _ (hc i).2⟩

end BasisCost

namespace Relocate

def shift (y : Site n) (X : Support n) := X.image (· + y)

theorem halo_shift (y : Site n) (X : Support n) (B : ℕ) : halo B (shift y X) = shift y (halo B X) := by
  ext x
  constructor
  · intro h; obtain ⟨z,hz,he⟩ := halo_spec.mp h; obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨x-y,halo_spec.mpr ⟨w,hw,?_⟩,sub_add_cancel ..⟩
    simpa only [← separation_translate w (x-y) y, sub_add_cancel]
  intro h; obtain ⟨w,hw,rfl⟩ := mem_image.mp h; obtain ⟨z,hz,he⟩ := halo_spec.mp hw
  exact halo_spec.mpr ⟨z+y,mem_image_of_mem _ hz,(separation_translate ..).trans_le he⟩

theorem cover_shift (y : Site n) (X : Support n) (B : ℕ) : coverNumber B (shift y X) ≤ coverNumber B X := by
  obtain ⟨D,⟨hD,h⟩,hh⟩ := coverNumber_realized B X; rw [← hh]
  apply le_trans _ (card_image_le (f:=(·+y)) (s:=D))
  apply Corona.list_cost B (D:=shift y D); rw [covers,halo_shift]
  refine ⟨image_subset_image hD,fun i hi j hj => ?_⟩
  obtain ⟨i,hI,rfl⟩ := mem_image.mp hi; obtain ⟨j,hJ,rfl⟩ := mem_image.mp hj
  have he := h i hI j hJ
  clear hi hj hJ hI
  induction he with
  | refl => exact .refl
  | tail _ he ih => exact .tail ih ⟨mem_image_of_mem _ he.1, mem_image_of_mem _ he.2.1, (separation_translate ..).trans_le he.2.2⟩

theorem healthy_shift {U : Config G n} {y : Site n} {t : ℝ} {X : Support n}
    (h : Healthy t (shift y X) U) : Healthy t X (translate y U) := by
  have ht := Work.H03.flags_send 1 y t U
  rw [pull_one] at ht
  refine disjoint_left.mpr fun i hi hb => disjoint_left.mp h (mem_image_of_mem _ hi) ?_
  rw [← ht]; exact mem_image.mpr ⟨_,hb,by simp [affine]⟩

def along (y : Site n) (a : Directions G n) : Directions G n := fun e => a (e.1+y,e.2)

theorem jets (y : Site n) (f : Config G n → ℂ) (l : List (Directions G n)) (U : Config G n) :
    leftDerivs (f ∘ translate y) l U = leftDerivs f (l.map (along y)) (translate y U) := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih => simp only [leftDerivs,List.map_cons,ih]; rfl

theorem sup_translate {P : BudgetPoint} {o y : Site n} {f : Config G n → ℂ} {X : Support n} {a : ℝ}
    (h : P.supBounds o X f a) : P.supBounds (o+y) (shift y X) (f ∘ translate y) a := by
  refine ⟨h.1,fun U hu l hl hd => ?_⟩
  rw [jets]; refine h.2 _ (healthy_shift hu) _ (by simpa only [List.length_map]) ?_
  intro A hA e; obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
  exact (hd B hB (e.1+y,e.2)).trans_eq (by simp)

end Relocate

variable (C : Family G) (N p : ℕ) (m : ℕ)

abbrev point := C.path.levels.budget m
abbrev col := (C.path.levels.params m).columns
abbrev gHat := C.path.levels.clock.hatCoupling m
abbrev divisor := Real.sqrt (C.path.levels.clock.forcedAllowance m)
abbrev coord (v : C.label d) := (C.factory d N p).entries m ((C.factory d N p).terminal.symm v)

def wallet := ∏ i∈Finset.range m,col C (i+1)

theorem col_ge : 1 ≤ col C m := (C.path.levels.params m).columns_ge
theorem wallet_ge : 1 ≤ wallet C m := one_le_prod fun i _ => col_ge C (i+1)
theorem gHat_pos : 0 < gHat C m := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed m)))
theorem gHat_le_one : gHat C m ≤ 1 := inv_le_one_of_one_le₀ (Real.le_sqrt_of_sq_le (by simpa using (C.path.levels.fits.delayed m).le))
theorem gHat_le : gHat C m ≤ (point C m).threshold := le_mul_of_one_le_right (gHat_pos C m).le (Real.one_le_exp (sq_nonneg _))
theorem divisor_pos : 0<divisor C m := Real.sqrt_pos.mpr (Real.exp_pos _)
theorem divisor_le : divisor C m ≤ 1 := Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _)))

theorem width_pos {a : ℝ} (h : 0<a) (k : ℕ) : 0 < Mix.width C a k m := div_pos (pow_pos (gHat_pos C m) _)
    (mul_pos (mul_pos h (zero_lt_one.trans_le (col_ge C m))) (zero_lt_one.trans_le (wallet_ge C m)))

theorem coord_bound (H : C.Makes) (v : C.label d) (hm : C.ref d ≤ m) (hm' : m ≤ N) :
    (C.labels.level d).coeffSize (coord C N p m v).x ≤ wallet C m * (C.labels.level d).coeffSize v := by
  induction m,hm using Nat.le_induction with
  | base => rw [H.calibrated d N p hm' |>.reads,LinearEquiv.apply_symm_apply]
            exact le_mul_of_one_le_left (BasisCost.coeff_nonneg _) (wallet_ge ..)
  | succ m hm ih =>
    rw [wallet,prod_range_succ,mul_comm _ (col C (m+1)),mul_assoc]
    refine ((H.calibrated d N p (hm.trans (by omega : m≤N))).back m hm hm' _).trans ?_
    exact mul_le_mul_of_nonneg_left (ih (by omega : m≤N)) (zero_le_one.trans (col_ge ..))

theorem pays_coord {a : ℝ} (ha : 0 < a) (k : ℕ) (H : C.Makes) (v : C.label d) (hv : (C.labels.level d).coeffSize v ≤ a)
    (hm : C.ref d ≤ m) (hm' : m ≤ N) :
    Mix.width C a k m * (col C m * (C.labels.level d).coeffSize (coord C N p m v).x) ≤ (gHat C m)^k := by
  have ht := (coord_bound C N p m H v hm hm').trans (mul_le_mul_of_nonneg_left hv (zero_le_one.trans (wallet_ge ..)))
  have he := (width_pos C m ha k).le
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (zero_le_one.trans (col_ge ..))) he).trans_eq ?_
  rw [show col C m * (wallet C m * a) = Mix.envelope C a m by unfold Mix.envelope wallet; ring]
  exact div_mul_cancel₀ _ (mul_pos (mul_pos ha (zero_lt_one.trans_le (col_ge ..))) (zero_lt_one.trans_le (wallet_ge ..))).ne'

abbrev canon (o : Site (C.side m p)) (v : C.label d) := (C.localSection d).places ((C.labels.level d).scaled (point C m).threshold⁻¹
    ((C.labels.level d).core (coord C N p m v).x)) o







end YM.Extra.Multi
