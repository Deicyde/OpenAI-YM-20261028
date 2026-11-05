import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Marginal
import YM.PREC.Pred

/-!
# Ratio/trigger/score moment on their one (possibly conditional) marginal

`Moments.purchased`: allow the endpoint exponential at the indicated
aperture, on TOP of any given fixed-m degree cost in *all* the Gaussian
variables in the component. Price has only polynomial growth in the total
number read (with all colors counted); exponential factors are just per
endpoint coordinate. Uses all coordinates (in particular any harmonic
variables), counting square though `Vec` has function-space sup norm.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian.Moments
open Function Filter Lattice RG Wilson Next.SectorChange Next.SectorChange.Gaussian
open MeasureTheory ProbabilityTheory WithLp Matrix Finset
open scoped Topology BigOperators RealInnerProductSpace ENNReal

variable {ι : Type}

def load (s : Finset ι) (x : Vec ι) : ℝ := ∑ i∈s, x i ^ 2

lemma load_nonneg (s : Finset ι) (x : Vec ι) : 0 ≤ load s x := sum_nonneg fun _ _ => sq_nonneg _
lemma load_le {s t : Finset ι} (x : Vec ι) (h : s ⊆ t) : load s x ≤ load t x :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

variable [Fintype ι]

def powers (x : Vec ι) : ℝ := 1+load univ x
lemma load_square (x : Vec ι) : load univ x = dotProduct x x := by simp only [load,dotProduct,sq]

lemma grows (x : Vec ι) : 1 ≤ powers x := le_add_of_nonneg_right (load_nonneg _ _)
lemma powers_pos (x : Vec ι) : 0 < powers x := zero_lt_one.trans_le (grows x)

omit [Fintype ι] in
@[fun_prop] lemma load_cont (s : Finset ι) : Continuous (load s) := by unfold load; fun_prop
@[fun_prop] lemma powers_cont : Continuous (powers (ι:=ι)) := by unfold powers; fun_prop

variable [DecidableEq ι] {C : Next.SectorChange.Gaussian.Table ι}

lemma charged (h : C.PosDef) (f : Vec ι → ℝ) :
    (Integrable f (cloud C) ↔ Integrable (fun x => ratio C x*f x)) ∧
      (∫ x,f x ∂cloud C) = ∫ x,ratio C x * f x := by
  rw [cloud_formula h]
  have he : Measurable (fun x => ENNReal.ofReal (ratio C x)) := (measurable_ratio _).ennreal_ofReal
  have ht : ∀ᵐ x ∂volume, ENNReal.ofReal (ratio C x)<⊤ := Eventually.of_forall fun x => by simp
  rw [integral_withDensity_eq_integral_toReal_smul he ht,
    integrable_withDensity_iff_integrable_smul' he ht]
  simp_rw [ENNReal.toReal_ofReal (ratio_pos h _).le,smul_eq_mul]
  simp

lemma charged_one (h : C.PosDef) : Integrable (ratio C) ∧ ∫ x, ratio C x = 1 := by
  have hl := ((charged h (fun _ => 1)).1.mp (integrable_const (1:ℝ)))
  have hp := (charged h (fun _ => 1)).2
  simpa using And.intro hl hp.symm

lemma full_room (h : C.PosDef) {r : ℝ} (hv : FreeResolvent.Gap C⁻¹ r) :
    let f := fun x : Vec ι => Real.exp (r/4*load univ x)
    Integrable f (cloud C) ∧ (∫ x, f x ∂cloud C) ≤ 2^Fintype.card ι := by
  let L := (2 : ℝ) • C
  intro f
  have hl : L.PosDef := h.smul (by norm_num : (0:ℝ)<2)
  let M : ℝ := 2^Fintype.card ι
  have hm : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hh : L⁻¹=(1/2:ℝ) • C⁻¹ := by
    apply Matrix.inv_eq_left_inv; unfold L
    rw [Matrix.smul_mul,Matrix.mul_smul, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det C |>.mp h.isUnit), smul_smul]; norm_num
  have ht (x) : ratio C x*f x ≤ M*ratio L x := by
    have he i := hv.lower i
    have hm' : coat L ≤ M*coat C := by
      simp only [coat,L,det_smul]; change _ * Real.sqrt (M*_ ) ≤ _
      rw [mul_left_comm M,Real.sqrt_mul (zero_le_one.trans hm)]
      have hh' : Real.sqrt M ≤ M := by nlinarith only [hm,Real.sq_sqrt (zero_le_one.trans hm),Real.sqrt_nonneg M]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh' (Real.sqrt_nonneg _)) dome_pos.le
    have hV : force L x = force C x / 2 := by
      rw [force,hh,smul_mulVec,dotProduct_smul, force,smul_eq_mul]; ring
    unfold ratio f
    rw [mul_assoc,← Real.exp_add,load_square,hV,← mul_assoc]
    apply mul_le_mul
    · have hp := coat_pos h; have hx := coat_pos hl
      rw [← div_eq_mul_inv M,← one_div, div_le_div_iff₀ hp hx]; simpa
    · apply Real.exp_monotone; unfold force; linarith only [he x]
    · exact (Real.exp_pos _).le
    exact mul_nonneg (zero_le_one.trans hm) (inv_nonneg.mpr (coat_pos hl).le)
  have hf : Measurable f := by
    unfold f; fun_prop
  have hi := (charged_one hl).1.const_mul M
  have hx : Integrable (fun x => ratio C x*f x) := hi.mono' (((measurable_ratio _).mul hf).aestronglyMeasurable)
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (mul_pos (ratio_pos h x) (Real.exp_pos _)).le]; exact ht x)
  refine ⟨(charged h f).1.mpr hx, (charged h f).2.trans_le ?_⟩
  exact (integral_mono hx hi ht).trans_eq (by rw [integral_const_mul,(charged_one hl).2,mul_one])

lemma corner_room (X : Finset ι) (h : C.PosDef) {Q : ℝ} (hq : 0 < Q) (he : Peak C Q) :
    let f := fun x => Real.exp (Q⁻¹/4*load X x)
    Integrable f (cloud C) ∧ (∫ x, f x ∂cloud C) ≤ 2^X.card := by
  intro f
  let e := Function.Embedding.subtype (fun i => i∈X)
  let A : Next.SectorChange.Gaussian.Table X := C.submatrix ((↑):X→ι) ((↑):X→ι)
  have hh : A.PosDef := h.submatrix Subtype.val_injective
  let F := fun x : Vec X => Real.exp (Q⁻¹/4*load univ x)
  obtain ⟨hi,hl⟩ := full_room hh ((he.project e).compress_gap hh hq)
  let g := fun x : Vec ι => (x ∘ ((↑):X→ι))
  have hz : f = F ∘ g := by
    funext x; unfold f F g load
    simp only [Function.comp_apply,Finset.sum_coe_sort X (fun i => x i ^ 2)]
  have hp : MeasurePreserving g (cloud C) (cloud A) := margin_law ((↑):X→ι) h.posSemidef
  rw [hz]
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have hx := integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hi.aestronglyMeasurable : AEStronglyMeasurable F ((cloud C).map g))
  rw [hp.map_eq] at hx
  change (∫ x, F (g x) ∂cloud C) ≤ _; rw [← hx]
  simpa using! hl

/-- At rank m. `overlap` weights do not enter this polynomial payoff. -/
def inflate (m : ℕ) (u : ℝ) : ℝ := (1+m/u)^m

lemma inflate_ge (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : 1 ≤ inflate m u :=
  one_le_pow₀ (le_add_of_nonneg_right (by positivity))

lemma inflates (m : ℕ) {u x : ℝ} (hx : 0 ≤ x) (hu : 0 < u) :
    (1+x)^m ≤ inflate m u * Real.exp (u*x) := by
  by_cases hm : m=0
  · simpa [hm,inflate] using Real.one_le_exp (mul_nonneg hu.le hx)
  have hl : 0 < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  let s := u / m
  have ht : 0 ≤ s*x := by unfold s; positivity
  calc
    _ ≤ ((1+m/u)*Real.exp (s*x))^m := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have he : s * (m/u) = 1 := by unfold s; field_simp
      have hh := Real.add_one_le_exp (s*x)
      calc
        _ ≤ 1*Real.exp (s*x)+(m/u)*Real.exp (s*x) := by
          apply add_le_add
          · linarith
          calc
            _ = (m/u)*(s*x) := by rw [← mul_assoc,mul_comm (m/u),he,one_mul]
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hh]) (by positivity)
        _ = _ := by ring
    _ = _ := by
      unfold inflate; rw [mul_pow,← Real.exp_nat_mul, show ↑m*(s*x)=u*x by unfold s; field_simp]

/-- Value (or order-cost envelope) integrated on the one centered marginal. -/
def slopeEnvelope (X : Finset ι) (Q : ℝ) (m : ℕ) (x : Vec ι) : ℝ :=
  powers x ^ m * Real.exp (Q⁻¹/8 * load X x)

omit [DecidableEq ι] in
@[fun_prop] lemma slopeEnvelope_meas (X : Finset ι) (Q : ℝ) (m : ℕ) : Measurable (slopeEnvelope X Q m) := by
  apply Continuous.measurable; unfold slopeEnvelope; fun_prop
omit [DecidableEq ι] in
lemma slopeEnvelope_pos (X : Finset ι) (Q : ℝ) (m : ℕ) (x : Vec ι) : 0 < slopeEnvelope X Q m x := by
  unfold slopeEnvelope; have hh := powers_pos x; positivity

private def bump (d m : ℕ) (Q : ℝ) := (1+(d:ℝ))^m * inflate m (Q⁻¹/8)

def meter (d K : ℕ) (Q : ℝ) (m : ℕ) := (1+d:ℝ)*((1+(d:ℝ))^m * inflate m (Q⁻¹/8)) * 2^(K+1)

private lemma peak_score [Nonempty ι] (X : Finset ι) {Q : ℝ} (hq : 0 < Q) (m : ℕ) (x : Vec ι) :
    slopeEnvelope X Q m x ≤ ∑ i : ι, bump (Fintype.card ι) m Q * Real.exp (Q⁻¹/4 * load (insert i X) x) := by
  let d := Fintype.card ι
  let b := bump d m Q
  let y := fun i => x i ^2
  obtain ⟨j,-,hj⟩ := Finset.exists_max_image univ y univ_nonempty
  have hu : powers x ≤ (1+(d:ℝ))*(1+y j) := by
    have h : load univ x ≤ (d:ℝ)*y j := calc
      _ ≤ ∑ _i : ι, y j := Finset.sum_le_sum (fun i hi => hj i hi)
      _ = _ := by simp [d]
    unfold powers
    have he : 0 ≤ y j := sq_nonneg _; have hp : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
    linarith only [h,hp,he]
  let l := insert j X
  have hs : y j ≤ load l x := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (mem_insert_self _ _)
  have hx := load_le x (subset_insert j X)
  let v := Q⁻¹/8
  have hv : 0 < v := by unfold v; positivity
  have he : 0 ≤ b := mul_nonneg (pow_nonneg (by positivity) _) (zero_le_one.trans (inflate_ge m hv.le))
  have hi : powers x^m ≤ b*Real.exp (v*y j) := by
    refine (pow_le_pow_left₀ (powers_pos _).le hu m).trans ?_
    unfold b bump; rw [mul_pow,mul_assoc]
    exact mul_le_mul_of_nonneg_left (inflates m (sq_nonneg _) hv) (by positivity)
  calc
    _ ≤ b*Real.exp (v*y j)*Real.exp (v*load X x) := mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le
    _ ≤ b*Real.exp (Q⁻¹/4 * load l x) := by
      rw [mul_assoc, ← Real.exp_add, show Q⁻¹/4 = v + v by unfold v; ring]
      refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) he
      linarith only [mul_le_mul_of_nonneg_left hs hv.le, mul_le_mul_of_nonneg_left hx hv.le]
    _ ≤ _ := Finset.single_le_sum (fun i _ => mul_nonneg (b:=Real.exp (Q⁻¹/4 * load (insert i X) x)) he (Real.exp_pos _).le) (mem_univ j)

theorem purchased (X : Finset ι) {Q : ℝ} (hq : 0 < Q) (h : C.PosDef) (he : Peak C Q) (m : ℕ) :
    Integrable (slopeEnvelope X Q m) (cloud C) ∧ (∫ x, slopeEnvelope X Q m x ∂cloud C) ≤
      meter (Fintype.card ι) X.card Q m := by
  rcases isEmpty_or_nonempty ι with h0|h0
  · have hE : slopeEnvelope X Q m = fun _ => 1 := by have he : X=∅ := by ext i; exact isEmptyElim i
                                                     funext x; simp [he,slopeEnvelope,powers,load]
    rw [hE]
    simp only [integrable_const, integral_const, probReal_univ, smul_eq_mul, one_mul,
      Fintype.card_eq_zero,true_and,meter,Nat.cast_zero,add_zero,one_pow,one_mul]
    exact one_le_mul_of_one_le_of_one_le (inflate_ge _ (by positivity)) (one_le_pow₀ (by norm_num))
  let d := Fintype.card ι
  let b := bump d m Q
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg (by positivity) _) (zero_le_one.trans (inflate_ge m (by positivity)))
  let f (j : ι) (x : Vec ι) := Real.exp (Q⁻¹/4 * load (insert j X) x)
  let g (j : ι) (x : Vec ι) := b * f j x
  let L (x : Vec ι) := ∑ j, g j x
  have hx j := corner_room (insert j X) h hq he
  have hg (j) : Integrable (g j) (cloud C) := (hx j).1.const_mul _
  have hL : Integrable L (cloud C) := integrable_finsetSum _ fun j _ => hg j
  have hs (x : Vec ι) : slopeEnvelope X Q m x ≤ L x := peak_score X hq m x
  have hf : Integrable (slopeEnvelope X Q m) (cloud C) := hL.mono' (slopeEnvelope_meas ..).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (slopeEnvelope_pos ..).le]; exact hs x)
  refine ⟨hf,(integral_mono hf hL hs).trans ?_⟩
  unfold L; rw [integral_finsetSum _ fun j _ => hg j]
  calc
    _ ≤ ∑ _j : ι, b * 2^(X.card+1) := Finset.sum_le_sum fun j _ => by
      unfold g; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left
        ((hx j).2.trans (pow_le_pow_right₀ (by norm_num) (Finset.card_insert_le _ _))) hb
    _ = d * b * 2^(X.card+1) := by simp [d, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity : (0:ℝ)≤1)) hb) (by positivity)
end YM.AnalyticBridge.LocalGaussian.Moments
