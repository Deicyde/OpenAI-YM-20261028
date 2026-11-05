import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-!
# One common presentation price at the physical cutoff

No additive factor for repetitions at a marker in the derivative/sup price;
overlap still matters when charging these to output costs. Global envelope
on the full group also when flagged, not inferred from a matching estimate
only on a healthy stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Source Labels Overlay Marker Mix Function Filter MeasureTheory Finset Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {V : Type} {d N p : ℕ}

def columns (C : Family G) (N : ℕ) := ∏ i∈range N,(C.path.levels.params (i+1)).columns
lemma envelope_pos (C : Family G) {a : ℝ} (ha : 0<a) (N : ℕ) : 0 < envelope C a N := mul_pos
    (mul_pos ha (zero_lt_one.trans_le (C.path.levels.params N).columns_ge))
    (prod_pos fun i _ => zero_lt_one.trans_le (C.path.levels.params (i+1)).columns_ge)
private lemma col_one (C : Family G) (N : ℕ) : 1 ≤ columns C N := one_le_prod fun i _ => (C.path.levels.params (i+1)).columns_ge
private lemma col_le (C : Family G) (N : ℕ) : columns C N ≤ envelope C 1 N := by rw [envelope,one_mul]; exact le_mul_of_one_le_left (zero_le_one.trans (col_one ..)) (C.path.levels.params _).columns_ge

private lemma coeffSize_nn (z : C.label d) : 0 ≤ (C.labels.level d).coeffSize z := sum_nonneg (fun _ _ => norm_nonneg _)

/-- Include all intervening calibrations' certified column norms. No
cancellation between coordinates or different markers used. -/
theorem raw_size (h : C.Makes) (hi : C.ref d ≤ N) (z : C.label d) :
    let F := C.labels.level d
    F.coeffSize ((C.factory d N p).terminal.symm z) ≤ columns C N * F.coeffSize z := by
  intro F; let T := C.factory d N p; let v := T.terminal.symm z
  have hb := h.calibrated d N p hi
  have he {m : ℕ} (hm : C.ref d ≤ m) (hN : m ≤ N) : F.coeffSize (T.entries m v).x ≤ columns C m * F.coeffSize z := by
    induction m,hm using Nat.le_induction with
    | base => exact (congrArg F.coeffSize (C.normalized h hi _)).trans_le (le_mul_of_one_le_left (coeffSize_nn _) (col_one ..))
    | succ m hm ih =>
      refine (hb.back m hm hN v).trans ((mul_le_mul_of_nonneg_left (ih (by omega))
        (zero_le_one.trans (C.path.levels.params (m+1)).columns_ge)).trans_eq ?_)
      unfold columns; rw [prod_range_succ]; ring
  simpa [T, v, hb.bare_coord] using he hi le_rfl

def orient (C : Family G) (d : ℕ) (s : Signed) := ((C.labels.level d).act s.ortho).toContinuousLinearMap

def changes (C : Family G) (d : ℕ) := (Fintype.card (C.labels.level d).Index:ℝ)*(∑ s : Signed, ‖orient C d s‖)
lemma changes_nn (C : Family G) (d : ℕ) : 0 ≤ changes C d := mul_nonneg (by positivity) (sum_nonneg fun _ _ => norm_nonneg _)

def degree (C : Family G) (d : ℕ) := univ.sup fun i => ((C.labels.level d).grades i).2
lemma scaled_size (C : Family G) (z : C.label d) {t : ℝ} (ht : 0<t) (h : t ≤ 1) :
    (C.labels.level d).coeffSize (((C.labels.level d).scaled t⁻¹) z) ≤ t⁻¹^degree C d * (C.labels.level d).coeffSize z := by
  unfold Frame.coeffSize; rw [mul_sum]; apply sum_le_sum; intro i hi
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_inv₀ ht).2 h) (le_sup (f:=fun i => ((C.labels.level d).grades i).2) hi)) (norm_nonneg _)

lemma places_combined (C : Family G) (z : C.label d) {n : Side} (o : Site n) :
    (C.localSection d).places z o = ∑ i : (C.labels.level d).Index, z i • (C.localSection d).places (Pi.single i 1) o := by
  let D := C.localSection d
  let L : C.label d →ₗ[ℂ] Config G n → ℂ := {
    toFun z := D.places z o, map_smul' z f := funext fun U => congrFun (D.eval_linear.map_smul z f) _,
    map_add' z f := funext fun U => congrFun (D.eval_linear.map_add z f) _ }
  change L z = ∑ i : (C.labels.level d).Index, z i • L (Pi.single i 1)
  simp_rw [← map_smul,← map_sum]; congr; ext1 i; simp [Pi.single_apply]

lemma places_uniform (C : Family G) (d : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : Side) (o : Site n) (z : C.label d) (U : Config G n),
    ‖(C.localSection d).places z o U‖ ≤ K * (C.labels.level d).coeffSize z := by
  let D := C.localSection d
  choose k hk using fun i : (C.labels.level d).Index => isCompact_univ.exists_bound_of_continuousOn (D.continuous_evaluate (Pi.single i 1)).continuousOn
  have he (i) : 0 ≤ k i := (norm_nonneg _).trans (hk i 1 (Set.mem_univ _))
  refine ⟨∑ i,k i,sum_nonneg fun i _ => he i,fun n o z U => ?_⟩
  rw [places_combined, Finset.sum_apply,Frame.coeffSize,mul_sum]; apply (norm_sum_le ..).trans (sum_le_sum ?_); intro i _
  rw [Pi.smul_apply,norm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_right ((hk _ (expandAt o U) (Set.mem_univ _)).trans (single_le_sum (fun i _ => he i) (mem_univ _))) (norm_nonneg _)

lemma places_priced (h : C.Makes) (hi : C.ref d ≤ N) (o : Site (C.side N p)) (z : C.label d) :
    let B := (C.path.rep N p N).p
    let F := C.labels.level d
    let D := C.localSection d
    B.supBounds o (D.footprint o) (D.places z o) ((C.path.levels.params N).columns * F.coeffSize (F.scaled B.threshold z)) := by
  intro B F D
  have hh := h.priced d N p hi o
  rw [← (h.wilson.represents N p N le_rfl).vac] at hh
  rw [places_combined C, Frame.coeffSize, mul_sum]
  refine (regular_bound_sum _ _ _ fun i _ => ⟨regular_smul _ (hh i).1,?_⟩).2
  convert bound_smul (z i) (hh i).2 using 1
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg B.threshold_pos.le _)]
  dsimp only [B]; ring

lemma grain_big {n : Side} {X : Support n} {B : BudgetPoint} {F : Config G n → ℂ} {a b : ℝ} {o : Site n}
    (h : B.supBounds o X F a) (he : a * Real.exp 1 ≤ b) : grain B X F o b := by
  have hs : HasSum (fun i : ℕ => (1:ℝ) / i.factorial) (Real.exp 1) := by simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (1:ℝ)
  have hf := hs.summable.sum_le_tsum (range (B.order+1)) (fun i _ => by positivity)
  refine ⟨fun _ => a,fun _ => h.1,le_trans ?_ he,fun k hk hv U hu => h.2 U hu k hk hv⟩
  apply (le_trans _ (mul_le_mul_of_nonneg_left (hf.trans_eq hs.tsum_eq) h.1))
  rw [mul_sum]; exact sum_le_sum fun _ _ => by simp [div_eq_mul_inv]

namespace Probes
variable (Q : Probes C V N p)

lemma effective_price (i : V) : (C.labels.level (Q.d i)).coeffSize (Q.effective i) ≤ changes C (Q.d i)*‖Q.z i‖ := by
  have he : ‖Q.effective i‖ ≤ (∑ s, ‖orient C (Q.d i) s‖) * ‖Q.z i‖ := by
    have he : ‖Q.oriented i‖ ≤ _ := (orient C _ (Q.signed i)).le_opNorm (Q.z i)
    have hh := single_le_sum (s:=univ) (f:=fun s => ‖orient C (Q.d i) s‖) (fun i _ => norm_nonneg _) (mem_univ (Q.signed i))
    unfold effective; split <;> (try rw [norm_star]); all_goals exact he.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
  unfold Frame.coeffSize changes
  rw [mul_assoc, ← nsmul_eq_mul,← card_univ,← sum_const]; exact sum_le_sum (fun j _ => (norm_le_pi_norm _ _).trans he)

lemma priced_size (h : C.Makes) (i : V) (hi : C.ref (Q.d i) ≤ N) : (C.labels.level (Q.d i)).coeffSize (Q.costs i) ≤
    columns C N * (changes C (Q.d i) * ‖Q.z i‖) := (raw_size h hi _).trans (mul_le_mul_of_nonneg_left (Q.effective_price i) (zero_le_one.trans (col_one ..)))

lemma fraction_budget (h : C.Makes) (i : V) (hi : C.ref (Q.d i) ≤ N) : grain (C.path.rep N p N).p (Q.footprint i)
    (Q.fraction i) (Q.place i) ((changes C (Q.d i)*Real.exp 1) * ‖Q.z i‖ * envelope C 1 N) := by
  let B := (C.path.rep N p N).p; let F := C.labels.level (Q.d i)
  rw [Q.fraction_places h i hi,Q.footprint_eq h i]
  have hc : 0 ≤ (C.path.levels.params N).columns := zero_le_one.trans (C.path.levels.params N).columns_ge
  apply grain_big (places_priced h hi _ _); rw [F.scaled_inv B.threshold_pos.ne' (Q.costs i)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Q.priced_size h i hi) hc) (Real.exp_pos _).le).trans_eq (by unfold columns envelope; ring)
end Probes

lemma fraction_global (C : Family G) (d : ℕ) : ∃ K : ℝ,0 ≤ K ∧ ∀ {V N p} (Q : Probes C V N p), C.Makes → ∀ i : V, Q.d i ≤ d → C.ref (Q.d i) ≤ N →
    ∀ U : Config G (C.side N p), ‖Q.fraction i U‖ ≤ K*‖Q.z i‖*envelope C 1 N*((C.path.rep N p N).p.threshold)⁻¹^(degree C (Q.d i)) := by
  choose k hk hK using places_uniform C
  let K := ∑ j∈range (d+1), k j*changes C j
  have h (j : ℕ) : 0 ≤ k j * changes C j := mul_nonneg (hk _) (changes_nn ..)
  refine ⟨K,sum_nonneg fun j _ => h j,fun Q hC i hd hi U => ?_⟩
  rename_i V N p
  let t := ((C.path.rep N p N).p.threshold)⁻¹
  let L := t^(degree C (Q.d i))
  have ht : 0 ≤ L := pow_nonneg (inv_pos.mpr (C.path.rep N p N).p.threshold_pos).le _
  have hj : k (Q.d i) * changes C (Q.d i) ≤ K := single_le_sum (fun i _ => h i) (mem_range.mpr (Nat.lt_succ_of_le hd))
  rw [Q.fraction_places hC i hi]; apply (hK _ _ _ _ U).trans
  apply (mul_le_mul_of_nonneg_left (scaled_size C _ (C.path.rep N p N).p.threshold_pos (C.path.rep N p N).p.threshold_le) (hk _)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Q.priced_size hC i hi) ht) (hk _)).trans
  calc
    _ = ((k _ * changes C (Q.d i))*‖Q.z i‖ * columns C _) * L := by ring
    _ ≤ _ := by
      have := zero_le_one.trans (col_one C N); have h0 : 0 ≤ K := (h _).trans hj
      gcongr; exact col_le ..
end YM.Extra.Trajectories
