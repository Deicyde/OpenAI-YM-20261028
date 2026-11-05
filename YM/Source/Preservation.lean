import YM.Source.Insertion

/-! Check absolute summability in the marker expansion and
compose exact masses across levels (without limits). -/

set_option autoImplicit false
noncomputable section
namespace YM.Source
open Labels RG Lattice Wilson
open Set MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {d : ℕ} {F : Frame G d}

namespace Coefficient
variable {R : Rep G n} {H : Hol G} {o : Site n} {σ C Λ δ w : ℝ} {P : Coefficient F n}

theorem regular_series {a b : ℝ} (h : P.remBound o R a b) : Dominated (P.maskedTerm R) := by
  obtain ⟨A, B, _, _, _, _, ⟨k,h₁,h₂⟩,_⟩ := h
  refine ⟨_, h₁.2.1, fun i U ↦ le_trans (b := k i) ?_ (R.p.loMass _ _ (h₂ i).1)⟩
  by_cases hu : Healthy R.p.threshold (P.support i) U
  · rw [maskedTerm, masked_eq _ _ _ _ hu]
    exact (h₂ i).2 U hu [] (Nat.zero_le _) (by simp)
  rw [maskedTerm, masked_ne _ _ _ _ hu, norm_zero]; exact (h₂ i).1

theorem marked_series {a b : ℝ} (hr : R.Lawful σ C Λ δ w) (h : P.remBound o R a b) :
    Dominated (P.marked R) := by
  obtain ⟨z,hz,hZ⟩ := Activities.K_total hr.labels.boundK
  obtain ⟨X,Y, _, _, _, _, _, ⟨k,hk,hK⟩⟩ := h
  have H : Summable k := hk.2.1.of_nonneg_of_le (fun i => (hK i).1) fun i => R.p.loMass _ _ (hK i).1
  let p := k+z
  have hp (i) : 0 ≤ p i := add_nonneg (hK i).1 (hZ i).1
  have he : Summable fun i => 2 * p i := (H.add hz).mul_left _
  refine ⟨_,summable_finsetProd_of_summable_nonneg (fun i ↦ mul_nonneg (by norm_num) (hp i)) he, ?_⟩
  intro i V
  unfold marked; split
  · calc
      _ ≤ _ := norm_sum_le ..
      _ ≤ ∑ _j ∈ i, ∏ l ∈ i, p l := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [norm_mul,norm_prod]
        conv_rhs => rw [← Finset.mul_prod_erase i p hj]
        refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (hp _)
        · exact le_trans ((hK j).2 V) (le_add_of_nonneg_right (hZ _).1)
        refine Finset.prod_le_prod (fun l _ ↦ norm_nonneg _) fun l _ ↦ ?_
        rw [Complex.norm_real]
        exact le_trans ((hZ l).2 V) (le_add_of_nonneg_left (hK _).1)
      _ ≤ ∏ l ∈ i, (2 * p l) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const]
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun l _ ↦ hp l)
        exact_mod_cast (Nat.lt_two_pow_self (n := i.card)).le
  · rw [norm_zero]; exact Finset.prod_nonneg fun _ _ ↦ mul_nonneg (by norm_num) (hp _)

private lemma plus {f g : Config G n → ℂ} (H : Envelope f) (K : Envelope g) : Envelope (fun x => f x + g x) := by
  obtain ⟨C, hc⟩ := H.cost
  obtain ⟨D, hd⟩ := K.cost
  exact ⟨H.meas.add K.meas, C+D, fun x ↦ (norm_add_le ..).trans (add_le_add (hc _) (hd _))⟩
private lemma times {f g : Config G n → ℂ} (H : Envelope f) (K : Envelope g) : Envelope (fun x => f x * g x) := by
  obtain ⟨C,hc⟩ := H.cost
  obtain ⟨D,hd⟩ := K.cost
  exact ⟨H.meas.mul K.meas, C*D, fun x ↦ (norm_mul_le ..).trans
    (mul_le_mul (hc x) (hd x) (norm_nonneg _) ((norm_nonneg _).trans (hc x)))⟩
private lemma ofReal {f : Config G n → ℝ} (H : Envelope f) : Envelope fun x => (f x : ℂ) := by
  obtain ⟨C,hc⟩ := H.cost
  exact ⟨Complex.continuous_ofReal.measurable.comp H.meas, C, fun x ↦ by simp only [Complex.norm_real]; exact hc _⟩

theorem envelope {A B : ℝ} (s : SectionData F) (hr : R.Lawful σ C Λ δ w) (h : P.remBound o R A B)
    (he : P.Format o H R) : Envelope (P.density o s R) := by
  have ht (v : F.Coeff) : Envelope (masked R.p.threshold (s.footprint o) (s.places v o)) := by
    refine ⟨masked_measurable _ _ _ (s.continuous_places ..).measurable,?_⟩
    obtain ⟨p,hp⟩ := isCompact_range (s.continuous_places v o).norm |>.bddAbove
    refine ⟨max p 0, fun U ↦ ?_⟩
    by_cases hx : Healthy R.p.threshold (s.footprint o) U
    · rw [masked_eq _ _ _ _ hx]; exact le_trans (hp ⟨U,rfl⟩) (le_max_left _ _)
    rw [masked_ne _ _ _ _ hx,norm_zero]; exact le_max_right _ _
  have hg : Envelope fun x : Config G n => P.x 0 := ⟨measurable_const, _, fun _ ↦ le_rfl⟩
  refine plus (times (ofReal (R.envelope hr))
    (plus (plus hg (ht _)) ⟨Measurable.tsum ?_, (regular_series h).bound⟩))
    (times (ofReal (R.exponentEnv hr).exp) ⟨Measurable.tsum ?_, (marked_series hr h).bound⟩)
  · intro i; exact masked_measurable _ _ (P.regular i) (he.smooth i).borel
  intro i; classical
  unfold marked
  refine Measurable.ite (R.activities.admissible_borel R.p i) ?_ measurable_const
  refine Finset.measurable_fun_sum _ fun j _ ↦ (he.borel j).mul ?_
  refine Finset.measurable_fun_prod _ fun l _ ↦ Complex.continuous_ofReal.measurable.comp (hr.labels.forced.meas l)
end Coefficient

namespace TransferData
variable {H : History G} {A : Hol G} {C : SectionData F} {N p r : ℕ} {T : TransferData F H N p}

theorem cylinder_cont (T : TransferData F H N p) (C : SectionData F) (x : Site (H.S.side N p))
    (v : F.Coeff) : Continuous (T.cylinder C v x) :=
  continuous_const.smul (C.continuous_places _ _)

theorem density_int (hc : H.Selected) (h : T.Based A C r) (v : F.Coeff) (m) (hr : r ≤ m) (hm : m ≤ N) :
    Integrable ((T.entries m v).density 0 C (H.rep N p m)) (prior G (H.S.side m p)) := by
  have he := Coefficient.envelope C (hc.represents N p m hm).good (h.cap m hr hm v) (h.format m hr hm v)
  obtain ⟨K,hk⟩ := he.cost
  exact Integrable.of_bound he.meas.aestronglyMeasurable K (Eventually.of_forall hk)

theorem integral_marked (hc : H.Selected) (h : T.Based A C r) (v : F.Coeff) (m) (hr : r ≤ m) (hm : m ≤ N) :
    (∫ U, (T.entries m (T.terminal.symm v)).density 0 C (H.rep N p m) U ∂prior G (H.S.side m p)) =
      (H.S.a m : ℂ)^d * (partition G (H.S.side N p) (H.β N p N) : ℂ) *
        moment (H.β N p N) (T.cylinder C v 0) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    have hi := continuous_integrable (H.β N p N) (cylinder_cont T C 0 v)
    rw [moment_formula _ _ hi]
    have hz : (partition G (H.S.side N p) (H.β N p N) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
    simp_rw [h.encode, (hc.starts N p).2, mul_assoc]
    rw [integral_const_mul]; simp [cylinder, hz]
  | of_succ k hk Hk =>
    simp_rw [h.unnormalized k hr hk]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, StepData.push_integral (H.levels.transition_mass ..) _
      (density_int hc h _ _ (hr.trans k.le_succ) hk), Hk (hr.trans k.le_succ), H.S.a_step]
    have he := (H.S.block k).property.ne'
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, mul_comm ((H.S.block k).val : ℂ), div_mul_cancel₀ _ (by exact_mod_cast he)]
end TransferData
end YM.Source
