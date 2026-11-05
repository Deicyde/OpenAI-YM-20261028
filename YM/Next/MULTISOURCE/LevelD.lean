import YM.Next.MULTISOURCE.Tournesol


/-! Control jet values (these ones may use volume prices!). -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice Marker Finset Filter MeasureTheory Desk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
variable {P : Rep G n}

lemma personal {c : ℝ} {W : Support n} {F : Pulse G n} {X : BudgetPoint} {r κ : ℝ} (h : Credit X r κ W F c) :
    GaugeInvariant F.1 ∧ (∀ i, GaugeInvariant (F.2 i)) ∧ (∀ U, ‖F.1 U‖ ≤ c+c) ∧ ∀ i U, ‖F.2 i U‖ ≤ κ*c := by
  obtain ⟨he,hr,hκ,hc,⟨i,E,hi,-,hh,Y,H,t,hH,ht,hE⟩,g,hg,hG⟩ := h
  rw [hi]; refine ⟨?_,fun i => (hG i).1.symmetry,?_,?_⟩
  · intro b U; apply congrArg₂ _ rfl
    rw [hE (gauge b U),hE U]; apply tsum_congr; intro i
    by_cases e : Healthy X.threshold (Y i) U
    · rw [masked_eq _ _ _ _ (by simpa [Healthy] using e),masked_eq _ _ _ _ e]; exact (hH i).2.1.symmetry b U
    rw [masked_ne _ _ _ _ (by simpa [Healthy] using e),masked_ne _ _ _ _ e]
  · intro U; refine (norm_add_le i _).trans (add_le_add hh ?_); rw [hE]
    obtain ⟨x,hx⟩ := he
    have hv := (Banked.reserve (G:=G) ⟨x,hx⟩ hr (hd:=fun i => (hH i).2.2.2) ht).absolute U
    apply (norm_tsum_le_tsum_norm hv).trans
    refine le_trans (hv.tsum_le_tsum (fun j => ?_) ht.2.1) ht.2.2
    have ew := (hH j).2.2.1
    refine le_trans ?_ (le_mul_of_one_le_left ew (burn_ge X hr (Y j)))
    by_cases e : Healthy X.threshold (Y j) U
    · rw [masked_eq _ _ _ _ e]; exact ((hH j).2.2.2 _ hx).2 U e [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ e, norm_zero]; exact ew
  intro i U; exact ((hG i).2.2.2 U).trans ((le_mul_of_one_le_left (hG i).2.2.1 (burn_ge X hr i.zone)).trans
    ((single_le_sum (fun j _ => mul_nonneg (burn_pos X r j.zone).le (hG j).2.2.1) (mem_univ i)).trans hg))

/-- regular on all-good test stored later. `FitsPurse` here controls all U. -/
structure FitsPurse (c : ℝ) (F : Config G n → ℂ) : Prop where
  nonneg : 0 ≤ c
  symmetry : GaugeInvariant F
  borel : Measurable F
  all (U) : ‖F U‖ ≤ c
lemma FitsPurse.integral {c : ℝ} {F : Config G n → ℂ} (h : FitsPurse c F) : Integrable F (prior G _) :=
    Integrable.of_bound h.borel.aestronglyMeasurable c (Eventually.of_forall h.all)


lemma jet_bounded (R : Census V) (B κ : ℝ) {σ C Λ δ v : ℝ} (P : Rep G n) (h : P.Lawful σ C Λ δ v)
    (hp : GaugeInvariant P.exponent) (q : R.Mode) : ∃ C : ℝ, ∀ (D : V → Pulse G n) (X : V→Support n),
      (∀ i,Credit P.p 0 κ (X i) (D i) B) → FitsPurse C (jet P R D q) := by
  -- compactness of finite algebra.
  let p (W : Support n) (x : ℂ × (V → ℂ) × (Pack n → ℂ) × (Pack n → V → ℂ)) :=
    (x.1 • (Poly.pass (lambda R x.2.1) * ∑ T∈Pack.clears W,∏ j∈T, (Poly.send R.quiet (x.2.2.1 j) + lambda R (x.2.2.2 j)))).part q
  obtain ⟨K,hK⟩ := (Desk.holders P h).cost
  choose g hg using fun i => (Desk.holders_K P h i).cost
  let L := ∑ i, |g i|
  let K' := Set.prod (Metric.closedBall (0:ℂ) K) (Set.prod (Metric.closedBall (0:V → ℂ) |B+B|)
      (Set.prod (Metric.closedBall (0:Pack n→ℂ) L) (Metric.closedBall (0:Pack n → V→ℂ) |κ*B|)))
  have hc : ∀ W, Continuous (p W) := by
    intro W
    have he : Continuous (lambda R) := by
      unfold lambda; apply continuous_finsetSum; intro i _; fun_prop
    unfold p; fun_prop
  have hz (W : Support n) : BddAbove ((fun c => ‖p W c‖) '' K') :=
    ((show IsCompact K' from (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))).image (hc W).norm).bddAbove
  choose f H using hz; classical
  let k := ∑ W, |f W|
  refine ⟨k,fun D X hD => ⟨by unfold k; positivity,?_,?_,?_⟩⟩
  · intro t U; unfold jet polar composeAt; rw [hp t U, gauge_flags]
    simp_rw [(personal (hD _)).1 t U, (personal (hD _)).2.1 _ t U]
    congr 3
    apply sum_congr rfl; intro i _; refine prod_congr rfl fun j _ => ?_
    rw [(show incumbent P (gauge t U) j=_ from (incumbent_legible _ _ h.labels.forced).symmetry t U)]
  · exact (throughJet _ h _ _ (Leaf.sum _ _ fun i => Leaf.insert_ ((hD i).integrand.1) _) fun j =>
      Leaf.sum _ _ fun i => Leaf.insert_ ((hD i).integrand.2 _) _ : Leaf.All (polar P R D)) q |>.meas
  intro U
  let W := flags P.p.threshold U
  refine (H W ?_).trans ((le_abs_self _).trans (single_le_sum (fun i _ => abs_nonneg (f i)) (mem_univ W)))
  let a i : ℂ := (D i).1 U
  let m p i : ℂ := (D i).2 p U
  let F : (ℂ × (V → ℂ) × (Pack n → ℂ) × (Pack n → V → ℂ)) := ((Real.exp (P.exponent U):ℂ),a, incumbent P U,m)
  refine ⟨F,⟨(mem_closedBall_zero_iff.mpr (hK U)),?_,?_,?_⟩,rfl⟩
  · refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_)
    exact ((personal (hD i)).2.2.1 U).trans (le_abs_self _)
  · refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (sum_nonneg fun i _ => abs_nonneg (g i))).mpr fun i => ?_)
    exact (hg i U).trans ((le_abs_self _).trans (single_le_sum (fun j _ => abs_nonneg (g j)) (mem_univ i)))
  refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j =>
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ((personal (hD i)).2.2.2 j U).trans (le_abs_self _))
end YM.Multi.Step
