import YM.Bid.Energy

/-!
# E09 finite-store inequalities

No compatibility assumptions on the periods here. Use `spend` only as
re-reading part of the counts in the SAME Stores. Fine and noise spend rows
are paid at `t * largeT`; the original seeds (including these) are still paid
at `t^2`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.E09
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open YM.Pressure YM.Pressure.Stores YM.Pressure.Tube YM.Pressure.Teller Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ComplexOrder Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma fine_budget (A : Stores S) (T : Tube G S) (U : Config G f) (V : Config G c)
    (x m d cF : ℝ) (Q : Config G c) (t : ℝ)
    (ht : 0 ≤ t) (hu : t ≤ largeT G x S.patch.L)
    (hm : 0 ≤ m) (hmp : m ≤ T.high.linear/8) (hmd : m ≤ d)
    (hF : cF ≤ T.high.linear/4)
    (h : T.high.linear/2*t*(∑ i ∈ A.swell U t, toll U i) +
      d*t^2*((A.costs \ A.swell U t).card:ℝ) ≤ A.tally T x U V) :
    m*t^2*A.costs.card + m*t*largeT G x S.patch.L*(A.spend U Q V x).costs.card +
      cF*t*(∑ i ∈ A.swell U t, toll U i) ≤ A.tally T x U V := by
  let u := largeT G x S.patch.L
  have hs : A.swell U u ⊆ A.swell U t := by
    intro i hi
    obtain ⟨hi,hi'⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,lt_of_le_of_lt hu hi'⟩
  let R := ∑ i ∈ A.swell U t, toll U i
  have hr : 0 ≤ R := sum_nonneg fun i _ => G.chord_nonneg _
  have h1 : (A.swell U t).card • t ≤ R :=
    card_nsmul_le_sum _ _ _ (fun i hi => le_of_lt (mem_filter.mp hi).2)
  have h2 : (A.swell U u).card • u ≤ R :=
    le_trans (card_nsmul_le_sum _ (toll U) _ (fun i hi => le_of_lt (mem_filter.mp hi).2))
      (sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => G.chord_nonneg _)
  simp only [nsmul_eq_mul] at h1 h2
  have hk : ((A.costs \ A.swell U t).card : ℝ) + (A.swell U t).card = A.costs.card := by
    exact_mod_cast (card_sdiff_add_card_eq_card (show A.swell U t ⊆ A.costs from filter_subset ..))
  change m*t^2*_ + m*t*u*(A.swell U u).card + cF*t*R ≤ _
  apply le_trans _ h
  rw [← hk]
  have hfee := mul_le_mul_of_nonneg_right
    (show 2*m + cF ≤ T.high.linear/2 by linarith only [hmp,hF]) (mul_nonneg ht hr)
  dsimp only [R] at *
  linarith only [mul_le_mul_of_nonneg_left h1 (mul_nonneg hm ht),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hm ht), hfee,
    mul_le_mul_of_nonneg_right hmd
      (show 0 ≤ t^2*((A.costs \ A.swell U t).card:ℝ) by positivity)]

lemma wire_listed (A : Stores S) (U : Config G f) (V : Config G c) (k : S.Choices)
    (x W : ℝ) (h : A.Plot U k V x W) (b : Bond c) (hb : b ∈ A.aisles) :
    W * fiery G x S.patch.L ≤ wire (S.prediction U k) V b := by
  refine (h.drive b ?_).1 hb
  have hi : b.1 ∈ pinPos b := by simp [pinPos]
  refine Finset.not_disjoint_iff.mpr ⟨b.1, halo_subset _ _ ?_, hi⟩
  exact mem_union_left _ <| mem_union_right _ <| mem_biUnion.mpr ⟨b,hb,hi⟩

lemma noise_budget (A : Stores S) (T : Tube G S) (U : Config G f) (Q V : Config G c)
    (x m C W t : ℝ)
    (hw : 1 ≤ W) (hlist : ∀ i ∈ A.aisles, W*t ≤ wire Q V i)
    (ht : 0 ≤ t) (hu : t ≤ largeT G x S.patch.L)
    (hm : 0 ≤ m) (hmp : m ≤ S.kernel.penalty/32)
    (hC : C ≤ S.kernel.penalty/16 * W)
    (h : S.kernel.penalty/8*(∑ i∈A.aisles, wire Q V i^2) ≤ A.talli T x Q V) :
    m*t^2*A.aisles.card + m*t*largeT G x S.patch.L*(A.spend U Q V x).aisles.card +
      C*t*(∑ i ∈ A.aisles, wire Q V i) ≤ A.talli T x Q V := by
  let u := largeT G x S.patch.L
  let p := S.kernel.penalty
  have hp : 0 < p := S.kernel.penalty_pos
  let R := ∑ i ∈ A.aisles, wire Q V i^2
  have hr : 0 ≤ R := sum_nonneg fun i _ => sq_nonneg _
  have hall (i) (hi : i ∈ A.aisles) : t ≤ wire Q V i :=
    (le_mul_of_one_le_left ht hw).trans (hlist i hi)
  have H : A.drives Q V u ⊆ A.aisles := filter_subset ..
  have h1 : A.aisles.card • (t^2) ≤ R := card_nsmul_le_sum _ _ _ fun i hi =>
    pow_le_pow_left₀ ht (hall i hi) _
  have h2 : (A.drives Q V u).card • (t*u) ≤ R := by
    refine le_trans
      (card_nsmul_le_sum _ (fun i => wire Q V i^2) _ ?_)
      (sum_le_sum_of_subset_of_nonneg H fun _ _ _ => sq_nonneg _)
    intro i hi
    rw [sq]
    exact mul_le_mul (hall i (H hi)) (le_of_lt (mem_filter.mp hi).2)
      (ht.trans hu) (ht.trans (hall _ (H hi)))
  simp only [nsmul_eq_mul] at h1 h2
  have hfee : C*t*(∑ i ∈ A.aisles, wire Q V i) ≤ p/16 * R := by
    unfold R
    simp_rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hct : C*t ≤ p/16 * wire Q V i := calc
      C*t ≤ p/16 * W * t := mul_le_mul_of_nonneg_right hC ht
      _ = p/16 * (W*t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlist i hi) (by positivity)
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hct (ht.trans (hall i hi))
  apply le_trans _ h
  change m*t^2*_ + m*t*u*(A.drives Q V u).card + _ ≤ p/8 * R
  change m ≤ p/32 at hmp
  linarith only [mul_le_mul_of_nonneg_left h1 hm, mul_le_mul_of_nonneg_left h2 hm,
    mul_le_mul_of_nonneg_right hmp hr, hfee]

private lemma tides_subset (A : Stores S) (V : Config G c) (x δ : ℝ) (hx : temp x ≤ δ) :
    A.tides V x δ ⊆ A.tides V x (temp x) := by
  intro i hi
  obtain ⟨hi,hi'⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hi,lt_of_le_of_lt hx hi'⟩

lemma coarse_budget (A : Stores S) (T : Tube G S) (V : Config G c)
    (x m B δ t : ℝ) (hs : 0 ≤ temp x) (hx : temp x ≤ δ) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hu : t ≤ 2*temp x)
    (hm : m ≤ T.low.direct/64) (h : Bid.Crowds δ B T x V) :
    4*m*t^2*((A.tides V x (temp x) \ A.tides V x δ).card : ℝ) ≤
      A.tallc T x V + T.low.linear*temp x*(∑ i ∈ A.tides V x δ, toll V i) +
        B*temp x^4*(A.outs x).card := by
  let s := temp x
  let o := A.outs x
  let w := T.workC (till x) V (temp x)
  let y := A.tides V x δ
  let z := A.tides V x (temp x)
  have hy : y ⊆ z := tides_subset A V x δ hx
  have hz : z ⊆ o := filter_subset ..
  -- First range: charge all outs for the cardinal bound.
  have h1' : (o \ z).card • (-(B * s^4)) ≤ ∑ i ∈ o \ z, w i := by
    refine card_nsmul_le_sum _ _ _ fun i hi => ?_
    obtain ⟨ho,hn⟩ := mem_sdiff.mp hi
    exact h.middle i (le_of_not_gt fun e => hn <| mem_filter.mpr ⟨ho,e⟩)
  have h1 : o.card • (-(B * s^4)) ≤ ∑ i ∈ o \ z, w i := by
    apply le_trans _ h1'
    simp only [nsmul_eq_mul]
    apply mul_le_mul_of_nonpos_right ?_ (neg_nonpos.mpr (by positivity))
    exact_mod_cast card_le_card (show o \ z ⊆ o from sdiff_subset)
  -- Second range: keep positive t^2 on each.
  have h2 : (z \ y).card • (4*m*t^2) ≤ ∑ i ∈ z \ y, w i := by
    refine card_nsmul_le_sum _ _ _ fun i hi => ?_
    obtain ⟨hz,hn⟩ := mem_sdiff.mp hi
    obtain ⟨ho,hr⟩ := mem_filter.mp hz
    change temp x < toll V i at hr
    apply le_trans _ (h.positive i hr (le_of_not_gt fun e => hn <| mem_filter.mpr ⟨ho,e⟩))
    have hp := T.low.quadratic_pos
    linarith only [mul_le_mul_of_nonneg_left hr.le
                     (show 0 ≤ T.low.direct * temp x from mul_nonneg hp.le hs),
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht hu 2) hp.le,
      mul_le_mul_of_nonneg_right hm (sq_nonneg t)]
  -- Third range: only take the Crowds allowance.
  have h3 : -(T.low.linear*s*(∑ i ∈ y, toll V i)) ≤ ∑ i ∈ y, w i := by
    rw [mul_sum, ← sum_neg_distrib]
    exact sum_le_sum fun i hi => h.last i (mem_filter.mp hi).2
  simp only [nsmul_eq_mul] at h1 h2
  change 4*m*t^2*((z\y).card:ℝ) ≤
    (∑ i ∈ o, w i) + T.low.linear*s*(∑ i ∈ y, toll V i) + B*s^4*o.card
  rw [← sum_sdiff hz, ← sum_sdiff hy]
  linarith only [h1,h2,h3]

lemma flags_budget (A : Stores S) (V Q : Config G c) (U : Config G f)
    (x δ : ℝ) (hx : temp x ≤ δ) (K : ℕ) (h : Bid.Payments δ A x U Q V K) :
    A.flags.card ≤ 4 *
      ((A.tides V x (temp x) \ A.tides V x δ).card + K*(A.spend U Q V x).shares) := by
  apply le_trans h.flags
  apply Nat.mul_le_mul_left
  exact le_trans (card_sdiff_add_card_eq_card (tides_subset A V x δ hx)).ge (Nat.add_le_add_left h.fee _)

end YM.Work.E09
