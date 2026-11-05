import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Tangent

set_option warningAsError false

/-! # Honest prices for the nonuniqueness (and for using enlargement)

No predicate simplification inside the pack and `κ` at birth or at
intermediate scales must still be paid. Needed unmarked Pack purchases
specified. Reuses one-support diameter/cover witnesses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Multi.Pack
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} (P : Rep G n) {F : Config G n→ℂ} {p : Pack n}

lemma final_parent (t : ℝ) {X Y : Support n} (h : X ⊆ Y) (f : Config G n → ℂ)
    (H : UsesFinal t X f) : UsesFinal t Y f := by
  intro U V he hg
  refine H _ _ (agrees_mono he h) ?_; ext i; constructor <;> intro h'
  · obtain ⟨h1,h2⟩ := mem_inter.mp h'
    have hf : i∈ Y∩ flags t V := hg ▸ (show i∈Y∩flags t U from mem_inter.mpr ⟨h h1,h2⟩)
    exact mem_inter.mpr ⟨h1,(mem_inter.mp hf).2⟩
  obtain ⟨h1,h2⟩ := mem_inter.mp h'
  have hf : i∈Y∩flags t U := hg.symm ▸ (show i∈Y∩flags t V from mem_inter.mpr ⟨h h1,h2⟩)
  exact mem_inter.mpr ⟨h1,(mem_inter.mp hf).2⟩

lemma shielded_legible (hM : Measurable F) (hs : GaugeInvariant F) (hr : UsesFinal P.p.threshold p.zone F) :
    Legible P.p p (shielded P p F) := by
  unfold shielded
  refine ⟨Measurable.ite (Pack.neighborhood_meas ..) hM measurable_const,fun k U => ?_,fun U V h hg => ?_,fun U h => ?_⟩
  · simp only [hs k U,gauge_flags]
  · change (if _ then _ else _) = if _ then _ else _; rw [hr _ _ h hg,hg]
  by_contra he; exact h (if_neg he)

lemma guarded (p : Pack n) (F : Config G n → ℂ) {t} (ht : 0 ≤ t) (hf : ∀ U, ‖F U‖ ≤ t) (U) :
    ‖shielded P p F U‖ ≤ t := by unfold shielded; split; exact hf U; exact (norm_zero).trans_le ht

def tagCost (p : Pack n) (δ κ t : ℝ) := burn P.p δ p.zone*t/κ
lemma solo_credit (h : Legible P.p p F) {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (he : ∀ U, ‖F U‖ ≤ c) (X : Support n) (hX : X.Nonempty) (hp : X ⊆ p.zone) :
    Multi.Credit P.p δ κ X (soloPay p F) (tagCost P p δ κ c) := by
  let a : ℝ := tagCost P p δ κ c; have ha : 0≤a := div_nonneg (mul_nonneg (burn_pos ..).le hc) hκ.le
  refine ⟨hX,hδ,hκ,ha,⟨0,0,?_,fun _ => rfl,(norm_zero).trans_le ha,(Banked.zero ..).enlarge ha⟩,
    fun i => if i=p then c else 0, ?_, fun i => ?_⟩
  · funext x; simp [soloPay]
  · simp only [mul_ite,mul_zero,sum_ite_eq', mem_univ, if_true]
    unfold tagCost; field_simp; exact le_rfl
  by_cases hi : i=p
  · subst i; simp only [soloPay]; exact ⟨h,fun _ => hp,hc,he⟩
  simp only [soloPay,if_neg hi, ne_eq,not_true_eq_false]; exact ⟨Legible.zero ..,False.elim,le_rfl,fun U => (norm_zero).le⟩

/-- Preserve κ. t' is the stronger exponent pack budget, needed when
spending this kernel lemma at a higher test. Need κ>0 as in single/mixed
step tests. Even if only at δ=0 obtain Mint from unmarked stock. -/
theorem kernel_credit {δ κ t w σ Λ v κ' : ℝ} (hv : P.Lawful σ w Λ v κ')
    (hm : Mint P δ t) (hκ : 0 < κ) (hδ : 0 ≤ δ) (h : Legible P.p p F) {c : ℝ} (hc : 0 ≤ c) (he : ∀ U, ‖F U‖ ≤ c)
    (X : Support n) (hX : X.Nonempty) (hp : X ⊆ p.zone) (z : Site n) :
    Multi.Credit P.p δ κ X (nullPay P p z F) ((2+t)*tagCost P (spread p z) δ κ c) := by
  let y := spread p z
  let V := tagCost P y δ κ c
  let h0 := burn P.p δ y.zone
  let B := P.p.B
  have hE : P.p.supportExponent>0 := P.p.exponent_pos
  have h₁ := (solo_credit P h hκ hc hδ he X hX hp)
  have hh : burn P.p δ p.zone ≤ h0 := Real.exp_monotone (by
    apply mul_le_mul_of_nonneg_left (show _ ≤ _ from ?_) (add_nonneg hE.le hδ)
    exact_mod_cast (Corona.cover_mono (show p.zone⊆y.zone from Finset.subset_insert ..) B))
  have h₂ : Multi.Credit P.p δ κ X (soloPay p F) V := h₁.expand
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc) hκ.le)
  obtain ⟨f,hf,hg⟩ := hm
  have ht : 0≤t := le_trans (Finset.sum_nonneg (fun j _ => mul_nonneg (burn_pos ..).le (hf j).1)) (hg z)
  have h₃ : Multi.Credit P.p δ κ X (enlarged P p z F) ((1+t)*V) := by
    unfold enlarged
    have hi : p.zone ⊆ y.zone := Finset.subset_insert ..
    let K (i : Pack n) := burn P.p δ i.zone*f i
    have hk i : 0 ≤ K i := mul_nonneg (burn_pos ..).le (hf i).1
    have h : Multi.Credit P.p δ κ X (soloPay y (shielded P y F)) V := solo_credit P
      (shielded_legible P h.borel h.symmetry (final_parent _ hi F h.reads)) hκ hc hδ (guarded P y F hc he) X hX (hp.trans hi)
    let f0 (j : Pack n) (U) := F U * incumbent P U j
    let W j := soloPay (braid p j) (shielded P (braid p j) (f0 j))
    have hz j (h : j∈attaches p z) : Multi.Credit P.p δ κ X (W j) (K j*V) := by
      let a := braid p j
      have h₄ : p.zone ⊆ a.zone := Finset.subset_union_left
      have h₅ : j.zone ⊆ a.zone := Finset.subset_union_right
      obtain H := incumbent_legible P j hv.labels.forced
      have hF := (show Legible P.p p F from ‹_›)
      have hW : Legible P.p a (shielded P (braid p j) (f0 j)) := shielded_legible P (hF.borel.mul H.borel)
        (fun t U => congr_arg₂ (·*·) (hF.symmetry t U) (H.symmetry t U)) (fun U W h h' =>
          congr_arg₂ (·*·) (final_parent _ h₄ F hF.reads _ _ h h') (final_parent _ h₅ _ H.reads _ _ h h'))
      apply (solo_credit P hW hκ (mul_nonneg hc (hf j).1) hδ
        (guarded P a (f0 j) (mul_nonneg hc (hf j).1) (fun U => (norm_mul_le ..).trans (mul_le_mul (he U) ((hf j).2 U) (norm_nonneg _) hc))) X hX (hp.trans h₄)).expand
      have hi' : coverNumber B a.zone ≤ coverNumber B y.zone+coverNumber B j.zone := (Corona.cover_mono
        (show a.zone⊆y.zone∪ j.zone from union_subset_union hi subset_rfl) _).trans (Corona.meets_sum
          (show z ∈ y.zone from mem_insert_self ..) ((mem_filter.mp h).2.1) ..)
      unfold V tagCost K
      have hs : burn P.p δ a.zone ≤ burn P.p δ y.zone*burn P.p δ j.zone := by
        unfold burn; rw [← Real.exp_add,← mul_add]; apply Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (add_nonneg hE.le hδ))
        exact_mod_cast hi'
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs (mul_nonneg hc (hf j).1)) hκ.le).trans_eq
      ring
    apply (h.add (Multi.Credit.sums (attaches p z) W _ hX hδ hκ hz)).expand
    have hV : 0 ≤ V := div_nonneg (mul_nonneg (burn_pos ..).le hc) hκ.le
    rw [add_mul,one_mul,← sum_mul]; exact add_le_add_right
      (mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg (fun i hh =>
        Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp hh).2.1⟩) (fun i _ _ => hk i)).trans (hg z)) hV) V
  have H4 := h₃.scale (-1 : ℂ); rw [neg_one_smul,norm_neg,norm_one,one_mul] at H4
  unfold nullPay; rw [sub_eq_add_neg]; exact (h₂.add H4).expand (le_of_eq (by unfold V; ring))
end YM.AnalyticNext.GridStop.Alphabet
