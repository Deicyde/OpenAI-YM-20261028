import YM.Push.BETA_TRANSPORT.Census

/-!
# Common input domination on further parameter subsequences

Fixed finite period ONLY.

Add positive slack of arbitrarily small total size
in the requested norms, leaving the same input exponent and cuts, to price
individual labels with ONE list along the comparisons.

This is a
quantified implication of the input curve and one cap, *not* an assertion that
the new margins meet a particular output construction's hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG RG.Activities RG.Shoot Filter Function Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {n : Side} {G : Gauge} {P : BudgetPoint}

structure LabelBudget (P : BudgetPoint) (e k : ℕ → ℝ) (S : Activities G n) (δ w : ℝ) extends Majorizes P e k S where
  E (x : Site n) : SumBudget (fun i => if (S.reg i).site=x then P.mass (S.reg i).support (e i) else 0) δ
  K (x : Site n) : SumBudget (fun i => if x ∈ (S.forced i).support then P.mass (S.forced i).support (k i) else 0) w

lemma valid_labelBudget {S : Activities G n} {δ w : ℝ} (h : S.Valid P δ w) : ∃ e k, LabelBudget P e k S δ w := by
  obtain ⟨e,he,hE⟩ := h.boundE; obtain ⟨k,hk,hK⟩ := h.boundK
  exact ⟨e,k,⟨he,hk⟩,hE,hK⟩

lemma budget_of_ge {v w : ℕ → ℝ} {δ : ℝ} (hv : SumBudget v δ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i, w i ≤ v i) : SumBudget w δ := by
  have hs := hv.2.1.of_nonneg_of_le hw h
  exact ⟨hw,hs,(hs.tsum_le_tsum h hv.2.1).trans hv.2.2⟩
lemma budget_add {v w : ℕ → ℝ} {δ τ : ℝ} (hv : SumBudget v δ) (hw : SumBudget w τ) : SumBudget (v+w) (δ+τ) :=
  ⟨fun i => add_nonneg (hv.1 i) (hw.1 i),hv.2.1.add hw.2.1,(hv.2.1.tsum_add hw.2.1).trans_le (add_le_add hv.2.2 hw.2.2)⟩
lemma budget_extra {δ τ : ℝ} {X : ℕ → Support n} {p : ℕ → Prop} [DecidablePred p] {v w : ℕ → ℝ}
    (hv : SumBudget (fun i => if p i then P.mass (X i) (v i) else 0) δ) (hw : SumBudget (fun i => P.mass (X i) (w i)) τ) :
    SumBudget (fun i => if p i then P.mass (X i) ((v+w) i) else 0) (δ+τ) := by
  refine budget_of_ge (budget_add hv hw) ?_ ?_ <;> intro i <;> dsimp only [BudgetPoint.mass, Pi.add_apply] <;>
    split
  · rw [mul_add]; exact add_nonneg (by simpa [*, BudgetPoint.mass] using hv.1 i) (hw.1 i)
  · rfl
  · rw [mul_add]
  · rw [zero_add]; exact hw.1 i

lemma collect_margin {v : ℕ → ℕ → ℝ} {δ : ℕ → ℝ} {X : ℕ → Support n} (hδ : Summable δ)
    (hv : ∀ j i, 0 ≤ v j i) (hB : ∀ j, SumBudget (fun i => P.mass (X i) (v j i)) (δ j)) :
    ∃ q : ℕ → ℝ, (∀ j i, v j i ≤ q i) ∧ SumBudget (fun i => P.mass (X i) (q i)) (∑' j, δ j) := by
  have ht (f : ℕ → ℕ → ℝ) (hf : ∀ j, SumBudget (f j) (δ j)) : Summable (uncurry f) ∧
        SumBudget (fun i => ∑' j, f j i) (∑' j, δ j) := by
    have hg : Summable (fun j => ∑' i, f j i) := hδ.of_nonneg_of_le (fun j => tsum_nonneg (hf j).1) (fun j => (hf j).2.2)
    have hs := (summable_prod_of_nonneg (f:=uncurry f) fun p => (hf p.1).1 p.2).mpr ⟨fun j => (hf j).2.1,hg⟩
    exact ⟨hs,fun i => tsum_nonneg fun j => (hf j).1 i,hs.prod_symm.prod,hs.tsum_comm.trans_le
      (hg.tsum_le_tsum (fun j => (hf j).2.2) hδ)⟩
  have h1 := ht v fun j => budget_unweighted (hv j) (hB j)
  have h2 := (ht (fun j i => P.mass (X i) (v j i)) hB).2
  refine ⟨fun i => ∑' j, v j i,fun j i => (h1.1.prod_symm.prod_factor i).le_tsum j (fun k _ => hv k i),?_⟩
  simpa only [BudgetPoint.mass, tsum_mul_left] using h2

/-- No assumption of uniform dominating lists along *every* sequence. -/
lemma input_subsequence {s : Set ℝ} {T : ℝ → Rep G n} (h : Curve P T s) {x : ℝ} (hx : x ∈ s) {δ w : ℝ}
    (hv : (T x).activities.Valid P δ w) {y : ℕ → ℝ} (hy : Tendsto y atTop (𝓝[s] x)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (r : ℕ → ℕ) (e k : ℕ → ℝ), StrictMono r ∧ (∀ j, y (r j) ∈ s) ∧ LabelBudget P e k (T x).activities (δ+τ) (w+τ) ∧
      ∀ j, LabelBudget P e k (T (y (r j))).activities (δ+τ) (w+τ) := by
  obtain ⟨e,k,H⟩ := valid_labelBudget hv
  let a (j : ℕ) := (τ/2) * ((1/2:ℝ)^j)
  have ha : Summable a := summable_geometric_two.mul_left _
  have hh : ∑' j, a j = τ := by unfold a; rw [tsum_mul_left,tsum_geometric_two]; ring
  obtain ⟨r,hr,he⟩ := extraction_forall_of_eventually (fun j => hy.eventually
    ((h.continuous (a j) (by unfold a; positivity) x hx).and (by exact self_mem_nhdsWithin)))
  choose c d hc hd hC hD using fun j => (he j).1
  obtain ⟨q,hq,hQ⟩ := collect_margin ha (fun j i => (hc j i).1) hC
  obtain ⟨p,hp,hP⟩ := collect_margin ha (fun j i => (hd j i).1) hD
  rw [hh] at hP hQ
  have hq' i : 0 ≤ q i := (hc 0 i).1.trans (hq 0 i)
  have hp' i : 0 ≤ p i := (hd 0 i).1.trans (hp 0 i)
  let E := e+q; let K := k+p
  have hb : LabelBudget P E K (T x).activities (δ+τ) (w+τ) := ⟨
    ⟨fun i => ⟨(H.smooth i).1.trans (le_add_of_nonneg_right (hq' i)), fun U hu l hl hw =>
      ((H.smooth i).2 U hu l hl hw).trans (le_add_of_nonneg_right (hq' i))⟩,
      fun i => ⟨(H.hard i).1.trans (le_add_of_nonneg_right (hp' i)), fun U => ((H.hard i).2 U).trans (le_add_of_nonneg_right (hp' i))⟩⟩,
    fun i => budget_extra (H.E i) hQ,fun i => budget_extra (H.K i) hP⟩
  refine ⟨r,E,K,hr,fun j => (he j).2,hb,fun j => ?_⟩
  have h1 := h.reg _ (he j).2 x hx; have h2 := h.forced _ (he j).2 x hx
  refine ⟨⟨fun i => ?_,fun i => ?_⟩,fun i => by rw [h1]; exact hb.E i,fun i => by rw [h2]; exact hb.K i⟩
  · rw [h1]; refine ⟨(hb.smooth i).1, fun U hu l hl hw => ?_⟩
    have hi := (H.smooth i).2 U hu l hl hw; have ht := (hc j i).2 U hu l hl hw
    have hz := norm_sub_le (leftDerivs ((T x).activities.E i) l U)
      (leftDerivs ((T x).activities.E i) l U - leftDerivs ((T (y (r j))).activities.E i) l U)
    rw [sub_sub_cancel] at hz; exact hz.trans (add_le_add hi (ht.trans (hq j i)))
  refine ⟨(hb.hard i).1,fun U => ?_⟩
  have hz := norm_sub_le ((T x).activities.K i U) ((T x).activities.K i U-(T (y (r j))).activities.K i U)
  rw [sub_sub_cancel] at hz; exact hz.trans (add_le_add ((H.hard i).2 U) (((hd j i).2 U).trans (hp j i)))

end YM.Push.BetaTransport
