import YM.Bid.Fuels

/-!
# Resale from mixed and grain budgets

We work per site label in the marker set (both sorts of addresses), not
summing up over the markers. The path reserve in `intake` buys toll only
at rank ≥ 2; the rest has to be paid already. Thereafter shrink the
radius once to pay a common nonfactorial bound in the actual stop order.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.I02
open Finset RG Lattice Marker Wilson Overlay Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators

private lemma budget_mono {ι : Type*} {f g : ι → ℝ} {c : ℝ}
    (hb : SumBudget g c) (hf : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ g i) : SumBudget f c := by
  have hs := hb.2.1.of_nonneg_of_le hf h
  exact ⟨hf, hs, (hs.tsum_le_tsum h hb.2.1).trans hb.2.2⟩

variable {G : Gauge} {n : Side}

private lemma sup_of_grain (p : BudgetPoint) {S : Support n} {F : Config G n → ℂ}
    {x : Site n} {a : ℝ} (ha : 0 ≤ a) (h : grain p S F x a) :
    p.supBounds x S F (a*(p.order.factorial:ℝ)) := by
  obtain ⟨f, hf, hs, H⟩ := h
  refine ⟨mul_nonneg ha (by positivity), fun U hu k hk hv => ?_⟩
  have hz : f k.length / (k.length.factorial:ℝ) ≤ a := by
    refine le_trans ?_ hs
    apply Finset.single_le_sum (f:=fun i : ℕ => f i / (i.factorial:ℝ)) (a:=k.length)
    · intro i _
      exact div_nonneg (hf i) (by positivity)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hh : f k.length ≤ a*(k.length.factorial:ℝ) := (div_le_iff₀ (by positivity)).mp hz
  exact (H k hk hv U hu).trans (hh.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast Nat.factorial_le hk) ha))

variable {V : Type} [DecidableEq V] {R : Census V}

private lemma rank_total {ι : Type*} (m : ι → R.Mode) (f : ι → ℝ) (i : V)
    (h0 : SumBudget (fun j => if ranked (m j)=false ∧ i∈(m j).val then f j else 0) 1)
    (h1 : SumBudget (fun j => if ranked (m j)=true ∧ i∈(m j).val then f j else 0) 1) :
    SumBudget (fun j => if i∈ (m j).val then f j else 0) 2 := by
  let g (b : Bool) (j : ι) := if ranked (m j)=b ∧ i∈(m j).val then f j else 0
  change SumBudget (g false) 1 at h0
  change SumBudget (g true) 1 at h1
  rw [show (fun j => if i∈ (m j).val then f j else 0)=(fun j => g false j+g true j) by
    funext j; cases hj : ranked (m j) <;> simp [g, hj]]
  refine ⟨fun j => add_nonneg (h0.1 j) (h1.1 j), h0.2.1.add h1.2.1, ?_⟩
  rw [Summable.tsum_add h0.2.1 h1.2.1]
  exact (add_le_add h0.2.2 h1.2.2).trans_eq (by norm_num)

-- Spend the factorial on a nonempty root key. Bigger keys don't
-- need a bigger factor; the smaller price suffices for all the others.
-- Used also on forced hits (there we can afford to loosen the bound).
private lemma shrink_budget {ι : Type*} (p : BudgetPoint) {c r D : ℝ}
    (m : ι → R.Mode) (S : ι → Support n) (f : ι → ℝ) (i : V)
    (hf : ∀ j, 0 ≤ f j) (hr : 0 < r) (hD : 1 ≤ D)
    (h : SumBudget (fun j => if i∈ (m j).val then
        Poly.toll (fun _ => r) (m j)*loaf p (S j) 0 (f j) else 0) c) :
    SumBudget (fun j => if i∈ (m j).val then
        Poly.toll (fun _ => r/D) (m j)*p.mass (S j) (f j*D) else 0) c := by
  have hP : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hb : 0 < r/D := div_pos hr hP
  apply budget_mono h
  · intro j
    split
    · exact mul_nonneg (Poly.worth (fun _ => hb) _).le (mul_nonneg (Real.exp_pos _).le (mul_nonneg (hf j) hP.le))
    exact le_rfl
  intro j
  split_ifs with hj
  · have ht : Poly.toll (fun _ => r/D) (m j)*D ≤ Poly.toll (fun _ => r) (m j) := by
      have he : 0 < (m j).val.card := Finset.card_pos.mpr ⟨i,hj⟩
      obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
      simp only [Poly.toll, prod_const, hl, pow_succ, mul_assoc, div_mul_cancel₀ _ hP.ne']
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le (div_le_self hr.le hD) _) hr.le
    calc
      _ = (Poly.toll (fun _ => r/D) (m j)*D)*loaf p (S j) 0 (f j) := by
        rw [BudgetPoint.mass, loaf, add_zero]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (mul_nonneg (Real.exp_pos _).le (hf j))
  exact le_rfl

variable [Fintype V] {X : Rep G n} {A : Bands R X}

-- On the mixed keys support can finance the change from provisional
-- rates t. Cost x = 0 is free even if there's no support pin.
private lemma support_pays (hI : Bid.I01) (hs : Stubs.far (A:=A))
    {t w : V → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hw : ∀ i, 0 < w i)
    (hr : ∀ i, 0<t i ∧ w i ≤ t i*Real.exp (δ*X.p.B/64)) {q : R.Mode}
    (hq : ranked q=true) (S : Support n) {x : ℝ} (hx : 0 ≤ x)
    (h : 0 < x → ∀ i∈ q.val, A.origins i ∈ S) :
    Poly.toll w q*loaf X.p S 0 x ≤ Poly.toll t q*loaf X.p S δ x := by
  rcases eq_or_lt_of_le hx with he|he
  · simp [← he, loaf]
  have hk : 2 ≤ q.val.card := by simpa [ranked] using hq
  let B := X.p.B
  let d := coverNumber B S
  have hB : 8 ≤ B := by
    obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.1 (show 1 < q.val.card from hk)
    exact (hs a b hab).1
  have hp : B*q.val.card ≤ 64*d := by
    apply hI n V A.origins B hB q.val _ hk S
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact h he i hi
    intro i _ j _ hij
    simpa only [sq] using (hs i j hij).2
  have hp' : (B:ℝ)*q.val.card ≤ 64*(d:ℝ) := by exact_mod_cast hp
  have heδ : (q.val.card:ℝ)*(δ*B/64) ≤ δ*d := by
    have := mul_le_mul_of_nonneg_left hp' hδ
    linarith
  have ht : Poly.toll w q ≤ Poly.toll t q*Real.exp (δ*d) := by
    calc
      _ ≤ ∏ i∈q.val, (t i * Real.exp (δ*B/64)) :=
        prod_le_prod (fun i _ => (hw i).le) (fun i _ => (hr i).2)
      _ = Poly.toll t q*Real.exp ((q.val.card:ℝ)*(δ*B/64)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Real.exp_nat_mul, Poly.toll]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr heδ)
        (Poly.worth (fun i => (hr i).1) q).le
  calc
    _ ≤ (Poly.toll t q*Real.exp (δ*d))*loaf X.p S 0 x :=
      mul_le_mul_of_nonneg_right ht (mul_nonneg (Real.exp_pos _).le hx)
    _ = _ := by
      unfold loaf
      rw [add_zero, add_mul, Real.exp_add]
      dsimp only [d, B]
      ring

private lemma intake_pays (hI : Bid.I01) (T : Stubs A) (ha : A.Active)
    (hs : Stubs.far (A:=A)) {w : V → ℝ} (hw : ∀ i, 0 < w i)
    (h : T.intake w) : T.funded w 0 true 1 := by
  rcases h with he|⟨t, δ, hδ, hr, hF, hG⟩
  · exact he
  constructor
  · intro i
    apply budget_mono (hF i)
    · intro j
      split
      · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (T.nonnegative j))
      exact le_rfl
    intro j
    split_ifs with hj
    · exact support_pays hI hs hδ hw hr hj.1 _ (T.nonnegative _) (fun _ => ha.pins j)
    exact le_rfl
  intro i
  apply budget_mono (hG i)
  · intro j
    split
    · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (T.usable j))
    exact le_rfl
  intro j
  split_ifs with hj
  · exact support_pays hI hs hδ hw hr hj.1 _ (T.usable _) (fun he => ha.retained j.1 j.2 (T.paid j he))
  exact le_rfl

theorem answer : YM.Bid.I02 := by
  intro hI G n V FV DV R X P r hr h
  obtain ⟨T, h0, h1⟩ := h.atC
  have h2 := intake_pays hI T h.ready h.spaced (fun _ => hr) h1
  let D : ℝ := X.p.order.factorial
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact_mod_cast (show 1 ≤ X.p.order.factorial from Nat.factorial_pos _)
  have hP : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨fun _ => div_pos hr hP, fun i => ?_, zero_lt_one, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (div_le_self hr.le hD) (norm_nonneg _)).trans (h.units i)
  · refine ⟨fun i => T.a i*D, fun i =>
      ⟨mul_nonneg (T.nonnegative _) hP.le, fun x hx =>
        sup_of_grain _ (T.nonnegative _) (T.kernels i x hx)⟩, fun i => ?_⟩
    exact shrink_budget X.p P.rays P.support T.a i T.nonnegative hr hD
      (rank_total P.rays (T.crown _ 0) i (h0.1 i) (h2.1 i))
  refine ⟨fun q => T.k q*D, fun i j => ⟨mul_nonneg (T.usable _) hP.le, fun x =>
    (T.supplies i j x).trans (le_mul_of_one_le_right (T.usable _) hD)⟩, fun i => ?_⟩
  rw [mul_one]
  exact shrink_budget X.p (fun j => P.marks j.1 j.2)
      (fun j => (X.activities.forced j.1).support) T.k i T.usable hr hD
      (rank_total _ (T.cord _ 0) i (h0.2 i) (h2.2 i))

end YM.Work.I02
