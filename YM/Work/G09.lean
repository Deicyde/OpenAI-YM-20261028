import YM.Bid.Loan

/-!
# Propagation of costs for a (matched) Duet

Instead of two global maxima, use a cone, in the opposite direction to a
primary cone: **coordinates are tiny compared to remainder budget**. This
propagates starting from the coarsest index (pairing), thanks to Bank and
roomCost, including their neighbor costs. Within that cone the discounted
cost bound propagates the other way.

All estimates are conditional on the Woke data. Nothing here constructs the
signed-difference coefficients from two trajectories.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G09

open YM.Bid
open Labels RG Lattice Source
open scoped Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {d : ℕ}

/-! ### Reducing `direction` to numerical estimates -/

private lemma coeff_nonneg (F : Labels.Frame G d) (u : F.Coeff) : 0 ≤ F.coeffSize u :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma coeff_tri (F : Labels.Frame G d) (u z : F.Coeff) :
    F.coeffSize z ≤ F.coeffSize u + F.coeffSize (u-z) := by
  unfold Labels.Frame.coeffSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖z i‖ ≤ ‖u i‖ + ‖u i-z i‖
  calc
    _ = ‖u i - (u i-z i)‖ := by rw [sub_sub_cancel]
    _ ≤ _ := norm_sub_le ..

private lemma coeff_core (F : Labels.Frame G d) (u : F.Coeff) :
    F.coeffSize (F.core u) ≤ F.coeffSize u := by
  unfold Labels.Frame.coeffSize
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖(Function.update u 0 0) i‖ ≤ ‖u i‖
  by_cases h : i = 0 <;> simp [Function.update, h]

private lemma coeff_vowel (F : Labels.Frame G d) (L : Side) (u : F.Coeff) :
    F.coeffSize u ≤ F.coeffSize (vowel F L u) := by
  unfold Labels.Frame.coeffSize
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [vowel, norm_mul, norm_pow, Complex.norm_natCast]
  have hL : (1 : ℝ) ≤ L.val := by
    exact_mod_cast (show 1 ≤ L.val from L.property)
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hL)

private theorem sizes_of_direction {H : History G} {W : Worth} {i : ℕ} {F : Labels.Frame G d}
    {u v : F.Coeff} {r t : ℝ} (h : direction H W i F u v r t) :
    let L := H.S.block i
    let Y := F.coeffSize (vowel F L v)
    let e := barunit L
    let K := W.K (H.levels.clock.J (i+1))
    0 ≤ t ∧ Y ≤ K * (F.coeffSize u + e*(Y+t)) ∧ r ≤ K*Y + e*t := by
  let L := H.S.block i
  let y := vowel F L v
  let e := barunit L
  let K := W.K (H.levels.clock.J (i+1))
  obtain ⟨-, ht, B, hB, herr, hcost⟩ := h
  have hK : 0 ≤ K := le_trans zero_le_one (W.prices _)
  have he : 0 ≤ e := by unfold e barunit puffs; positivity
  have hi := (hB (B y)).2.1
  rw [LinearEquiv.symm_apply_apply] at hi
  have hsub : F.coeffSize (u - B y) ≤ e*(F.coeffSize y+t) :=
    herr.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left ((coeff_core F v).trans (coeff_vowel F L v)) t) he)
  refine ⟨ht, hi.trans (mul_le_mul_of_nonneg_left ((coeff_tri F u (B y)).trans ?_) hK), hcost.trans ?_⟩
  · exact add_le_add le_rfl hsub
  · exact add_le_add (mul_le_mul_of_nonneg_left (coeff_core F _) hK) le_rfl

/-! ### Price and one-step cone arithmetic -/

private lemma bank_arith {K M C q : ℝ} (hK : 1 ≤ K) (hm : K ≤ M)
    (hc : 1 ≤ C) (h : 100000*M^6*(1+C)^2 ≤ q) :
    let a := 32*(1+C)^2
    let e := q⁻¹^3
    4*K*e ≤ 1 ∧ 4*K*a*e ≤ 1 ∧ (4*K^2+1)*(q*e) ≤ 1 := by
  dsimp only
  have hks : K ≤ K^2 := by nlinarith only [hK]
  have hprice : 128*K^2*(1+C)^2 ≤ q := by
    have hk2 : K^2 ≤ M^6 := calc
      _ ≤ M^2 := pow_le_pow_left₀ (by linarith) hm 2
      _ ≤ M^6 := pow_le_pow_right₀ (hK.trans hm) (by norm_num)
    refine le_trans ?_ h
    gcongr
    linarith
  have hs : 1 ≤ (1+C)^2 := one_le_pow₀ (by linarith)
  have hl : 128*K^2 ≤ q :=
    le_trans (le_mul_of_one_le_right (by positivity) hs) hprice
  have hq : 1 ≤ q := by linarith
  have hi : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hv : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have he : q⁻¹^3 ≤ q⁻¹ := by
    simpa using pow_le_pow_of_le_one (inv_nonneg.mpr hi.le) hv (show 1 ≤ 3 by norm_num)
  have hex : q*q⁻¹^3 ≤ q⁻¹ := calc
    q*q⁻¹^3 = q⁻¹^2 := by field_simp
    _ ≤ q⁻¹ := by
      simpa using pow_le_pow_of_le_one (inv_nonneg.mpr hi.le) hv (show 1 ≤ 2 by norm_num)
  have hbig : 4*K*(32*(1+C)^2) ≤ q := calc
    _ = 128*K*(1+C)^2 := by ring
    _ ≤ 128*K^2*(1+C)^2 := by gcongr
    _ ≤ q := hprice
  have hpay (b w : ℝ) (hb : 0 ≤ b) (hb' : b ≤ q) (hw : w ≤ q⁻¹) : b*w ≤ 1 := calc
    _ ≤ b*q⁻¹ := mul_le_mul_of_nonneg_left hw hb
    _ ≤ q*q⁻¹ := mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = 1 := mul_inv_cancel₀ hi.ne'
  exact ⟨hpay _ _ (by positivity) (by linarith) he, hpay _ _ (by positivity) hbig he,
    hpay _ _ (by positivity) (by linarith) hex⟩

private lemma cone_step_arith {K q e a b u v y r t : ℝ} (hk : 1 ≤ K)
    (he : 0 ≤ e) (hq : 0 ≤ q) (ha : 4*K^2 ≤ a) (hb : 0 ≤ b)
    (hp : 4*K*e ≤ 1) (hp' : 4*K*b*e ≤ 1) (hrent : (4*K^2+1)*(q*e) ≤ 1)
    (hu : 0 ≤ u) (hy : 0 ≤ y) (ht : 0 ≤ t)
    (hcone : a*u ≤ r) (hinv : y ≤ K*(u+e*(y+t))) (hh : v ≤ y) (hr : r ≤ K*y+e*t) :
    b*v ≤ t ∧ q*r ≤ t := by
  have hk' : 0 < K := by linarith
  have hm : e*t ≤ K*(e*t) := le_mul_of_one_le_left (mul_nonneg he ht) hk
  -- The leakage from the preceding level through u is already tiny.
  have hx : 4*K*u ≤ y+e*t := by
    apply le_of_mul_le_mul_left _ hk'
    calc
      K*(4*K*u) = (4*K^2)*u := by ring
      _ ≤ a*u := mul_le_mul_of_nonneg_right ha hu
      _ ≤ K*y+e*t := hcone.trans hr
      _ ≤ K*(y+e*t) := by rw [mul_add]; exact add_le_add le_rfl hm
  have hd : y ≤ 4*K*e*t := by
    linarith only [hx, hinv, hm, mul_le_mul_of_nonneg_right hp hy, mul_nonneg he ht]
  constructor
  · calc
      b*v ≤ b*(4*K*e*t) := mul_le_mul_of_nonneg_left (hh.trans hd) hb
      _ = (4*K*b*e)*t := by ring
      _ ≤ 1*t := mul_le_mul_of_nonneg_right hp' ht
      _ = _ := one_mul _
  calc
    q*r ≤ q*(K*(4*K*e*t)+e*t) := mul_le_mul_of_nonneg_left
      (hr.trans (add_le_add (mul_le_mul_of_nonneg_left hd hk'.le) le_rfl)) hq
    _ = ((4*K^2+1)*(q*e))*t := by ring
    _ ≤ 1*t := mul_le_mul_of_nonneg_right hrent ht
    _ = t := one_mul t

private lemma cone_step {W : Worth} {H : History G} (hC : roomCost H.levels W)
    (hbank : Bank W H.levels) {F : Labels.Frame G d} {i : ℕ} {u v : F.Coeff}
    {r t : ℝ} (hstep : direction H W i F u v r t)
    (h : 32*(1+(H.levels.params i).columns)^2 * F.coeffSize u ≤ r) :
    32*(1+(H.levels.params (i+1)).columns)^2 * F.coeffSize v ≤ t ∧ puffs (H.S.block i)*r ≤ t := by
  let j := H.levels.clock.J (i+1)
  let K := W.K j
  let C := (H.levels.params i).columns
  have hk : 1 ≤ K := W.prices _
  have ha : 4*K^2 ≤ 32*(1+C)^2 := by
    have hc : 64*K^2 ≤ C := le_trans (b := 64*(W.K (H.levels.clock.J i+1))^2)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (W.growth (show j ≤ _ from H.levels.fits.stepSlow i)) 2)
        (by norm_num)) (hC i)
    nlinarith only [hc, sq_nonneg K, sq_nonneg C]
  obtain ⟨hp, hp', hrent⟩ := bank_arith hk (W.growth (show j ≤ j+1 by omega))
    (H.levels.params (i+1)).columns_ge (hbank i)
  obtain ⟨ht, hinv, hr⟩ := sizes_of_direction hstep
  exact cone_step_arith hk (e := barunit (H.S.block i)) (by unfold barunit puffs; positivity)
    (by unfold puffs; positivity) ha (by positivity) hp hp' hrent (coeff_nonneg F u)
    (coeff_nonneg F _) ht h hinv (coeff_vowel F (H.S.block i) v) hr

/-! ### Propagation on the interval -/

private lemma gain_step (H : History G) (o i : ℕ) :
    gainChart H o i = gainChart H o (i+1) * puffs (H.S.block i) := by
  unfold gainChart puffs
  rw [H.S.scale_succ, Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1
  ring

/-- Cone in terms of each level's own cost (including the unit coordinate in
coeffSize), and discounted bound by the cost at the finest comparison level. -/
theorem cone_cost {W : Worth} {H : History G} (hC : roomCost H.levels W) (hbank : Bank W H.levels)
    {F : Labels.Frame G d} {B : SectionData F} {A : Hol G} {N p k o : ℕ}
    {P : Duet H F N p k o} {w : ℝ} (hP : Duet.Woke P A W B w)
    (i : ℕ) (hi : k ≤ i) (hi' : i ≤ o) :
    32*(1+(H.levels.params i).columns)^2 * F.coeffSize (P.voice i).x ≤ P.cost i ∧
    gainChart H o i * P.cost i ≤ P.cost o := by
  have cone (m : ℕ) (hm : k ≤ m) : m ≤ o →
      32*(1+(H.levels.params m).columns)^2 * F.coeffSize (P.voice m).x ≤ P.cost m := by
    induction m, hm using Nat.le_induction with
    | base =>
      intro hko
      have hn : 0 ≤ P.cost k := by
        obtain ⟨a,b,ha,hb,hab,-⟩ := (hP.origin k le_rfl hko).2
        exact (add_nonneg ha hb).trans hab
      simpa [hP.pairing, Labels.Frame.coeffSize] using hn
    | succ m hm ih =>
      intro hh
      exact (cone_step hC hbank (hP.funds m hm hh) (ih (by omega))).1
  refine ⟨cone i hi hi', ?_⟩
  induction hi' using Nat.decreasingInduction with
  | self => simp [gainChart]
  | of_succ j hj ih =>
    rw [gain_step, mul_assoc]
    have ha := (cone_step hC hbank (hP.funds j hi hj) (cone j hi hj.le)).2
    exact le_trans (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le) (ih (by omega))

/-- Boundary condition at the finest comparison level, closed using the cone. -/
theorem cost_finest {W : Worth} {H : History G} (hC : roomCost H.levels W) (hbank : Bank W H.levels)
    {F : Labels.Frame G d} {B : SectionData F} {A : Hol G} {N p k o : ℕ}
    {P : Duet H F N p k o} {w : ℝ} (hP : Duet.Woke P A W B w) :
    P.cost o ≤ 2*(1+(H.levels.params o).columns)*w := by
  have hh := (cone_cost hC hbank hP o hP.basic.1 le_rfl).1
  let C := (H.levels.params o).columns
  have he : 2*C * F.coeffSize (P.voice o).x ≤ P.cost o := by
    have hm : 2*C ≤ 32*(1+C)^2 := by
      have hp : 1 ≤ C := (H.levels.params o).columns_ge
      nlinarith only [hp, sq_nonneg C]
    exact (mul_le_mul_of_nonneg_right hm (coeff_nonneg F _)).trans hh
  dsimp only [C] at he
  linarith only [he, hP.spread]

theorem answer : YM.Bid.G09 := by
  intro G W H hC hbank N p d k o F B A P w _ hP i hi hi'
  obtain ⟨hh,hr⟩ := cone_cost hC hbank hP i hi hi'
  have hs : F.coeffSize (P.voice i).x ≤ P.cost i := by
    have hx := (H.levels.params i).columns_ge
    apply le_trans _ hh
    exact le_mul_of_one_le_left (coeff_nonneg F _) (by nlinarith only [hx])
  rw [mul_add]
  have hgam := mul_le_mul_of_nonneg_left hs (show 0 ≤ gainChart H o i from (Real.exp_pos _).le)
  linarith only [hgam, hr, cost_finest hC hbank hP]

end YM.Work.G09
