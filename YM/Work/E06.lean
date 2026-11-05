import YM.Bid.Energy
import YM.Corona.Fill

/-!
# F + I row lower bounds in a Plot

Use E04 for Mv/Mw size and shorten row + column/local-witness control.
A fine row's direct part finances the listed fine plaquettes, with surplus linear
income on the `swell`. In particular it is only **after summation** that we
heal F: in the dropped second component we pay the Mv cross term (small part
by counting dropped rows and large part by column bounds), not estimating
X on the assumption that the whole halo is good. Use only `Plot`'s actual
prerequisites, on the same S, T, k, U, V. No assumption of uniformity in x
before L and W are set.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.E06
open Filter Lattice RG Wilson Finset Precision Tree
open Pressure Pressure.Stores Pressure.Tube Pressure.Teller
open YM.Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

private lemma toll_nonneg (U : Config G f) (i : Cell f) : 0 ≤ toll U i :=
  G.chord_nonneg _

section geometry
variable {A : Stores S} {x w : ℝ} {U : Config G f} {k : S.Choices} {V : Config G c}

private lemma base_mem_start (S : StepData c f) (i : Cell f) :
    S.ratio.parent i.1 ∈ startPos S i :=
  mem_image_of_mem _ (by simp [touched, square, visits])

private lemma cost_at_home {i : Cell f} (hi : i ∈ A.costs) (b : ℕ) :
    S.ratio.parent i.1 ∈ A.dome b := by
  apply halo_subset
  apply mem_union_left
  apply mem_union_left
  exact mem_biUnion.mpr ⟨i, hi, base_mem_start ..⟩

private lemma aisle_at_home {i : Bond c} (hi : i ∈ A.aisles) (b : ℕ) :
    i.1 ∈ A.dome b := by
  apply halo_subset
  apply mem_union_left
  apply mem_union_right
  exact mem_biUnion.mpr ⟨i, hi, by simp [pinPos]⟩

private lemma limit_reach {i j : Cell f} (hi : i ∈ A.limit x)
    (hij : separation (S.ratio.parent i.1) (S.ratio.parent j.1) ≤ radiusB x / 50) :
    S.ratio.parent j.1 ∈ A.dome (5 * radiusB x) := by
  obtain ⟨o, ho, he⟩ := halo_spec.mp (show S.ratio.parent i.1 ∈ A.dome (2*radiusB x) from
    (mem_filter.mp hi).2)
  refine halo_spec.mpr ⟨o, ho, (separation_triangle o (S.ratio.parent i.1) _).trans ?_⟩
  omega

private lemma in_swell (p : A.Plot U k V x w) (ht : 0 ≤ fiery G x S.patch.L)
    {j : Cell f} (h : S.ratio.parent j.1 ∈ A.dome (5 * radiusB x))
    (hj : fiery G x S.patch.L < toll U j) : j ∈ A.swell U (fiery G x S.patch.L) := by
  apply mem_filter.mpr
  refine ⟨?_, hj⟩
  have he := (p.consumes j (fun hd => disjoint_left.mp hd h (base_mem_start S j))).2
  by_contra hn
  linarith only [ht, hj, he hn]
end geometry

-- Measure the multiplicity of a large endpoint on the ORIGINAL fine lattice, not
-- by pulling back a coarse halo and losing L^4.
private def clouds (a : Site f) (R y : ℝ) : Finset (Cell f) :=
  (halo (Nat.floor (Real.log y * R)) {a}) ×ˢ (Finset.univ : Finset PlaqAxes)

private def cloudPrice (R : ℝ) := (8*R + 1)^4 * (Fintype.card PlaqAxes : ℝ)

private lemma cloud_size (a : Site f) {y R : ℝ} (hy : 1 ≤ y) (hr : 0 ≤ R) :
    ((clouds a R y).card : ℝ) ≤ cloudPrice R * y := by
  let r := Nat.floor (Real.log y * R)
  have hf : (r : ℝ) ≤ Real.log y * R := Nat.floor_le (mul_nonneg (Real.log_nonneg hy) hr)
  have he : (r : ℝ) + r + 1 ≤ (8*R+1) * Real.exp (Real.log y / 4) := by
    have h := Real.add_one_le_exp (Real.log y / 4)
    have h1 := mul_le_mul_of_nonneg_right h hr
    nlinarith only [h, h1, hf, hr, Real.log_nonneg hy]
  have hp : Real.exp (Real.log y / 4) ^ 4 = y := calc
    _ = Real.exp (((4:ℕ):ℝ) * (Real.log y / 4)) := (Real.exp_nat_mul _ _).symm
    _ = _ := by norm_num; rw [show (4:ℝ) * (Real.log y / 4) = Real.log y by ring,
      Real.exp_log (lt_of_lt_of_le zero_lt_one hy)]
  have hn : (clouds a R y).card ≤ ((r+r+1)^4) * Fintype.card PlaqAxes := by
    unfold clouds
    rw [card_product, card_univ]
    apply Nat.mul_le_mul_right
    simpa using Corona.halo_size ({a} : Support f) r
  calc
    ((clouds a R y).card : ℝ) ≤ ((r:ℝ) + r + 1)^4 * (Fintype.card PlaqAxes : ℝ) := by
      exact_mod_cast hn
    _ ≤ ((8*R+1) * Real.exp (Real.log y / 4))^4 * (Fintype.card PlaqAxes : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he 4) (Nat.cast_nonneg _)
    _ = cloudPrice R * y := by rw [mul_pow, hp]; unfold cloudPrice; ring

private lemma cloud_mem {T : Tube G S} {t : ℝ} (ht : 0 < t) {U : Config G f} {i j : Cell f}
    (hj : t * Real.exp (separation i.1 j.1 / T.high.relaxation) < toll U j) :
    t < toll U j ∧ i ∈ clouds j.1 T.high.relaxation (toll U j / t) := by
  have hr := T.high.radius_pos
  have hf : t < toll U j := lt_of_le_of_lt (le_mul_of_one_le_right ht.le
    (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) hr.le))) hj
  have he : Real.exp (separation i.1 j.1 / T.high.relaxation) < toll U j / t :=
    (lt_div_iff₀ ht).mpr (by rw [mul_comm]; exact hj)
  rw [← Real.exp_log (div_pos (ht.trans hf) ht), Real.exp_lt_exp] at he
  refine ⟨hf, mem_product.mpr ⟨halo_spec.mpr ⟨j.1, mem_singleton_self _, ?_⟩, mem_univ _⟩⟩
  rw [separation_comm]
  exact Nat.le_floor ((div_lt_iff₀ hr).mp he).le

private def droppedRows (T : Tube G S) (A : Stores S) (x t : ℝ) (U : Config G f) :=
  (A.limit x).filter fun i => ¬ PathData.kept T.high t i.1 U

private lemma dropped_cost (T : Tube G S) (A : Stores S) {x C w : ℝ}
    {U : Config G f} {k : S.Choices} {V : Config G c} (p : A.Plot U k V x w)
    (ht : 0 < fiery G x S.patch.L)
    (E : LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent) :
    let t := fiery G x S.patch.L
    ((droppedRows T A x t U).card : ℝ) * t ≤
      cloudPrice T.high.relaxation * ∑ j ∈ A.swell U t, toll U j := by
  intro t
  let K := A.swell U t
  let X := droppedRows T A x t U
  let F (j : Cell f) := clouds j.1 T.high.relaxation (toll U j / t)
  have sub : X ⊆ K.biUnion F := by
    intro i hi
    obtain ⟨hi, hd⟩ : i ∈ A.limit x ∧ ¬ PathData.kept T.high t i.1 U := mem_filter.mp hi
    unfold PathData.kept at hd
    push Not at hd
    obtain ⟨j, hj⟩ := hd
    obtain ⟨hh, hs⟩ := cloud_mem (T := T) (U := U) (i := i) (j := j) ht hj
    exact mem_biUnion.mpr ⟨j, in_swell p ht.le (limit_reach hi (E.dropped U i.1 j hj)) hh, hs⟩
  have ha : X.card ≤ ∑ j ∈ K, (F j).card := (card_le_card sub).trans card_biUnion_le
  have hc : (X.card : ℝ) ≤ ∑ j ∈ K, ((F j).card : ℝ) := by exact_mod_cast ha
  change (X.card : ℝ) * t ≤ cloudPrice T.high.relaxation * ∑ j ∈ K, _
  refine le_trans (mul_le_mul_of_nonneg_right hc (show 0 ≤ t from ht.le)) ?_
  rw [sum_mul, mul_sum]
  apply sum_le_sum
  intro j hj
  have hu : t < toll U j := (mem_filter.mp (show j ∈ A.swell U t from hj)).2
  have ht' : 0 < t := ht
  refine (le_div_iff₀ ht').mp ?_
  rw [mul_div_assoc]
  exact cloud_size _ ((one_le_div ht').mpr hu.le) T.high.radius_pos.le

private lemma dropped_bill (T : Tube G S) (A : Stores S) {x C w : ℝ}
    {U : Config G f} {k : S.Choices} {V : Config G c} (p : A.Plot U k V x w)
    (ht : 0 < fiery G x S.patch.L) (hc : 0 ≤ C)
    (E : LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent) :
    let t := fiery G x S.patch.L
    ∑ i ∈ droppedRows T A x t U, ‖shorten T.up (till x) 1 U i‖ ≤
      C * (cloudPrice T.high.relaxation + 1) * ∑ j ∈ A.swell U t, toll U j := by
  intro t
  let K := A.swell U t
  let X := droppedRows T A x t U
  let M := crunch (n := f) T.up (till x) 1
  have column : (∑ i ∈ X, ∑ j ∈ K, M i j * toll U j) ≤ C * ∑ j ∈ K, toll U j := by
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro j _
    rw [← sum_mul]
    apply mul_le_mul_of_nonneg_right _ (toll_nonneg _ _)
    exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun i _ _ => E.attic i j))
      (E.back j)
  have row (i : Cell f) (hi : i ∈ X) :
      ∑ j, M i j * toll U j ≤ C * t + ∑ j ∈ K, M i j * toll U j := by
    rw [← sum_sdiff (subset_univ K)]
    apply add_le_add_left -- RHS and LHS add same ∑ j ∈ K
    calc
      _ ≤ ∑ j ∈ (univ \ K), M i j * t := by
        apply sum_le_sum
        intro j hj
        by_cases hm : M i j = 0
        · simp [hm]
        apply mul_le_mul_of_nonneg_left _ (E.attic ..)
        by_contra! he
        have hk : j ∈ K := in_swell p ht.le
          (limit_reach (mem_filter.mp hi).1 (E.maps _ _ (lt_of_le_of_ne (E.attic i j) (Ne.symm hm)))) he
        exact (mem_sdiff.mp hj).2 hk
      _ ≤ C * t := by
        rw [← sum_mul]
        apply mul_le_mul_of_nonneg_right _ ht.le
        exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => E.attic i j))
          (E.finite i)
  have count : (∑ _i ∈ X, C*t) ≤ C * (cloudPrice T.high.relaxation * ∑ j ∈ K, toll U j) := calc
    _ = C * ((X.card : ℝ) * t) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dropped_cost T A p ht E) hc
  calc
    _ ≤ ∑ i ∈ X, (C*t + ∑ j ∈ K, M i j * toll U j) :=
      sum_le_sum fun i hi => (E.valued i U).trans (row i hi)
    _ ≤ C * (cloudPrice T.high.relaxation * ∑ j ∈ K, toll U j) + C * ∑ j ∈ K, toll U j := by
      rw [sum_add_distrib]; exact add_le_add count column
    _ = _ := by unfold K; ring

-- Basic row arithmetic. Keep the direct and shorten components separate.
private def directPart (T : Tube G S) (U : Config G f) (V : Config G c)
    (x t : ℝ) (i : Cell f) :=
  let v := T.Mv (till x) (temp x) V (i,false)
  PathData.clipped T.high t (toll U i) + ‖v‖^2 / 2 - inner ℝ v (Pressure.shoot T.high U i)

private def secondPart (T : Tube G S) (U : Config G f) (V : Config G c)
    (x t : ℝ) (i : Cell f) :=
  let v := T.Mv (till x) (temp x) V (i,true)
  trunk T.up T.high (till x) 1 t U i + ‖v‖^2 / 2 - inner ℝ v (shorten T.up (till x) 1 U i)

private lemma partsF (T : Tube G S) (U : Config G f) (V : Config G c)
    (x t : ℝ) (i : Cell f) :
    T.workF (till x) U V t (temp x) i = directPart T U V x t i + secondPart T U V x t i := by
  simp [directPart, secondPart, Tube.workF, crown, toll, Tube.Xf, plotted]
  ring

private lemma square_bound {m r : ℝ} (hm : 0 ≤ m) (v y : G.Color)
    (hy : ‖y‖ ≤ Real.sqrt m * r) :
    (Real.sqrt m * r - ‖v‖)^2 / 2 ≤ m * r^2/2 + (‖v‖^2 / 2 - inner ℝ v y) := by
  have hi := le_trans (real_inner_le_norm v y) (mul_le_mul_of_nonneg_left hy (norm_nonneg v))
  calc
    _ = m * r^2 / 2 + (‖v‖^2 / 2 - ‖v‖ * (Real.sqrt m * r)) := by
      nlinarith only [show Real.sqrt m ^ 2 * r^2 = m * r^2 by rw [Real.sq_sqrt hm]]
    _ ≤ _ := by linarith only [hi]

private lemma shoot_norm (T : Tube G S) (U : Config G f) (i : Cell f) :
    ‖Pressure.shoot T.high U i‖ ≤ Real.sqrt T.high.direct * toll U i := by
  rw [Pressure.shoot, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)

private lemma square_direct (T : Tube G S) (U : Config G f) (V : Config G c)
    (x t : ℝ) (i : Cell f) (hi : toll U i ≤ t) :
    let v := T.Mv (till x) (temp x) V (i,false)
    (Real.sqrt T.high.direct * toll U i - ‖v‖)^2 / 2 ≤ directPart T U V x t i := by
  intro v
  calc
    _ ≤ T.high.direct * toll U i ^ 2 / 2 + (‖v‖^2 / 2 - inner ℝ v (Pressure.shoot T.high U i)) :=
      square_bound T.high.quadratic_pos.le v _ (shoot_norm T U i)
    _ = _ := by simp only [directPart, v, PathData.clipped, if_pos hi]; ring

private lemma square_noise (T : Tube G S) (Q V : Config G c) (x : ℝ) (i : Bond c) :
    let v := T.Mw (till x) (temp x) V i
    (Real.sqrt S.kernel.penalty * wire Q V i - ‖v‖)^2 / 2 ≤ T.workI (till x) Q V (temp x) i := by
  intro v
  apply square_bound S.kernel.penalty_pos.le v
  rw [Z, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)

private lemma direct_pay (T : Tube G S) (A : Stores S)
    {x ε w : ℝ} {U : Config G f} {k : S.Choices} {V : Config G c}
    (p : A.Plot U k V x w) (ht : 0 ≤ fiery G x S.patch.L)
    (M : ∀ i, ‖T.Mv (till x) (temp x) V i‖ ≤ ε * fiery G x S.patch.L)
    (hquad : ε ≤ Real.sqrt T.high.direct / 8)
    (hlin : ε * Real.sqrt T.high.direct ≤ T.high.linear / 4) :
    let t := fiery G x S.patch.L; let K := A.swell U t
    (3/4*T.high.linear * t * ∑ i ∈ K, toll U i) +
      (T.high.direct/128) * t^2 * ((A.costs \ K).card : ℝ) ≤
        ∑ i ∈ A.limit x, directPart T U V x t i := by
  intro t K
  let a := T.high.direct
  let b := T.high.linear
  let F := directPart T U V x t
  have ac : 0 ≤ a := T.high.quadratic_pos.le
  have ht' : 0 ≤ t := ht
  have hcost : A.costs ⊆ A.limit x := fun i hi =>
    mem_filter.mpr ⟨mem_univ _, cost_at_home hi _⟩
  have hK : K ⊆ A.costs := filter_subset ..
  have hsmall (i : Cell f) (hi : i ∈ A.costs \ K) : a / 128 * t ^ 2 ≤ F i := by
    let v := T.Mv (till x) (temp x) V (i,false)
    obtain ⟨hi, hk⟩ := mem_sdiff.mp hi
    have hu : toll U i ≤ t := le_of_not_gt fun h =>
      hk (mem_filter.mpr ⟨hi, h⟩)
    have hm : t/4 ≤ toll U i := (p.consumes i (fun h =>
      disjoint_left.mp h (cost_at_home hi _) (base_mem_start ..))).1 hi
    have hd : Real.sqrt a * t / 8 ≤ Real.sqrt a * toll U i - ‖v‖ := by
      have he : ‖v‖ ≤ Real.sqrt a / 8 * t :=
        (M (i,false)).trans (mul_le_mul_of_nonneg_right hquad ht)
      have hx : Real.sqrt a * (t/4) ≤ Real.sqrt a * toll U i :=
        mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg a)
      linarith only [he, hx]
    refine le_trans ?_ (square_direct T U V x t i hu)
    change _ ≤ (Real.sqrt a * toll U i - ‖v‖)^2 / 2
    have eq : (Real.sqrt a * t / 8)^2 / 2 = a / 128 * t^2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt ac]; ring
    rw [← eq]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hd 2) (by norm_num)
  have hlarge (i : Cell f) (hi : i ∈ K) : 3/4*b*t*toll U i ≤ F i := by
    let y := Pressure.shoot T.high U i
    let v := T.Mv (till x) (temp x) V (i,false)
    let r := toll U i
    have he : t < r := (mem_filter.mp hi).2
    have hr : ‖v‖ * ‖y‖ ≤ ε * t * (Real.sqrt a * r) :=
      mul_le_mul (M (i,false)) (shoot_norm T U i) (norm_nonneg _) ((norm_nonneg _).trans (M (i,false)))
    have hx : inner ℝ v y ≤ b / 4 * t * r := calc
      _ ≤ ‖v‖ * ‖y‖ := real_inner_le_norm ..
      _ ≤ ε * t * (Real.sqrt a * r) := hr
      _ = (ε * Real.sqrt a) * (t*r) := by ring
      _ ≤ b / 4 * (t*r) := mul_le_mul_of_nonneg_right hlin (mul_nonneg ht' (toll_nonneg ..))
      _ = b / 4 * t * r := by ring
    change 3/4*b*t*r ≤ PathData.clipped T.high t r + ‖v‖^2 / 2 - inner ℝ v y
    rw [PathData.clipped, if_neg (not_le.mpr he)]
    change 3/4*b*t*r ≤ b*t*r + ‖v‖^2 / 2 - inner ℝ v y
    linarith only [hx, sq_nonneg ‖v‖]
  calc
    _ = (∑ i ∈ A.costs \ K, a/128*t^2) + ∑ i ∈ K, 3/4*b*t*toll U i := by
      simp only [sum_const, nsmul_eq_mul, ← mul_sum, a, b]; ring
    _ ≤ (∑ i ∈ A.costs \ K, F i) + ∑ i ∈ K, F i :=
      add_le_add (sum_le_sum hsmall) (sum_le_sum hlarge)
    _ = ∑ i ∈ A.costs, F i := sum_sdiff hK
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg hcost ?_
      intro i hi hx
      have hu : toll U i ≤ t := le_of_not_gt fun h => hx (hK
        (in_swell p ht (limit_reach hi (j := i) (by simp)) h))
      exact le_trans (by positivity) (square_direct T U V x t i hu)

private lemma heal (T : Tube G S) (A : Stores S) {x C ε w : ℝ}
    {U : Config G f} {k : S.Choices} {V : Config G c}
    (p : A.Plot U k V x w) (ht : 0 < fiery G x S.patch.L)
    (hc : 0 ≤ C) (hε : 0 ≤ ε)
    (M : ∀ i, ‖T.Mv (till x) (temp x) V i‖ ≤ ε * fiery G x S.patch.L)
    (E : LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent)
    (margin : ε * (C * (cloudPrice T.high.relaxation + 1)) ≤ T.high.linear/4) :
    let t := fiery G x S.patch.L
    let K := A.swell U t
    (-(T.high.linear / 4 * t * ∑ i ∈ K, toll U i)) ≤
      ∑ i ∈ A.limit x, secondPart T U V x t i := by
  intro t K
  let Z := ∑ i ∈ K, toll U i
  let u := shorten T.up (till x) 1 U
  let X := droppedRows T A x t U
  have hm : ε*t*(∑ i ∈ X, ‖u i‖) ≤ T.high.linear/4*t*Z := calc
    _ ≤ ε*t*(C * (cloudPrice T.high.relaxation + 1) * Z) :=
      mul_le_mul_of_nonneg_left (dropped_bill T A p ht hc E) (mul_nonneg hε ht.le)
    _ = ε*(C*(cloudPrice T.high.relaxation + 1))*(t*Z) := by ring
    _ ≤ T.high.linear/4*(t*Z) := mul_le_mul_of_nonneg_right margin
      (mul_nonneg ht.le (sum_nonneg fun i _ => toll_nonneg ..))
    _ = T.high.linear/4*t*Z := by ring
  have hx (i : Cell f) (hi : i ∈ X) : -(ε*t*‖u i‖) ≤ secondPart T U V x t i := by
    have he := (mem_filter.mp (show i ∈ droppedRows T A x t U from hi)).2
    let v := T.Mv (till x) (temp x) V (i,true)
    have hy : inner ℝ v (u i) ≤ ε*t*‖u i‖ :=
      (real_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (M (i,true)) (norm_nonneg _))
    simp only [secondPart, trunk, if_neg he, zero_add]
    change _ ≤ ‖v‖^2 / 2 - inner ℝ v (u i)
    linarith only [sq_nonneg ‖v‖, hy]
  calc
    _ ≤ ∑ i ∈ X, (-(ε*t*‖u i‖)) := by rw [sum_neg_distrib, ← mul_sum]; exact neg_le_neg hm
    _ ≤ ∑ i ∈ X, secondPart T U V x t i := sum_le_sum hx
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg (filter_subset ..) ?_
      intro i hi hx
      have hh : PathData.kept T.high t i.1 U := by
        by_contra h
        exact hx (mem_filter.mpr ⟨hi,h⟩)
      let v := T.Mv (till x) (temp x) V (i,true)
      simp only [secondPart, trunk, if_pos hh]
      change _ ≤ ‖u i‖^2/2 + ‖v‖^2/2 - inner ℝ v (u i)
      nlinarith only [real_inner_le_norm v (u i), sq_nonneg (‖v‖ - ‖u i‖)]

private lemma noise_pay (T : Tube G S) (A : Stores S) {x C w : ℝ}
    {U : Config G f} {k : S.Choices} {V : Config G c}
    (p : A.Plot U k V x w) (ht : 0 ≤ fiery G x S.patch.L)
    (H : ∀ i, ‖T.Mw (till x) (temp x) V i‖ ≤ C * fiery G x S.patch.L)
    (space : C ≤ Real.sqrt S.kernel.penalty/2 * w) :
    let Q := S.prediction U k
    S.kernel.penalty/8 * (∑ i ∈ A.aisles, (wire Q V i)^2) ≤ A.talli T x Q V := by
  intro Q
  let t := fiery G x S.patch.L
  let a := S.kernel.penalty
  have elem (i : Bond c) (hi : i ∈ A.aisles) : a / 8 * wire Q V i ^ 2 ≤ T.workI (till x) Q V (temp x) i := by
    let n := wire Q V i
    let v := T.Mw (till x) (temp x) V i
    have ha := Real.sqrt_nonneg a
    have hn : 0 ≤ n := G.chord_nonneg _
    have he : w*t ≤ n := (p.drive i (fun hd =>
      disjoint_left.mp hd (aisle_at_home hi _) (by simp [pinPos]))).1 hi
    have hv : ‖v‖ ≤ Real.sqrt a/2 * n := calc
      _ ≤ C * t := H i
      _ ≤ Real.sqrt a/2 * w * t := mul_le_mul_of_nonneg_right space ht
      _ = Real.sqrt a/2 * (w*t) := by ring
      _ ≤ Real.sqrt a/2 * n := mul_le_mul_of_nonneg_left he (by positivity)
    refine le_trans ?_ (square_noise T Q V x i)
    change a / 8 * n^2 ≤ (Real.sqrt a * n - ‖v‖)^2 / 2
    have eq : (Real.sqrt a * n / 2)^2 / 2 = a / 8 * n^2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (show 0 ≤ a from S.kernel.penalty_pos.le)]
      ring
    rw [← eq]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hv]) 2
  rw [mul_sum]
  refine le_trans (sum_le_sum elem) (sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, aisle_at_home hi _⟩
  intro i _ _
  exact le_trans (by positivity) (square_noise T Q V x i)

private lemma pays_L (P : Teller G) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
    C / (n:ℝ)^2 ≤ Real.sqrt P.top.clip.direct / 8 ∧
    C / (n:ℝ)^2 * Real.sqrt P.top.clip.direct ≤ P.top.clip.linear/4 ∧
    C / (n:ℝ)^2 * (C*(cloudPrice P.top.clip.relaxation + 1)) ≤ P.top.clip.linear/4 := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => C / (n:ℝ)^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have hz : 0 < Real.sqrt P.top.clip.direct := Real.sqrt_pos.2 P.top.clip.quadratic_pos
  have hp := P.top.clip.tail_pos
  refine Eventually.and (h.eventually (ge_mem_nhds ?_))
    (Eventually.and ((h.mul_const _).eventually (ge_mem_nhds ?_))
      ((h.mul_const _).eventually (ge_mem_nhds ?_)))
  all_goals first | positivity | rw [zero_mul]; positivity

/-- The column and witness bills only cost `O(1/L²)` times the swell currency at
fixed pre-L data. Commit the L floor, then ask for large enough W, then use the
late x tail (including E04) at those parameters. -/
theorem answer : Bid.E06 := by
  intro a e G P
  obtain ⟨C, hp, E⟩ := e a P
  obtain ⟨N,hN⟩ := eventually_atTop.mp (pays_L P C)
  refine ⟨N, fun L hh => ?_⟩
  let r := Real.sqrt P.bind.penalty / 2
  have hr : 0 < r := div_pos (Real.sqrt_pos.2 P.bind.penalty_pos) (by norm_num)
  filter_upwards [eventually_ge_atTop (C / r)] with w hw
  refine ⟨P.top.clip.direct/128, div_pos P.top.clip.quadratic_pos (by norm_num), ⟨?_⟩⟩
  filter_upwards [(E L w).late,
    eventually_gt_atTop (-(G.slopeConstant * Real.log L.val))] with x hx hy
  have ht : 0 < fiery G x L := by
    have : 0 < betaF G x L := by unfold betaF; linarith only [hy]
    unfold fiery temp; positivity
  intro c f S hl hcf T H F A U k V hf p
  obtain ⟨hU, -, hM⟩ := hx c f S hl hcf T H F A U k V hf p
  subst L
  have hb := hN S.patch.L.val hh
  rw [← H.high] at hb
  obtain ⟨hQ,hL,hE⟩ := hb
  constructor
  · have h1 := direct_pay T A p ht.le hM.phi hQ hL
    have h2 := heal T A p ht hp.le (by positivity) hM.phi hU hE
    rw [← H.high]
    simp_rw [Stores.tally, partsF, sum_add_distrib]
    linarith only [h1, h2]
  · have hw' : C ≤ r*w := by rw [mul_comm]; exact (div_le_iff₀ hr).mp hw
    exact noise_pay T A p ht.le hM.hot (by rw [H.knobs]; exact hw')

end YM.Work.E06
