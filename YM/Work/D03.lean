import YM.Bid.Drops

/-!
# One-slot forward differences in the ordered extraction

At each cutoff the featured moment of the forward difference is a difference of two
ordinary moments. Reindex the finite sum. Eventually the shifted test can be evaluated
by shifting the physical corner on the cover (check both possible nonzero values at the
period seam). The backward test quotient plus `down` then tends uniformly to zero and is
supported in one separated compact. Its cost at each sufficiently large fixed period
tends to zero at the mesh tail of that period. No uniform-in-period count of grid points
is needed for this fuse estimate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.D03
open Set Filter Function MeasureTheory Analysis Extraction Extraction.Lease Dash Lattice Wilson
open Bid (heighten targetB)
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal

variable {G : Gauge} {C : Family G} {d n N p : ℕ}

/-- Shift one slot by one edge in lattice units. -/
def jump {A : Type*} [Zero A] [One A] (i : Fin n) (a : Axis) : Fin n → Four A :=
  Pi.single i (step a)

lemma featuring_heighten (x : C.label d) (v : Shot C.book) (a : Axis)
    (r : Fin v.n → Site (C.side N p)) :
    featuring (heighten C d x a) v.left v.i N p r = (C.S.a N : ℂ)⁻¹ *
      (C.numeric N p (v.record x) (r + jump v.i a) - C.numeric N p (v.record x) r) := by
  classical
  let M (s : Fin v.n → Site (C.side N p)) (U : Config G (C.side N p)) :=
    ∏ j : Fin v.n, C.seen (v.record x j) (s j) U
  let E (U : Config G (C.side N p)) := ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (r j) U
  have hE (s : Fin v.n → Site (C.side N p)) U (hs : ∀ j ≠ v.i, s j = r j) :
      M s U = C.O N p (d:=d) x (s v.i) U * E U := by
    dsimp only [M]; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.i)]
    congr 1
    · rw [show v.record x v.i=⟨d,x⟩ by simp [Shot.record]]
      rfl
    refine Finset.prod_congr rfl fun j hj => ?_
    have h := Finset.ne_of_mem_erase hj
    rw [show v.record x j=v.left j by simp [Shot.record,h], hs j h]
  have hf (U : Config G (C.side N p)) : (∏ j : Fin v.n, if j=v.i then heighten C d x a N p (r v.i) U
      else C.seen (v.left j) (r j) U) = (C.S.a N:ℂ)⁻¹ * (M (r+jump v.i a) U - M r U) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.i), if_pos rfl]
    rw [show (∏ j ∈ Finset.univ.erase v.i, if j=v.i then heighten C d x a N p (r v.i) U
      else C.seen (v.left j) (r j) U) = E U from
      Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)]
    rw [hE _ U (by intro j hj; simp [jump,hj]), hE r U (by simp)]
    simp only [Pi.add_apply, jump, Pi.single_eq_same, heighten, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hi s : Integrable (M s) (law G _ (C.beta N p)) := C.integrableR (v.record x) s
  rw [C.num, C.num, ← integral_sub (hi _) (hi _), ← integral_const_mul]
  unfold featuring moment; simp_rw [hf]

/-- Exact discrete summation by parts (even across period seams). -/
lemma pair_sum {s A : Type*} [AddGroup s] [Fintype s] [CommRing A]
    (f g : s → A) (u : s) (k : A) :
    (∑ r : s, f r * (k * (g (r+u)-g r))) = ∑ r : s, (k * (f (r-u)-f r)) * g r := by
  have he := Equiv.sum_comp (Equiv.addRight u) (fun r => f (r-u)*g r)
  change (∑ r, f ((r+u)-u)*g (r+u)) = _ at he
  simp only [add_sub_cancel_right] at he
  calc
    _ = k * ((∑ r, f r*g (r+u)) - ∑ r, f r*g r) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by
      rw [he, ← Finset.sum_sub_distrib, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma on_lattice (x : C.label d) (v : Shot C.book) (a : Axis) (N p : ℕ) :
    targetB (heighten C d x a) v N p = (C.S.a N:ℂ)^(4*v.n) *
      ∑ r : Fin v.n → Site (C.side N p), ((C.S.a N:ℂ)⁻¹ *
          (v.f (Order.cells C N p (r-jump v.i a)) - v.f (Order.cells C N p r))) *
        C.numeric N p (v.record x) r := by
  simp_rw [targetB, featuring_heighten x v]
  exact congr_arg ((C.S.a N:ℂ)^(4*v.n)*·) (pair_sum (fun r => v.f (Order.cells C N p r)) ..)

lemma tag_add_jump (t : ℝ) (s : Fin n → Cover) (i a) :
    tag t (s + jump i a) = tag t s + t • Points.direction i a := by
  ext1 j; ext b
  by_cases h : j = i
  · subst j; by_cases e : b = a <;> simp [tag, jump, Points.direction, mul_add, e]
  simp [tag, jump, Points.direction, h]

lemma tag_sub_jump (t : ℝ) (s : Fin n → Cover) (i a) :
    tag t (s - jump i a) = tag t s - t • Points.direction i a := by
  apply eq_sub_of_add_eq
  exact (tag_add_jump t (s-jump i a) i a).symm.trans (congr_arg (tag t) (sub_add_cancel s _))

lemma wrap_jump (s : Side) (i : Fin n) (a : Axis) (j : Fin n) :
    wrap s (jump i a j) = jump i a j := by
  by_cases h : j = i
  · subst j; simp [jump]
  simp [jump, h]

lemma cells_lift (C : Family G) (r : Fin n → Site (C.side N p)) :
    Order.cells C N p r = tag (C.S.a N) (lift ∘ r) := rfl

lemma cells_tag_inside (C : Family G) (u : Fin n → Cover)
    (h : tag (C.S.a N) u ∈ Inside C.S p n) :
    Order.cells C N p (wrap _ ∘ u) = tag (C.S.a N) u := by
  rw [cells_lift]; congr 1
  funext j; apply lift_eq_iff.mpr
  refine ⟨rfl, fun b => ?_⟩
  have H := h j b
  change -C.S.radius p < C.S.a N * (u j b:ℝ) ∧ C.S.a N * (u j b:ℝ) < C.S.radius p at H
  rw [Schedule.radius, ← C.S.span_side N p] at H
  have H' : -((C.side N p).val:ℝ) < 2 * (u j b:ℝ) ∧ 2 * (u j b:ℝ) ≤ (C.side N p).val := by
    change -( (C.S.side N p).val:ℝ) < 2 * (u j b:ℝ) ∧ 2 * (u j b:ℝ) ≤ (C.S.side N p).val
    constructor <;> nlinarith [C.S.a_pos N]
  exact_mod_cast H'

/-- At sufficiently large fixed period (then small mesh), evaluate the shifted test
in summation by parts without wrapping. It suffices that its original support and
one translate lie strictly inside the comparison cell. -/
lemma physical (C : Family G) (f : Test n) (i : Fin n) (a : Axis)
    (hi : tsupport f ⊆ Inside C.S p n)
    (hj : ∀ y ∈ tsupport f, y + C.S.a N • Points.direction i a ∈ Inside C.S p n)
    (r : Fin n → Site (C.side N p)) : f (Order.cells C N p (r-jump i a)) =
      f (Order.cells C N p r - C.S.a N • Points.direction i a) := by
  let t := C.S.a N
  let z := r - jump i a
  rcases eq_or_ne (f (Order.cells C N p z)) 0 with hl|hl
  · rcases eq_or_ne (f (Order.cells C N p r - t • Points.direction i a)) 0 with hr|hr
    · exact hl.trans hr.symm
    have he := hi (subset_closure (show Order.cells C N p r - t • Points.direction i a ∈ support f from hr))
    let u := (lift ∘ r) - jump i a
    have hw : wrap _ ∘ u = z := funext fun j => by simp [u,z,comp_def,wrap_jump]
    rw [cells_lift C r, ← tag_sub_jump] at he ⊢
    exact congr_arg f ((congr_arg (Order.cells C N p) hw.symm).trans (cells_tag_inside C u he))
  have he := hj _ (subset_closure (show Order.cells C N p z ∈ support f from hl))
  let u := (lift ∘ z) + jump i a
  have hw : wrap _ ∘ u = r := funext fun j => by simp [u,z,comp_def,wrap_jump]
  rw [cells_lift, ← tag_add_jump] at he
  have HH := cells_tag_inside C u he
  rw [hw, tag_add_jump] at HH
  rw [HH,add_sub_cancel_right]; rfl

def residue (f : Test n) (i : Fin n) (a : Axis) (t : ℝ) (y : Points n) : ℂ :=
  (t:ℂ)⁻¹ * (f (y - t • Points.direction i a) - f y) + down f i a y

lemma uniform (f : Test n) (i : Fin n) (a : Axis) (S : Schedule) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ y, ‖residue f i a (S.a N) y‖ ≤ ε := by
  let P := Points.direction i a
  let D := fderiv ℝ (⇑f)
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show (⊤ : ℕ∞)≠0 by simp)
  have he : UniformContinuous D := (f.hasCompactSupport.fderiv ℝ).uniformContinuous_of_continuous
    (f.contDiff.continuous_fderiv hn)
  obtain ⟨δ,hδ,h⟩ := Metric.uniformContinuous_iff.mp he ε hε
  filter_upwards [S.shrinks.eventually (gt_mem_nhds hδ)] with N hN y
  let t := S.a N
  have ht := S.a_pos N
  have hT : ‖t • P‖ = t := by simp [norm_smul, Real.norm_eq_abs, t, abs_of_pos ht, P, Points.direction]
  have hv := (convex_ball y δ).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => f.contDiff.differentiable hn z) (φ := D y)
      (fun z hz => (dist_eq_norm (D z) (D y) ▸ h (Metric.mem_ball.mp hz)).le)
      (Metric.mem_ball_self hδ) (show y-t • P∈Metric.ball y δ by
        rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,hT]; exact hN)
  have hc : residue f i a t y = (t:ℂ)⁻¹ * (f (y-t • P) - f y - D y ((y-t • P)-y)) := by
    rw [sub_sub_cancel_left,map_neg,map_smul, Complex.real_smul, residue]
    change (t:ℂ)⁻¹ * (f (y - t • P) - f y) + D y P = _
    have h0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    field_simp; ring
  rw [hc,norm_mul,norm_inv,Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [sub_sub_cancel_left, norm_neg, hT] at hv
  rw [sub_sub_cancel_left]
  calc
    _ ≤ t⁻¹ * (ε * t) := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr ht.le)
    _ = ε := by field_simp [t, ht.ne']

lemma period_cost (S : Schedule) (M : (Fin n → Site (S.side N p)) → ℂ) (c : ℝ)
    (h : ∀ r, ‖M r‖ ≤ c) : ‖(S.a N:ℂ)^(4*n) * ∑ r, M r‖ ≤ (length S p)^(4*n) * c := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.a_pos _)]
  have he : ‖∑ r, M r‖ ≤ ((S.side N p).val:ℝ)^(4*n)*c := by
    calc
      _ ≤ ∑ _r : Fin n → Site (S.side N p), c := (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => h j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                    ZMod.card, ← pow_mul, nsmul_eq_mul, Nat.cast_pow]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg (S.a_pos _).le _)).trans_eq
  rw [← mul_assoc, ← mul_pow, S.span_side]

variable {F : Extraction.Order}

lemma error_sum (x : C.label d) (v : Shot C.book) (a : Axis) (B : Bound C F) :
    Tendsto (fun j : ℕ × ℕ => targetB (heighten C d x a) v j.1 j.2 +
      Order.smears C j.1 j.2 (v.record x) (down v.f v.i a)) F.fuse (𝓝 0) := by
  obtain ⟨K,hK,hx,hc⟩ := exists_compact_between
    (v.f.hasCompactSupport.union (down v.f v.i a).hasCompactSupport) (conf_open _)
    (union_subset (show tsupport v.f ⊆ conf _ from v.f.tsupport_subset)
      (show tsupport (down v.f v.i a) ⊆ conf _ from (down v.f v.i a).tsupport_subset))
  have hK1 := subset_union_left.trans hx
  have hK2 := subset_union_right.trans (hx.trans interior_subset)
  obtain ⟨δ,hδ,h⟩ := v.f.hasCompactSupport.exists_thickening_subset_open isOpen_interior hK1
  let P := Points.direction v.i a
  have hs : ∀ᶠ N : ℕ in atTop, ∀ y ∈ tsupport v.f, y + C.S.a N • P ∈ K := by
    filter_upwards [C.S.shrinks.eventually (gt_mem_nhds hδ)] with N hN y hy
    apply interior_subset (h (Metric.mem_thickening_iff.mpr ⟨y,hy,?_⟩))
    rw [dist_eq_norm,add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (C.S.a_pos _)]
    simpa [P, Points.direction] using hN
  obtain ⟨D,hD,H⟩ := B.volume v.n (v.record x) K hK hc
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Order.fused, Order.late]
  filter_upwards [H, F.per.cofinal.eventually (room C.S hK)] with k hk hper
  let p := F.per k
  have hp : 0 < length C.S p := by unfold length; positivity
  let V := length C.S p ^ (4*v.n)
  have hV : 0 < V := pow_pos hp _
  let e := ε / (V * (D+1))
  have hDen : 0 < V*(D+1) := mul_pos hV (by linarith)
  have he := uniform v.f v.i a C.S (show 0 < e from div_pos hε hDen)
  filter_upwards [hk, F.mesh.cofinal.eventually hs, F.mesh.cofinal.eventually he] with j hj ht he
  let N := F.mesh j
  let t := C.S.a N
  have Ht (r : Fin v.n → Site (C.side N p)) := physical C v.f v.i a
    (hK1.trans (interior_subset.trans hper)) (fun y hy => hper (ht y hy)) r
  let q := Order.cells C N p (n:=v.n)
  let M (r : Fin v.n → Site (C.side N p)) := residue v.f v.i a t (q r) * C.numeric N p (v.record x) r
  have hr (r) : ‖M r‖ ≤ e*D := by
    by_cases hh : q r ∈ K
    · have hw := hj (lift ∘ r) (show tag t (lift ∘ r) ∈ K from hh)
      rw [lifted,show wrap _ ∘ lift ∘ r = r from funext fun i => wrap_lift (r i)] at hw
      dsimp only [M]; rw [norm_mul]
      exact mul_le_mul (he _) hw (norm_nonneg _) (div_nonneg hε.le hDen.le)
    have h1 : v.f (q r) = 0 := by_contra fun h => hh (interior_subset (hK1 (subset_closure h)))
    have h2 : down v.f v.i a (q r) = 0 := by_contra fun h => hh (hK2 (subset_closure h))
    have h3 : v.f (q r - t • P) = 0 := by
      by_contra h
      exact hh (sub_add_cancel (q r) (t • P) ▸ ht (q r-t • P) (subset_closure h))
    have h0 : M r = 0 := by dsimp only [M,residue]; rw [h1,h2,h3]; ring
    rw [h0,norm_zero]; exact mul_nonneg (div_nonneg hε.le hDen.le) hD
  have Hsum : targetB (heighten C d x a) v N p + Order.smears C N p (v.record x) (down v.f v.i a) =
      (C.S.a N:ℂ)^(4*v.n) * ∑ r, M r := by
    rw [on_lattice, Order.smears, ← mul_add, ← Finset.sum_add_distrib]; congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only [M,residue,q]; rw [Ht r, ← add_mul]
  change dist (targetB _ v N p + _) 0 < ε
  rw [dist_zero_right, Hsum]
  apply (period_cost C.S M (e*D) hr).trans_lt
  change V * (e*D) < ε
  have hw : e * (V * (D + 1)) = ε := div_mul_cancel₀ ε hDen.ne'
  nlinarith [mul_pos (show 0 < e from div_pos hε hDen) hV]

theorem answer : YM.Bid.D03 := by
  intro G C S F _ H B live d x a v
  have he := Order.along (H.reads v.n (v.record x) (down v.f v.i a))
  have hl := (error_sum x v a B).sub he
  rw [zero_sub] at hl
  exact (hl.congr (fun j => add_sub_cancel_right ..))
end YM.Work.D03
