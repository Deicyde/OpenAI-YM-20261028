import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bedrock
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mint
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Odometer

/-!
# Pay the entire `scope` of inverses now

Continues the actual-producer cost on affine Born supports (E §:ew).
Large-$L$ not even needed for this line. Every call will have
`Ringing` on precise L and J and V, so we use quantifier over every S
and Va and the chosen T. Mold is finite input; θ credit for actual
trajectory elsewhere even after this step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Win Rates Green Mint Win.Promise
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

abbrev paceR (x : ℝ) := radiusB x/4

lemma install_promises (P : Teller G) (D : Patch) (h : D.Branches P.bind G) :
    ∃ (B : Win.Promise) (u : Turns), u.exp_width ≤ B.alpha ∧
    ∀ᶠ x : ℝ in atTop, u.pace (paceR x) < 1 ∧
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c) (A : Stores S) (F : Forest S.ratio),
      P.Funds S T → S.patch=D → cert S x A V →
      let v := gram T F x A V
      B.Served v (dcol S) ∧ u.Takes (eyes S G (radiusB x)) v (dcol S) (paceR x) := by
  obtain ⟨B,hb⟩ := bedrock P D h
  obtain ⟨u,hu,hx⟩ := Win.Promise.receive B
  refine ⟨B,u,hu,?_⟩
  have he : Tendsto paceR atTop atTop := tendsto_atTop.mpr fun i => by
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (4*i+4)] with x hx
    unfold paceR; omega
  filter_upwards [hb,he.eventually hx] with x hb hh
  refine ⟨hh.1,fun c f S T V A F hP hD ha => ?_⟩
  let v := gram T F x A V
  have h := hb c f S T hP hD ha.1 F A V ha.2
  exact ⟨h,hh.2 c (Vars G f) (dcol S) _ (roomB S _) _ h⟩

lemma shrink_pace (u : Turns) (G : Gauge) (D : Patch) (n : ℕ) (B : ℝ) (hB : 0≤B) :
    ∀ᶠ x : ℝ in atTop, B*u.pace (paceR x) ≤ allowance G D x n 0 := by
  filter_upwards [Rates.decay G D u.wins n 0 (B*u.expense)] with x h
  simp only [Rates.pieces, pow_zero,mul_one] at h
  apply le_trans _ h
  unfold Turns.pace
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg hB u.bought.le)
  have ht : (till x:ℝ) ≤ (paceR x:ℝ) := Nat.cast_le.mpr (by unfold till paceR; omega)
  linarith [mul_le_mul_of_nonneg_left ht u.wins.le]

-- utilities for projected use
lemma takes_sub {A : Stores S} {x : ℝ} {T : Tube G S} {F : Forest S.ratio} (C : Mint T F A x)
    (a : ArrayR G f) :
    C.μ - a = - ((eyes S G (radiusB x)).within C.sheet).transpose *ᵥ (C.sheet *ᵥ a+C.source) +
      ((eyes S G (radiusB x)).error C.sheet).transpose *ᵥ a := by
  let v := C.sheet; let Y := eyes S G (radiusB x)
  have he : (Y.error v).transpose = (Y.within v).transpose*v-1 := by
    rw [Windows.error, Matrix.transpose_sub, Matrix.transpose_mul,show v.transpose=v from steal .., Matrix.transpose_one]
  change - ((Y.within v).transpose *ᵥ C.source) - _ = _ + (Y.error v).transpose *ᵥ a
  rw [he, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  rw [neg_mulVec,mulVec_add]
  abel

-- row_ball for free use at zero columns
lemma span (u : Turns) {x : ℝ} (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (V : Config G c)
    (h : u.Takes (eyes S G (radiusB x)) (gram T F x A V) (dcol S) (paceR x)) :
    let W := eyes S G (radiusB x); let v := gram T F x A V
    Green.Both (dcol S) (dcol S) (W.within v) u.exp_width u.base u.base ∧
      Green.Both (dcol S) (dcol S) (W.error v) u.exp_width (u.pace (paceR x)) (u.pace (paceR x)) := by
  obtain ⟨-,h1,h2,h3⟩ := h.greens (1:ℝ) ⟨zero_le_one,le_rfl⟩
  intro W v
  have he : Win.Promise.flows v 1=v := by unfold Win.Promise.flows ResolventVolume.graph; rw [one_smul]; abel
  rw [he] at h1 h2
  exact ⟨h1,h2⟩

lemma towers_source (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) (X : Turns) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (Y : Mint T F A x), cert S x A Y.V →
      0 < Y.u → Y.u ≤ allowance G D x 1 p →
      X.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x) →
      (∀ i, |Y.origin i| ≤ allowance G D x 1 (p+10)) ∧
      (∀ i, |Y.source i| ≤ allowance G D x 1 (p+11)) ∧
      ∀ i, |Y.μ i| ≤ allowance G D x 1 (p+12) := by
  obtain ⟨W,hW,hc⟩ := gram_budget P D hD
  filter_upwards [replica_norm P C he D hD, Rates.widen G D 1 (show p≤p+9 by omega),
    Rates.widen G D 1 (show 9≤p+9 by omega), Rates.grow G D (Real.sqrt weight+W*2) (show p+9<p+10 by omega) 1,
    Rates.grow G D W (show p+10<p+11 by omega) 1, Rates.grow G D X.base (show p+11<p+12 by omega) 1]
    with x hx h1 h2 h3 h4 h5 c f S T hS hT A F Y hv hu hl hX
  have hf := hc c f S T hT hS F A Y.V x
  have ha : 0≤P.top.width/2 := (half_pos P.top.width_pos).le
  have hs i : |Y.sh i| ≤ 2*allowance G D x 1 (p+9) := calc
    _ ≤ ‖lie Y.sh i.1‖ := piece_cost _ i.2
    _ ≤ _ := (fixes Y hu i.1).trans (mul_le_mul_of_nonneg_left (hl.trans h1) (by positivity))
  let B := allowance G D x 1 (p+9)
  have he i : |Y.origin i| ≤ allowance G D x 1 (p+10) := by
    unfold origin zeroed; split
    next ht =>
      have hv := hx c f S T Y.V A F hT hS hv Y.k i.1 ht
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      apply (add_le_add (mul_le_mul_of_nonneg_left ((piece_cost _ _).trans (hv.trans h2)) (Real.sqrt_nonneg _))
        (row_ball _ _ _ hf.unmasked.1 ha _ (show 0 ≤ 2*B from mul_nonneg (by norm_num) (allowance_nn ..))
          i fun j _ => hs j)).trans
      calc _ = _ := (show Real.sqrt weight*B+W*(2*B)=(Real.sqrt weight+W*2)*B by ring)
           _ ≤ _ := h3
    next ht => rw [abs_zero]; exact allowance_nn ..
  have hP i : |Y.source i| ≤ allowance G D x 1 (p+11) := (row_ball _ _ _ hf.affine.2 ha _
    (allowance_nn G D x 1 (p+10)) i fun j _ => he j).trans h4
  refine ⟨he,hP,fun i => ?_⟩
  unfold Mint.μ Windows.center
  rw [Pi.neg_apply, abs_neg]
  exact (row_ball _ _ _ (span X T F A _ hX).1.2 X.wide.le _ (allowance_nn G D x 1 (p+11)) i fun j _ => hP j).trans h5
end YM.AnalyticNext.ConnectedActivity.Aff
