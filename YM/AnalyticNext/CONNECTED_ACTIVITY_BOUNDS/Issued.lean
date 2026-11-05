import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Forecast
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Rate
import YM.Progress.STATIONARY_SCENES.Response

/-!
# Use with `allowance` budget; one more power of B at a time

At this point in the proof we can fix the actual patch after L. All powers
of t are in fine cut-chart units, not the shooting β. Combine
these receipts with others with the SAME data and with β on its range.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Rates
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- convenient stencil radius receipt
lemma prepare (D : Patch) : ∀ᶠ x : ℝ in atTop,
    4*stencilD D (till x)+10 ≤ radiusB x/4 ∧ radial (till x) D ≤ radiusB x/4 := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (1000*(1+predReach D))] with x hx
  unfold stencilD radial till; omega

lemma late_cost (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (a : LogField G f) (b : LogField G c),
      let r := allowance G D x 1 p; let W := allowance G D x 1 (p+1); let Z := allowance G D x 2 (p+p+3)
      ‖a‖≤r → ‖b‖≤r →
      let R := till x; let U := represent a; let V := represent b
      (∀ i, let N := zip (flatN T) (Limage T b) i; ‖N‖≤W ∧ ‖primalN T R V i-N‖ ≤ Z) ∧
      ∀ (k : S.Choices) (y : Pos S), let F := forecast T y a b
        ‖F‖ ≤ W ∧ ‖primal T R y k V U - F‖ ≤ Z := by
  obtain ⟨C,τ,r,hC,hτ,hr,H⟩ := ordered_cost P D hb
  filter_upwards [(Rates.vanishes G D p).eventually (ge_mem_nhds hr), Rates.grow G D C (by omega : p<p+1) 1,
    Rates.decay G D hτ 1 0 1, Rates.widen G D 1 (by omega : 0 ≤ p+1), Work.E01.radiusB_tendsto.eventually_ge_atTop 1,
    Rates.grow G D (3*C) (show p+(p+1)<p+p+3 by omega) 2] with x h1 h2 h3 h4 h5 h6 c f S T hT hD a b Y W Z ha hy R U V
  have he : (1:ℝ)≤(radiusB x) := by exact_mod_cast h5
  have hv : 0 ≤ Y := allowance_nn ..
  have hw : C*Y*Next.Fluctuations.widen R Y τ ≤ Z := by
    have hp : (radiusB x:ℝ)*Y=W := by unfold W Y allowance Rates.pieces; rw [pow_succ]; ring
    have hm : (till x:ℝ) ≤ radiusB x := by exact_mod_cast Nat.div_le_self (radiusB x) 100000
    simp only [Rates.pieces, pow_zero, mul_one, one_mul] at h3
    have hf : Next.Fluctuations.widen R Y τ ≤ 3*W := by
      unfold Next.Fluctuations.widen
      have hh := h3.trans h4
      change Real.exp (-τ*R) ≤ W at hh; change (R:ℝ) ≤ (radiusB x:ℝ) at hm
      linarith [mul_le_mul_of_nonneg_right hm hv, mul_le_mul_of_nonneg_right he hv]
    calc
      _ ≤ C*Y*(3*W) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = 3*C*(Y*W) := by ring
      _ ≤ Z := by unfold Y W; rw [Rates.exchange]; exact h6
  constructor
  · intro i; obtain ⟨hu,hv⟩ := (H c f S T hT hD a b Y h1 ha hy R Classical.ofNonempty).1 i
    exact ⟨hu.trans h2,hv.trans hw⟩
  intro k y; obtain ⟨hu,hv⟩ := (H c f S T hT hD a b Y h1 ha hy R k).2 y
  exact ⟨hu.trans h2,hv.trans hw⟩

lemma residual_cost (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) (p r : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
    ∀ (a : Pos S) (V : Config G c) (v : Directions G f),
      let t := till x; let d := stencilD D t
      (∀ i : Bond c, separation (base S a) i.1 ≤ 4*d + 1 → G.chord (V i) ≤ allowance G D x 1 p) →
      (∀ i, ‖v i‖ ≤ allowance G D x 1 r) →
      ‖forecast T a (form v) 0- derivative T t a V v‖ ≤ allowance G D x 2 (p+r+4) := by
  obtain ⟨C,hC,H⟩ := perturb P D hb
  filter_upwards [Rates.grow G D (P.top.paths*4) (show r<p+r+2 by omega) 2,
    Rates.decay G D P.top.width_pos 1 0 1, prepare D,
    Rates.grow G D C (show p+r+1<p+r+2 by omega) 2,
    Rates.grow G D 2 (show p+r+2<p+r+4 by omega) 2]
    with x hf hh hp hc hw c f S T hD hT a V v t d hv hu
  let X := allowance G D x 1 p
  let Y := allowance G D x 1 r
  let Z := allowance G D x 2 (p+r+2)
  have hz : 0≤X := allowance_nn ..
  have hY : 0≤Y := allowance_nn ..
  have h : ‖derivative T t a V v-derivative T t a 1 v‖ ≤ Z := by
    have he y : separation (base S a) y.1 ≤ 4*stencilD S.patch t+1 → G.chord (V y) ≤ X := by
      rw [hD]; apply hv y
    have hh (y : Bond f) (_ : separation (base S a) (home S y) ≤ stencilD S.patch t+1) := hu y
    apply le_trans (H _ _ S T hD hT t a v Y X hY hz hh V he)
    rw [hD]
    calc
      _ ≤ C*(radiusB x)*X*Y := by
        have hi : (((4*d:ℕ):ℝ)+1) ≤ radiusB x := by
          exact_mod_cast (show 4*d+1 ≤ radiusB x by unfold d t; omega)
        gcongr
      _ ≤ Z := by
        change _ ≤ allowance G D _ _ _
        convert hc using 1; unfold X Y allowance Rates.pieces; ring
  have hi := leave P x T hT a v Y hY hu
  simp only [Rates.pieces,pow_zero,mul_one,one_mul] at hh
  have ht := le_trans hi (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (P.top.paths_pos.le)) (by positivity : 0 ≤ (4 : ℝ))) hY)
  have ht : ‖forecast T a (form v) 0 - derivative T t a 1 v‖ ≤ Z := ht.trans <| le_trans
    (le_of_eq (show allowance G D x 1 0 * P.top.paths * 4 * Y = P.top.paths*4*allowance G D x 2 r by
      unfold Y allowance Rates.pieces; ring)) hf
  apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (derivative T t a 1 v) _)
  rw [norm_sub_rev (derivative T t a 1 v)]; exact (add_le_add ht h).trans ((two_mul Z).symm ▸ hw)

lemma chord_price (G : Gauge) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ (n : Side) (a : LogField G n), ‖a‖ ≤ allowance G D x 1 p →
      ∀ i : Bond n,G.chord (represent a i) ≤ allowance G D x 1 (p+1) := by
  obtain ⟨C,r,hC,hr,H⟩ := chord_chart_cost G
  filter_upwards [(vanishes G D p).eventually (ge_mem_nhds hr), Rates.grow G D C (by omega : p<p+1) 1]
    with x hx hc n a ha i
  have hu : ‖a (pole i)‖ ≤ allowance G D x 1 p := (norm_le_pi_norm a (pole i)).trans ha
  change G.chord (G.lieExp (a (pole i))*1) ≤ _; rw [mul_one]
  exact ((H _ (hu.trans hx)).trans (mul_le_mul_of_nonneg_left hu hC.le)).trans hc

lemma absolute_response (P : Teller G) (p : ℕ) (D : Patch) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch = D →
    ∀ (b : LogField G c), ‖b‖ ≤ allowance G D x 1 p → ∀ (F : Forest S.ratio),
      ‖station T F b‖ ≤ allowance G D x 1 (p+1) := by
  let N : ℝ := max 1 (Response.total D.J P.η P.C)
  let n : ℝ := Fintype.card G.ColorIndex
  have hn : 0 < N := zero_lt_one.trans_le (le_max_left ..)
  filter_upwards [Rates.grow G D (Real.sqrt n * N) (by omega : p<p+1) 1] with x hv c f S T h hD b he F
  let K := extracted S F (installed S.ratio T.R.A0)
  let E := allowance G D x 1 p
  have hq := allowance_nn G D x 1 p
  have ht := ((h.crosses).2.2.2 [] (Nat.zero_le _)).1
  simp only [advanceC,List.length_nil,add_zero,pow_one] at ht
  apply (pi_norm_le_iff_of_nonneg (allowance_nn G D ..)).mpr; intro i
  have hy (j : G.ColorIndex) : |station T F b i j| ≤ N*E := by
    have hY := Response.response_price S P.width.le ht F i
    have hs : ∑ u : Body 1 c, |K i u| ≤ N := by
      apply le_trans _ (le_trans hY (show Response.total S.patch.J P.η P.C ≤ N from hD.symm ▸ le_max_right ..))
      refine Finset.sum_le_sum fun i _ => le_mul_of_one_le_left (abs_nonneg _) ?_
      apply Real.one_le_exp; have h := P.width; positivity
    calc
      _ ≤ ∑ u, |K i u * parts G 1 b j u| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ u, |K i u| * E := Finset.sum_le_sum fun u _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((piece_cost (b u) j).trans ((norm_le_pi_norm b u).trans he))
          (abs_nonneg _)
      _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hs hq
  have hz : ‖station T F b i‖^2 ≤ n*(N*E)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply le_trans (Finset.sum_le_sum (g:=fun _ => (N*E)^2) ?_) (le_of_eq ?_)
    · intro j _; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy j) _
    simp [n]
  apply le_trans _ hv
  have hp := Nat.cast_nonneg (α:=ℝ) (Fintype.card G.ColorIndex)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt n*N*allowance G D x 1 p)).mp
  rw [mul_assoc,mul_pow,Real.sq_sqrt]; exact hz; exact hp
end YM.AnalyticNext.ConnectedActivity.Aff
