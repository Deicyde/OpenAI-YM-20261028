import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Issued
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Trunk

/-!
# V predicted affine energy is paid even on arbitrary formal V away from
holes on the footprint. Using $\mu_0$ later consumes **this** cancellation.

Select a gauge separately even for two calls though fitting their later
estimates simultaneously. Origin far from trivial holonomy is not an
error state.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Win Rates
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section patch

def cert (S : StepData c f) (x : ℝ) (A : Stores S) (V : Config G c) :=
    100*(1+radiusB x)≤c.val ∧ A.flags=RG.flags (temp x) V

/-- Obtain a linear extension about one gauge patch (7 radius powers,
post-burn). Avoids ALL rough V there through actual output locus; no
assumption on V thresholds in any unreported sector data. -/
lemma remote_frame (G : Gauge) (D : Patch) (k : ℕ) (hk : k≤40) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (_h : S.patch=D) (A : Stores S) (V : Config G c), cert S x A V →
    let B := radiusB x
    ∀ y : Site c, y∉A.dome ((k+1)*B) → ∃ (z : Site c→G.El) (a : LogField G c),
      ‖a‖ ≤ allowance G D x 1 7 ∧ AgreeNear id y (k*B) (gauge z V) (represent a) := by
  obtain ⟨C,δ,hC,hd,he⟩ := extend_interior G
  filter_upwards [tariff_paid G D (k+1), (vanishes G D 6).eventually (ge_mem_nhds hd),
    Work.E01.radiusB_tendsto.eventually_ge_atTop 1, grow G D C (by decide : 6<7) 1]
    with x hx hu hv ht c f S hh A V hV B y hy
  have hz : 0<B := hv
  have hs : 100*(1+B) ≤ c.val := hV.1
  have hm : (k+1)*B ≤ 41*B := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨z,hz⟩ := reduceV S V A x hV.2 ((k+1)*B) (k*B) (by rw [Nat.add_mul]; omega) y hy (by omega)
  obtain ⟨a,ha,hb⟩ := he id y (k*B) (gauge z V) _ (allowance_nn G D x 1 6) hu fun i hi => (hz i hi).trans hx
  exact ⟨z,a,ha.trans ht,hb⟩

lemma vacancy (x : ℝ) (A : Stores S) (V : Config G c) {i : Site c} (r : ℕ)
    (h : A.flags= RG.flags (temp x) V) (he : i∉A.dome r) : ∀ j, separation i j ≤ r → j∉ RG.flags (temp x) V := by
  intro j hj hf
  rw [← h] at hf
  exact he (halo_spec.mpr ⟨j,Finset.mem_union_right _ hf,(separation_comm ..).trans_le hj⟩)
end patch

lemma shadow_copy (g : Ratio c f) (b : LogField G c) :
    let a := linearCopy g (collect G b)
    replica g (represent b)=represent (form a) ∧ ‖form a‖ ≤ ‖b‖ := by
  intro a
  refine ⟨?_,(pi_norm_le_iff_of_nonneg (norm_nonneg b)).mpr ?_⟩
  · rw [← exp_copy]; unfold represent; rw [collect_form]
  rintro j; change ‖a _‖ ≤ _
  unfold a linearCopy; split
  next => rw [norm_zero]; exact norm_nonneg _
  next => exact norm_le_pi_norm b _

lemma shares_copy (S : StepData c f) {U W : Config G c} {y : Site c} {k : ℕ} (h : AgreeNear id y k U W) :
    AgreeNear S.ratio.parent y k (replica S.ratio U) (replica S.ratio W) := by
  intro i hi; unfold replica; split
  next => rfl
  next => exact h _ hi

lemma first_bill (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c) (_F : Forest S.ratio),
      P.Funds S T → S.patch=D → 100*(1+radiusB x)≤c.val →
      let R := till x; let B := radiusB x
      ∀ (k : S.Choices) (i : Pos S) (b : LogField G c),
      ‖b‖≤allowance G D x 1 p → AgreeNear id (base S i) B V (represent b) →
      (∀ j,separation (base S i) j≤B → j∉RG.flags (temp x) V) →
      let t := forecast T i (form (linearCopy S.ratio (collect G b))) b
      ‖t‖≤ allowance G D x 1 (p+1) ∧
        ‖target T R (temp x) i k V (replica S.ratio V) - t‖ ≤ allowance G D x 2 (p+p+3) := by
  filter_upwards [late_cost P D hD p, he.receipt D.L, prepare D] with x hx ht hh c f S T V F h hS hL R B k i b hb hd hf t
  have hp := shadow_copy S.ratio b
  have hu : AgreeNear id (base S i) (radial (till x) S.patch) V (represent b) := hd.shrink (by
    rw [hS,separation_self,zero_add]; exact hh.2.trans (Nat.div_le_self ..))
  have hm := (ht c f S T h (congr_arg Patch.L hS) hL F V).2.1
  rw [target_unveiled _ _ _ _ _ _ hm hf,primal_local T (till x) i _ (h.knobs.symm ▸ h.kernel) (shares_copy _ hu) hu,hp.1]
  exact (hx c f S T h hS _ _ (hp.2.trans hb) hb).2 k i

lemma replica_norm (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c) (A : Stores S) (_F : Forest S.ratio),
      P.Funds S T → S.patch=D → cert S x A V →
      ∀ (k : S.Choices) (i : Pos S), i∈choosing A (radiusB x) →
      ‖target T (till x) (temp x) i k V (replica S.ratio V)‖ ≤ allowance G D x 1 9 := by
  filter_upwards [first_bill P C he D hD 7, burn G D 1 (7+7+3) 1 1 (by norm_num),
    Rates.widen G D 1 (show 0≤7+1 by decide),Rates.grow G D 2 (show 7+1<9 by decide) 1,
    remote_frame G D 1 (by norm_num)] with x ht hx hp hk hv c f S T V A F hh hS hm k i hi
  let B := radiusB x; let y := base S i
  have hl : y∉A.dome (8*B) := (mem_filter.mp hi).2
  obtain ⟨z,a,ha,hw⟩ := hv c f S hS A V hm y (fun hz => hl (placed A _ _ (by omega) hz))
  have hd p (h : separation (base S i) p ≤ B) : p∉ flags (temp x) (gauge z V) := by
    rw [gauge_flags]; apply vacancy x A V (8*B) hm.2 hl; unfold y; omega
  rw [one_mul] at hw
  obtain ⟨h1,h2⟩ := ht c f S T _ F hh hS hm.1 k i a ha hw hd
  let t := target T (till x) (temp x) i k V (replica S.ratio V)
  have hy : target T (till x) (temp x) i k (gauge z V) (replica S.ratio (gauge z V)) = G.adjoint (z y) t := by
    rw [← copied S.ratio S.patch.odd_side V z]; exact target_gauge P hh .. 
  rw [hy] at h2
  change ‖t‖ ≤ _
  rw [← G.norm_adjoint (z y) t]
  have hh := norm_le_norm_sub_add (G.adjoint (z y) t) (forecast T i (form (linearCopy S.ratio (collect G a))) a)
  linarith only [h1,h2,hx,hp,hk,hh]

lemma shot_budget (P : Teller G) (p : ℕ) (D : Patch) : ∀ᶠ x : ℝ in atTop, ∀ (c f : Side)
    (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (b : LogField G c),
    S.patch=D → P.Funds S T → ‖b‖≤allowance G D x 1 p →
    ∀ i : Bond f, ‖attempt T F b i‖ ≤ allowance G D x 1 (p+2) := by
  filter_upwards [absolute_response P p D,grow G D 2 (show p+1<p+2 by omega) 1,
    Rates.widen G D 1 (show p≤p+1 by omega)] with x hx hy hv c f S T F b hD h hb i
  let a := collect G (station T F b) i
  let B := allowance G D x 1 (p+1)
  have hi : ‖a‖ ≤ B := (norm_le_pi_norm _ (pole i)).trans (hx c f S T h hD b hb F)
  have hf : ‖linearCopy S.ratio (collect G b) i‖ ≤ B := by
    unfold linearCopy; split
    next => rw [norm_zero]; exact allowance_nn ..
    next => exact (norm_le_pi_norm b _).trans (hb.trans hv)
  change ‖a-_‖ ≤ _; exact (norm_sub_le ..).trans ((add_le_add hi hf).trans (by linarith only [hy,show 2*B≤_ from hy]))

/-- Ungauged statement of the local row estimate. Needs SAME `b` to pay
using the actual extensions even at neighboring rows. Projection (freeze)
not used here: for the active set later, large seed margins ensure that
projection won't change the tested row. -/
lemma unfrozen (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c)
      (F : Forest S.ratio) (k : S.Choices), S.patch=D → 100*(1+radiusB x)≤c.val →
      P.Funds S T → ∀ (A B : Bed), Alongside A B T →
      ∀ (b : LogField G c) (i : Pos S), let r := radiusB x; let z := base S i
      ‖b‖ ≤ allowance G D x 1 p → AgreeNear id z r V (represent b) →
      (∀ j,separation z j≤r → j∉ flags (temp x) V) →
      let R := till x
      ‖target T R (temp x) i k V (replica S.ratio V) + derivative T R i V (attempt T F b)‖ ≤
        allowance G D x 2 (p+p+9) := by
  filter_upwards [first_bill P C he D hD p, shot_budget P p D,
    chord_price G D p, residual_cost P D hD (p+1) (p+2), prepare D,
    Rates.widen G D 2 (show p+p+3≤p+1+(p+2)+4 by omega),
    Rates.grow G D 2 (show p+1+(p+2)+4<p+p+9 by omega) 2] with x hx hw hz he hm hy hQ c f S T V F k hS hs hT A B hA b i r z hv hk hf R
  let a := linearCopy S.ratio (collect G b); let W := attempt T F b
  obtain ⟨-,h'⟩ := hx c f S T V F hT hS hs k i b hv hk hf
  have hd : ‖forecast T i (form W) 0-derivative T R i V W‖ ≤ allowance G D x 2 (p+1+(p+2)+4) := by
    apply he c f S T hS hT i V W _ (hw _ _ S T F b hS hT hv)
    intro j hj; rw [hk j (Nat.le_trans hj ?_)]; apply hz c b hv j
    unfold r; omega
  have ht : station T F b=form a + form W := by
    have hw : station T F b = form (a+W) := by unfold W attempt a; rw [add_sub_cancel, form_collect]
    exact hw
  have hr : forecast T i (station T F b) b = 0 := by
    obtain ⟨h1,h2⟩ := escape T hA hT i.1 F b
    unfold forecast
    cases i with | mk s u => rcases u with i|i <;> simp only [h1,h2,Sum.elim_inl,Sum.elim_inr,
      sub_self]
  let X := target T R (temp x) i k V (replica S.ratio V)
  let Y := derivative T R i V W; let H := forecast T i (form a) b; let t := forecast T i (form W) 0
  rw [ht, forecast_step hT] at hr
  change ‖X+Y‖≤_
  rw [show X+Y=(X-H)-(t-Y) by rw [eq_neg_of_add_eq_zero_left (show H+t=0 from hr)]; abel]
  apply le_trans ((norm_sub_le ..).trans (add_le_add (h'.trans hy) hd)); linarith only [hQ]
end YM.AnalyticNext.ConnectedActivity.Aff
