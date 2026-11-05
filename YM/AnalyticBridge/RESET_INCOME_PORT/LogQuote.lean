import YM.AnalyticBridge.RESET_INCOME_PORT.Quote
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.Next.SCHEDULE.Stadium
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.PRICE_COMPILER.Builders
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.ResidualPrice
import YM.SectorNext.VACUUM_NORMALIZATION.Etch
import YM.UVNext.COUPLING_RESET.Reset



set_option warningAsError false

/-!
# Actual Gram and covariance Quotes at incoming scalar probes

Use opaqueCost and etching on the matched Plate. Log Q price to
arbitrary precision, and AC term can even use prediction zero if already
late enough after the chosen rolls. No symmetric-AC hypothesis, no
acknowledgement of severe cancellations until AFTER formation of the
tables in these prices. `forecast` uses a finite set of actual table
contractions rather than calling for either exact log det. It is
for order-zero coupon / slip price only: truncation may see large
parts of the torus. Not saying that it automatically supplies winding
or support priced localized log determination in tag/fields (Etch locality
needs paying crown positions in compatible windows) or a pre-L ticket
or a cheap per-block coefficient of the output action. Estimates work in
all dimensions/periods tested at that one smoothing stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Rows
open SectorNext.Vacuum.Panel UVNext.CouplingReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {V : Config G c} {R : Rep G f}

namespace Etcher
variable {J I : Type} [Fintype J] [DecidableEq J]
omit [DecidableEq J] in
private lemma solvency {L : Gaussian.Table J} {η v C : ℝ} {p : J → Site c} (hv : 0≤v)
    (ht : Pours L p p v C) (h : Gapped L η) {M : ℝ} (hl : C≤M) : Numeric L η M := by
  intro a; have hh := (estimate (ht.weaker hv hl) a a); rw [sumSq_dot] at hh; rw [← sumSq_dot]
  exact ⟨h a, (le_abs_self _).trans (hh.trans (by rw [sumSq_dot]; linarith))⟩

omit [DecidableEq J] in
private lemma swap [Fintype I] (g : I ≃ J) {A : Gaussian.Table J} {η L : ℝ} (h : Numeric A η L) :
    Numeric (A.submatrix g g) η L := by
  intro a; let b (i : J) := a (g.symm i)
  have he (i : I) : b (g i)=a i := by simp [b]
  have ht : (b ⬝ᵥ b)=(a ⬝ᵥ a) := by
    rw [dotProduct,← g.sum_comp (fun i => b i*b i)] -- notation elaboration
    simp only [he,dotProduct]
  have hm : (b ⬝ᵥ (A *ᵥ b))=(a ⬝ᵥ ((A.submatrix g g) *ᵥ a)) := by
    unfold mulVec dotProduct; dsimp only
    rw [← g.sum_comp (fun i => b i * ∑ j,A i j*b j)]; apply Finset.sum_congr rfl; intro i _
    rw [← g.sum_comp (fun j => A (g i) j*b j)]; simp only [he]; rfl
  have H := h b; rwa [ht,hm] at H

def serial (A : Gaussian.Table J) (L : ℝ) (q : ℕ) := ∑ i : J, headLine A L q i

private lemma gate {A : Gaussian.Table J} {η L : ℝ} (hh : A.IsHermitian) (h : Numeric A η L)
    (hi : 0<η) (hg : η≤L) (k : ℕ) : |Real.log A.det-serial A L k| ≤ Fintype.card J * mist η L k := by
  rw [log_form A hh h hi hg,serial, ← Finset.sum_sub_distrib]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => faith A hh h hi hg k i)

structure Specs where
  η : ℝ
  L : ℝ
  u : ℝ
  C : ℝ
  gap : 0 < η
  hi : η < L
  pos : 0 < u
  pay : 0 < C

def steam (X : Specs) (x : ℝ) := X.C * Real.exp (-X.u*radiusB x)

def forecast (X : Specs) (e : Plate G S) (k : ℕ) (A : Stores S) (V : Config G c) (u : S.Choices) : Quote :=
  let n : ℝ := Fintype.card (Rows.In e.x A e.forest (G:=G))
  let g := e.Gram A V u
  ⟨serial g X.L k - serial e.Flat X.L k, 0,
   (n+ Fintype.card (Key e.forest G))*mist X.η X.L k,n * steam X e.x⟩

/-- Uniform numeric accuracy at fixed L. NO extra quote-correctness
hypotheses. Works for arbitrary shared assemblies later on Rolls path
checking the entrance tests (including the Cosmos path after checking delay!). -/
theorem table (G : Gauge) (P : Patch) (T : Teller G) (hb : P.Branches T.bind G) :
    ∃ X : Specs, ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (e : Plate G S),
      S.patch=P → 100*(1+radiusB x) ≤ c.val → T.Funds S e.tube → e.x=x →
        ∀ (A : Stores S) (V : Config G c), e.matched A V → ∀ u k, (forecast X e k A V u).Pays e A V u := by
  obtain ⟨v,D,η,b,E,hv,hD,hη,hb',hE,H⟩ := opaqueCost G P T hb
  obtain ⟨u,A,hu,hA,H'⟩ := ResidualPrice.paid_kernel G P T hb
  let X : Specs := ⟨η,η+D+1,u,A,hη,by linarith,hu,hA⟩
  refine ⟨X,?_⟩; filter_upwards [H,H'] with x hx hy
  intro c f S e hs ht hp he M V hm y k
  rw [← he] at hx hy ht
  obtain ⟨hr,hq,hH,hL,hJ⟩ := hx S e.tube hs ht hp M e.forest y V hm
  have hi : Numeric (e.Gram M V y) X.η X.L := solvency hv.le hr hq (by dsimp [X]; linarith)
  let B : Stores S := ⟨∅,∅,∅⟩
  have ht' : B.flags=RG.flags (temp e.x) (1:Config G c) := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_ |>.symm
    intro i hh
    obtain ⟨p,-,H⟩ := (flags_spec ..).mp hh
    exact (temp_nonneg _).not_gt (by simpa [faceValue,square,travel] using H)
  obtain ⟨hU,hV,hK,-⟩ := hx S e.tube hs ht hp B e.forest e.tag 1 ht'
  have hh : Numeric (e.Gram B 1 e.tag) X.η X.L := solvency hv.le hU hV (by dsimp [X]; linarith)
  have hw : Numeric e.Flat X.η X.L ∧ e.Flat.PosDef := by
    rw [show e.Flat = (e.Gram B 1 e.tag).submatrix (Native.lineEquiv e.forest e.x) (Native.lineEquiv e.forest e.x) from
      (Native.ground_gram e.tube e.forest e.tag e.x (Push.SectorMeasure.funds_branch hp)).symm]
    exact ⟨swap _ hh,Matrix.PosDef.submatrix hK (Native.lineEquiv ..).injective⟩
  constructor
  · have h₁ := abs_le.mp (gate hH.isHermitian hi X.gap X.hi.le k)
    have h₂ := abs_le.mp (gate hw.2.isHermitian hw.1 X.gap X.hi.le k)
    unfold forecast; dsimp only
    -- show aliases
    change -_ ≤ _ ∧ _ ≤ _ at h₁ h₂
    unfold Plate.Gram
    exact abs_le.mpr ⟨by linarith only [h₁.1,h₂.2],by linarith only [h₁.2,h₂.1]⟩
  unfold forecast; dsimp only; rw [sub_zero]; exact (hy S e.tube hs ht hp M e.forest y V hm).1

/-- Mist from *finite number* of iterations, not assuming trace
series absolutely on each walk. -/
lemma buffers (X : Specs) : ∃ a D : ℝ, 0<a ∧ 0<D ∧ ∀ n : ℕ,
    mist X.η X.L n = D * Real.exp (-a*n) := by
  let v := steep X.η X.L
  have hx := X.gap.trans X.hi
  have ht : 0<v := sub_pos.mpr ((div_lt_one hx).mpr X.hi)
  have hv : v<1 := sub_lt_self _ (div_pos X.gap hx)
  refine ⟨-Real.log v,(1-v)⁻¹,neg_pos.mpr (Real.log_neg ht hv), inv_pos.2 (sub_pos.mpr hv),?_⟩
  intro n; rw [neg_neg,mul_comm _ (n:ℝ),Real.exp_nat_mul,Real.exp_log ht]; exact mul_comm ..

private lemma keys_cost (c f : Side) (S : StepData c f) (e : Plate G S) (A : Stores S) :
    (Fintype.card (Rows.In e.x A e.forest (G:=G)) : ℝ) ≤ Fintype.card (Key e.forest G) ∧
    (Fintype.card (Key e.forest G) : ℝ) ≤ sites c * (Fintype.card Axis * Fintype.card G.ColorIndex * (S.patch.L.val:ℝ)^4) := by
  unfold Rows.In Key; simp_rw [Fintype.card_prod,Nat.cast_mul]
  have ht : Fintype.card e.forest.Free ≤ (Fintype.card (Site f) * Fintype.card Axis) :=
    (Fintype.card_le_of_injective _ (Subtype.val_injective (p:=fun p : Bond f=>p∉e.forest.trunks))).trans_eq
      (Fintype.card_prod ..)
  have he : sites f = sites c * (S.patch.L.val:ℝ)^4 := by unfold sites; rw [site_card, site_card,S.sizes]; push_cast; ring
  constructor
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity); norm_cast
    exact Fintype.card_le_of_injective _ (Subtype.val_injective (p:=fun p : e.forest.Free=>¬ chill A e.x e.forest p))
  have hz : (Fintype.card e.forest.Free:ℝ) ≤ sites f * Fintype.card Axis := by unfold sites; exact_mod_cast ht
  exact (mul_le_mul_of_nonneg_right hz (by positivity)).trans_eq (by rw [he]; ring)

/-- Comparison with any strictly positive requested money in *same E
output units*. This demonstrates that the Quote.Pays contribution itself
can be resolved to Reset precision (e.g. ζ=multiplier/64) with explicit
finite prices. NOT a similar smallness estimate on the actual determinant
(main prediction may be large!). Conversion doesn't purport to say how
costly those forecasts will be in spatial volumes; this is before
pricing the logarithmic curve/numerator estimates at such probes. -/
theorem accuracy (X : Specs) (L : Side) (G : Gauge) (ζ : ℝ) (hz : 0<ζ) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (e : Plate G S),
    e.x=x → S.patch.L=L → ∀ (A : Stores S) V u, (forecast X e (radiusB x) A V u).tip ≤
      sites c*(ζ*(Vac.Numbers.Hat x)^((11:ℝ)/5)) := by
  obtain ⟨a,D,ha,hD,h⟩ := buffers X
  let K : ℝ := Fintype.card Axis*Fintype.card G.ColorIndex*(L.val:ℝ)^4
  have hK : 0≤K := by unfold K; positivity
  let b := (K*(2*D+X.C))/(2*ζ)
  filter_upwards [Extra.Iteration.Scales.first a 3 ha, Extra.Iteration.Scales.first X.u 3 X.pos,
      eventually_gt_atTop (1:ℝ),eventually_ge_atTop b] with x hx hy hk ht
  have he : Vac.Numbers.Hat x = x^(-(1/2:ℝ)) := by
    rw [Vac.Numbers.Hat,Real.sqrt_eq_rpow,Real.rpow_neg (by linarith)]
  have hp : Vac.Numbers.Hat x ^ ((11:ℝ)/5) = x ^ (-(11/10:ℝ)) := by
    rw [he, ← Real.rpow_mul (by linarith : 0≤x)]; norm_num
  have hf : 0 ≤ steam X x := mul_nonneg X.pay.le (Real.exp_pos _).le
  intro c f S e hu hL A V u
  unfold Quote.tip forecast; dsimp only
  obtain ⟨hi,hv⟩ := keys_cost c f S e A
  rw [hL] at hv
  rw [hu,h,hp]
  have H : K*(2*(D*Real.exp (-a*radiusB x))+steam X x) ≤ 2*(ζ * x^(-(11/10:ℝ))) := by
    have hh : K*(2*D+X.C) ≤ 2*ζ*x := by unfold b at ht; rw [div_le_iff₀ (by positivity)] at ht; linarith only [ht]
    unfold steam
    calc
      _ ≤ K*(2*(D*x^(-(3:ℝ)))+X.C*x^(-(3:ℝ))) := by have := X.pay; gcongr
      _ ≤ 2*(ζ*(x*x^(-(3:ℝ)))) := by linarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0≤x^(-(3:ℝ)))]
      _ ≤ _ := by
        have h : x*x^(-(3:ℝ))= x^(-(2:ℝ)) := by rw [show -(2:ℝ)=1 + -3 by norm_num,Real.rpow_add (by linarith : 0<x),Real.rpow_one]
        rw [h]; gcongr <;> first | exact hk.le | norm_num
  have hr : 0≤D*Real.exp (-a*radiusB x) := by positivity
  -- changing e.x doesn't change Key dim; `hi` depends on the type and needs hu
  have h1 := (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Key e.forest G)))
  rw [hu] at hi
  have hs := (sites_pos c).le
  change _ ≤ sites c*K at hv
  linarith only [mul_le_mul_of_nonneg_left H hs,mul_le_mul_of_nonneg_right hi hr,
    mul_le_mul_of_nonneg_right hv hr, mul_le_mul_of_nonneg_right (hi.trans hv) hf]
end Etcher
end YM.AnalyticBridge.ResetIncome
