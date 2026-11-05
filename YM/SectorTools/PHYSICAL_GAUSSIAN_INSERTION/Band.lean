import YM.Next.MAXWELL.Det
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Consumer

/-!
# In-band prices for these local insertions

Pay even the affine cost here. Explicitly a post-L threshold INCLUDING the
broad-radius price `W`, which should therefore be determined before using
this to delay entrance. Works with `R.beta` bounded above by twice the *fine*
hatted beta (upper edge); all periods once paying the sizes. This is still
on the fixed Gaussian step, not asserting this gives supplies for other
parts of the analytic schedule.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion.Physical

open MeasureTheory Function Filter Set Matrix
open Lattice RG Pressure Wilson Pressure.Tube Pressure.Stores Tree Precision
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Wisps Push.SectorMeasure
open scoped Topology ContDiff BigOperators Classical ENNReal Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- All fixed-L. ρ>0 arbitrary. -/
private lemma take_rate {ρ : ℝ} (hρ : 0 < ρ) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M*x ≤ rate ρ (radiusB x) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2/ρ),
    eventually_ge_atTop M, eventually_gt_atTop (1 : ℝ)] with x hx h hx'
  have ht : (Real.log x)^2 ≤ (radiusB x : ℝ) := Nat.le_ceil ..
  have hh : 2*Real.log x ≤ ρ * radiusB x := by
    have hz := (div_le_iff₀ hρ).1 hx
    have hL : 0 ≤ Real.log x := (Real.log_pos hx').le
    linarith only [mul_le_mul_of_nonneg_right hz hL, mul_le_mul_of_nonneg_left ht hρ.le]
  calc
    M*x ≤ x*x := mul_le_mul_of_nonneg_right h (by linarith)
    _ = Real.exp (2*Real.log x) := by
      rw [two_mul, Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_monotone hh

lemma load_limit (G : Gauge) (L : Side) {W M s B : ℝ} (hW : 0 ≤ W)
    (hM : 0 < M) (hs : 0 < s) (hB : 0 ≤ B) :
    ∀ᶠ x in atTop, ∀ (β d : ℝ), 0 < β → β ≤ 2*betaF G x L → 0 < d → d ≤ W*fiery G x L →
      0 ≤ load x (coupling β) d M B s ∧
      load x (coupling β) d M B s ≤ rate (-(s/240)) (radiusB x) := by
  let k : ℝ := M * M * (B*(1+W))
  have ht : Tendsto temp atTop (𝓝 0) := by simpa using Work.E09.radiusB_temp 0
  have hf : Tendsto (fun x => fiery G x L) atTop (𝓝 0) := ht.comp (Work.E09.betaF_growth G L)
  have hx : ∀ᶠ x : ℝ in atTop, 2 * betaF G x L ≤ x^2 := by
    filter_upwards [eventually_ge_atTop (G.slopeConstant*Real.log L.val),
      eventually_ge_atTop (4:ℝ)] with x h1 h2
    unfold betaF; nlinarith
  filter_upwards [ht.eventually (eventually_lt_nhds zero_lt_one),
    hf.eventually (eventually_lt_nhds zero_lt_one), take_rate (ρ:=s/240) (by positivity) k,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 120, hx,
    eventually_gt_atTop (0:ℝ)] with x h1 h2 h3 h4 h5 h6
  intro β d hβ he hd hh
  let b := radiusB x
  have hc : (coupling β)⁻¹ ≤ x := by
    rw [coupling, inv_inv]; exact (Real.sqrt_le_left h6.le).mpr (he.trans h5)
  have hi : d ≤ W := (hh.trans (mul_le_mul_of_nonneg_left h2.le hW)).trans_eq (mul_one W)
  have hm : 0 < temp x := Work.E09.temp_pos h6
  have hu : rate (-s) (b/60) ≤ rate (-(s/120)) b := by
    apply Real.exp_monotone
    change -s*((b/60 : ℕ) : ℝ) ≤ -(s/120)*b
    have h : (b : ℝ) ≤ 120*((b/60 : ℕ) : ℝ) := by
      exact_mod_cast show b ≤ 120*(b/60) by change 120 ≤ b at h4; omega
    linarith only [mul_le_mul_of_nonneg_left h hs.le]
  unfold load
  have ht : 0 < coupling β := coupling_pos hβ
  constructor
  · positivity
  calc
    _ ≤ x*((M*(M*rate (-(s/120)) b))*(B*(1+W))) := by
      gcongr
      · unfold rate; positivity
      exact hu
    _ = k*x*rate (-(s/120)) b := by unfold k; ring
    _ ≤ rate (s/240) b * rate (-(s/120)) b := mul_le_mul_of_nonneg_right h3 (rate_pos ..).le
    _ = _ := by unfold rate b; rw [← Real.exp_add]; ring_nf

/-- Receipt with actual coupling plans. -/
def BandPrice (G : Gauge) (R : Teller G) (P : Patch) (p W e C x : ℝ) :=
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
      100*(1+radiusB x) ≤ c.val → R.Funds S T → ∀ (V : Config G c) (k : S.Choices)
      (H : Stores S) (F : Forest S.ratio), H.flags = RG.flags (temp x) V →
      ∀ (q : Chi) (β d : ℝ), 0<β → β ≤ 2*betaF G x P.L → 0<d → d ≤ W*fiery G x P.L →
      ∀ (Y : LinkArray G (Frozen H x F)) (U : Finset (Rows.In x H F (G:=G))),
        book T x V k H F q d Y (coupling β) U p (Real.exp (C * rate (-e) (radiusB x) * U.card))

lemma from_patch {G : Gauge} (R : Teller G) (P : Patch) {p K M B s b r σ η g₀ : ℝ} {o : ℕ}
    (hp : 1 ≤ p) (hK : 0 < K) (hM : 0 < M) (hB : 0 ≤ B) (hs : 0<s) (hb : 0<b)
    (h : ∀ᶠ x in atTop, PatchPrice G R P p o K M B s b r σ η g₀ x) (W : ℝ) (hW : 0 ≤ W) :
    ∃ e C : ℝ, 0<e ∧ 0<C ∧ ∀ᶠ x in atTop, BandPrice G R P p W e C x := by
  let e := min (b/2) (s/240)
  let C := 2*p*(1 + 2*K*2)
  let φ x := rate (-b) (radiusB x) * K
  let ρ x := rate (-e) (radiusB x)
  have he : 0 < e := lt_min (half_pos hb) (by positivity)
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hy : Tendsto (fun x => K*(p*(ρ x+φ x/2))) atTop (𝓝 0) := by
    have ht : Tendsto φ atTop (𝓝 0) := by simpa using (error_limit b hb).mul_const K
    simpa using (((error_limit e he).add (ht.div_const 2)).const_mul p).const_mul K
  have hv : ∀ᶠ x in atTop, φ x ≤ ρ x := by
    filter_upwards [take_rate (half_pos hb) K, eventually_ge_atTop (1:ℝ)] with x h hx
    let n := radiusB x
    calc
      _ ≤ rate (-b) n * rate (b/2) n := mul_le_mul_of_nonneg_left
        ((le_mul_of_one_le_right hK.le hx).trans h) (rate_pos ..).le
      _ = rate (-(b/2)) n := by unfold rate; rw [← Real.exp_add]; ring_nf
      _ ≤ _ := Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..))
        (show (0:ℝ) ≤ radiusB x by positivity))
  refine ⟨e,C,he,by unfold C; positivity,?_⟩
  filter_upwards [load_limit G P.L hW hM hs hB, h, hy.eventually
    (eventually_lt_nhds (show 0<(1/4:ℝ) by norm_num)), hv] with x h1 h2 h3 h4
  intro c f S T hS hg hT V k H F hV q β d hβ hz hd hd' Y U
  let a := ρ x
  let N : ℝ := U.card
  have ha : 0 < a := rate_pos ..
  obtain ⟨hL,hu⟩ := h1 β d hβ hz hd hd'
  let L := load x (coupling β) d M B s
  have hh : L ≤ a := hu.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right
    (neg_le_neg (min_le_right ..)) (show (0:ℝ) ≤ radiusB x by positivity)))
  obtain ⟨_,_,hblock⟩ := h2
  have hi := hblock S T hS hg hT V k H F hV q (coupling β) d a (coupling_pos hβ) hd ha h3.le Y U
  have hw : intoCost p K (φ x) a L U.card ≤ Real.exp (C*rate (-e) (radiusB x)*U.card) := by
    have h5 : L^2 / (4*a) ≤ a := by
      have hx := pow_le_pow_left₀ hL hh 2
      apply (div_le_iff₀ (by positivity : (0:ℝ)<4*a)).2; nlinarith only [show L^2 ≤ a^2 from hx, sq_nonneg a]
    have h6 : a+φ x/2 ≤ 2*a := by change φ x ≤ a at h4; linarith only [h4,ha]
    unfold intoCost; apply Real.exp_monotone
    calc
      _ ≤ 2*p*(N*a + 2*K*(N*(2*a))) := by
        have hx : 0 ≤ N := Nat.cast_nonneg _
        gcongr
      _ ≤ _ := le_of_eq (by unfold C; change _ = _*a*N; ring)
  obtain ⟨hl,hA,hB,hU,hm,hE⟩ := hi
  exact ⟨hl,hA,hB,hU,hm,hE.trans hw⟩

theorem bands (p : ℝ) (hp : 1 ≤ p) (P : Patch) (R : Teller G) (h : P.Branches R.bind G)
    (W : ℝ) (hW : 0 < W) :
    ∃ s C : ℝ, 0<s ∧ 0<C ∧ ∀ᶠ x in atTop, BandPrice G R P p W s C x := by
  obtain ⟨K,M,B,s,b,r,σ,η,g₀,hK,hM,hB,hs,hb,_,_,_,_,he⟩ := blocks p hp 0 G P R h
  exact from_patch R P hp hK hM hB hs hb he W hW.le

end YM.SectorTools.PhysicalGaussianInsertion.Physical
