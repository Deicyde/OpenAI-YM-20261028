import Mathlib.RingTheory.Nilpotent.Exp
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cues

/-!
# Costs for the curvature continuation on a single held physical step

Continue from `Hill`. Pay with the pre-L bills through Phi before setting L;
scale gates **here** after L, before S and its period. x still the coarse HAT,
t' the coarse temp, t the fine fiery. For the nonlinear U(μ+gZ) application,
g uses the GIVEN beta in x/2 .. 3*x, not either of the Hats.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Function Filter Lattice Wilson Pressure RG Next.SectorChange
open Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators Classical

/-- x-threshold varies after L. This wider envelope pays for links in the
specific patch gauge and for pricing first-order errors. NOT used as the
plaquette price to ensure Healthy. -/
def linkRoom (x : ℝ) := x^(-(3/8):ℝ)
lemma linkRoom_pos {x : ℝ} (h : 0 < x) : 0 < linkRoom x := Real.rpow_pos_of_pos h _
lemma linkRoom_tends : Tendsto linkRoom atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (by norm_num : 0<(3/8:ℝ))
lemma linkRoom_sq {x : ℝ} (hp : 0<x) : linkRoom x ^ 2 = x ^ (-(3/4):ℝ) := by
  unfold linkRoom; rw [sq,← Real.rpow_add hp]; norm_num



/-- actual fine/coarse price ratio; thresholds not generally restrictions
of a single temperature. -/
lemma across (G : Gauge) (L : Side) : ∀ᶠ x in atTop,
    let t := fiery G x L; let s := temp x
    0 < x ∧ 0 < s ∧ 0 < t ∧ s ≤ 2*t ∧ t ≤ 2*s ∧
    (Real.sqrt x)⁻¹ ≤ t := by
  have h : Tendsto (fun x => fiery G x L / temp x) atTop (𝓝 1) := Work.E09.temp_ratio _
  filter_upwards [eventually_gt_atTop 0,meter_grows.eventually_ge_atTop 2,
    h.eventually (le_mem_nhds (show 1/2<(1:ℝ) by norm_num)),
    h.eventually (ge_mem_nhds (show 1<(2:ℝ) by norm_num))] with x hx hw ht hl
  intro t s
  have hs := Work.E09.temp_pos hx
  have hh : s ≤ 2*t := by
    have he : 1/2*s ≤ t := (le_div_iff₀ hs).mp ht
    linarith only [he]
  have hS : 2*(Real.sqrt x)⁻¹ ≤ s := (mul_comm ..).trans_le (mul_le_mul_of_nonneg_left hw (by positivity))
  refine ⟨hx,hs,?_,hh,(div_le_iff₀ hs).mp hl,?_⟩
  · change 0<s at hs
    linarith only [hs,hh]
  linarith only [hS,hh]

/-- Scalar band, and polynomial and meter bills for this actual g. -/
theorem band (G : Gauge) (L : Side) : ∀ᶠ x in atTop,
    ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x →
    let t := fiery G x L; let g := coupling β
    0 < β ∧ 0 < g ∧ g ≤ 2*(Real.sqrt x)⁻¹ ∧ g⁻¹ ≤ 2*Real.sqrt x ∧
      meter x / 4 ≤ t/g ∧ t/g ≤ 4*meter x := by
  filter_upwards [across G L] with x hx
  obtain ⟨hp,hs,ht,hh,he,-⟩ := hx
  intro β hβ hB t g
  have hb : 0<β := by linarith
  have hg : 0<g := coupling_pos hb
  let u := Real.sqrt x; let w := (1/2:ℝ)*u
  have hu : 0<u := Real.sqrt_pos.mpr hp
  have hv : u^2=x := Real.sq_sqrt hp.le
  have hw : w^2≤β := by unfold w; nlinarith
  have hq : β≤(2*u)^2 := by nlinarith
  have hn : 0 ≤ w := by unfold w; positivity
  have hr : w ≤ g⁻¹ ∧ g⁻¹ ≤ 2*u := by
    have he : g⁻¹=Real.sqrt β := by unfold g coupling; rw [inv_inv]
    rw [he]
    exact ⟨by simpa [hn,Real.sqrt_sq] using Real.sqrt_le_sqrt hw,
      (Real.sqrt_le_sqrt hq).trans_eq (Real.sqrt_sq (by positivity))⟩
  have hf : g≤w⁻¹ := by
    rw [← inv_inv g]; exact inv_anti₀ (by unfold w; positivity) hr.1
  refine ⟨hb,hg,hf.trans_eq (by unfold w; change _=2*u⁻¹; field_simp),hr.2,?_,?_⟩
  · have hl : temp x/2 ≤ t := by unfold t; linarith
    rw [div_eq_mul_inv t]
    apply le_trans _ (mul_le_mul hl hr.1 hn ht.le)
    change meter x/4 ≤ (u⁻¹*meter x)/2*w
    unfold w
    exact le_of_eq (by field_simp; ring)
  rw [div_eq_mul_inv t]
  refine (mul_le_mul he hr.2 (by positivity) (by linarith)).trans_eq ?_
  change 2*(u⁻¹*meter x)*(2*u)=_
  field_simp
  ring

lemma band_small (G : Gauge) (L : Side) {C : ℝ} (he : 0<C) : ∀ᶠ x in atTop,
    ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x → coupling β ≤ C * fiery G x L := by
  filter_upwards [meter_grows.eventually_ge_atTop (4 / C),band G L] with x hx h
  intro β hb hk
  obtain ⟨-,hg,-,-,hi,-⟩ := h β hb hk
  have hc := (div_le_iff₀ he).mp hx
  have hh := (le_div_iff₀ hg).mp hi
  by_contra! hy
  nlinarith only [hg, hc,mul_le_mul_of_nonneg_right hc hg.le,mul_le_mul_of_nonneg_left hh he.le,hy]

/-- Still use `Remote.clearanceFare` (from hill) to pay for the gauge
and the *same* logarithm extension. -/
lemma extension_small (C : ℝ) (hp : 0 ≤ C) : ∀ᶠ x in atTop,
    C * Remote.clearanceFare x ≤ linkRoom x := by
  filter_upwards [eventually_gt_atTop 0, Lift.boundary_small C hp (1/16) (by norm_num),
    Work.E09.temp_cost (1/16) (by norm_num)] with x hx hQ h
  refine (Lift.boundary_fit x C hp).trans ((mul_le_mul hQ.2 h ((Work.E09.temp_pos hx).le) ?_).trans_eq ?_)
  · change 0 ≤ x^(_ : ℝ); positivity
  unfold linkRoom
  simp only [id_eq,← Real.rpow_add hx]; norm_num

lemma tiny_allow {f : ℝ → ℝ} (h : Tiny id f) {a b : ℝ} (he : a<b) : ∀ᶠ x : ℝ in atTop,
    f x * x^a ≤ x^b := by
  filter_upwards [eventually_gt_atTop 0,h (b-a) (by linarith)] with x hx hf
  exact (mul_le_mul_of_nonneg_right hf.2 (show 0 ≤ x^a by positivity)).trans_eq
    (by change x^(b-a)*x^a=_; rw [← Real.rpow_add hx, sub_add_cancel])
lemma const_allow {C a b : ℝ} (h : 0 ≤ C) (he : a<b) : ∀ᶠ x : ℝ in atTop,
    C * x^a ≤ x^b := tiny_allow (Tiny.const tendsto_id _ h) he

lemma threshold_small (G : Gauge) (L : Side) : ∀ᶠ x in atTop, fiery G x L ≤ linkRoom x := by
  filter_upwards [across G L, Work.E09.temp_cost (1/16) (by norm_num), const_allow (show 0 ≤ (2:ℝ) by norm_num)
    (show -(1/2:ℝ) + 1/16 < -(3/8:ℝ) by norm_num)] with x hx he hw
  obtain ⟨-, -, -, -, h, -⟩ := hx
  exact h.trans ((mul_le_mul_of_nonneg_left he (by norm_num)).trans hw)
lemma threshold_large (G : Gauge) (L : Side) (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ x in atTop,
    C * linkRoom x ^ 2 ≤ fiery G x L := by
  filter_upwards [across G L, const_allow hC (show (-(3/4):ℝ)<(-((1:ℝ)/2)) by norm_num)] with x hx h
  obtain ⟨hp, -, -, -, -, hh⟩ := hx
  apply le_trans _ hh
  rw [linkRoom_sq hp,Real.sqrt_eq_rpow,← Real.rpow_neg hp.le]; exact h

/-- Path lengths allowed by this continuation (not cutting the walk inside
our proofs). Costs post-L with l fixed before x. -/
def stride (l : ℕ) (x : ℝ) := (1+radiusB x)^l
lemma stride_ge (l : ℕ) (x : ℝ) : 1 ≤ stride l x := one_le_pow₀ (by omega)
lemma stride_tiny (l : ℕ) : Tiny id (fun x => (stride l x:ℝ)) := by
  simpa [stride] using (Tiny.cover_size.pow tendsto_id l)

/-- After division by g a stretched chart remainder still decays. -/
lemma band_price (G : Gauge) (L : Side) (C : ℝ) (hC : 0 ≤ C) (l : ℕ) :
    ∀ᶠ x in atTop, ∀ β : ℝ, x/2 ≤ β → β ≤ 3*x →
      (C * (stride l x:ℝ) * linkRoom x ^ 2) / coupling β ≤ x^(-(1/8):ℝ) := by
  have ht := (Tiny.const tendsto_id (2*C) (by positivity)).mul (stride_tiny l) tendsto_id
  filter_upwards [across G L,band G L,tiny_allow ht (show (-(1/4):ℝ)<(-(1/8):ℝ) by norm_num)] with x hx he hp
  intro β hb hh
  obtain ⟨hv,-⟩ := hx
  obtain ⟨-,hg,-,hK,-⟩ := he β hb hh
  rw [div_eq_mul_inv]
  refine (mul_le_mul_of_nonneg_left hK (show 0 ≤ C * (stride l x:ℝ)*linkRoom x ^ 2 by positivity)).trans (Eq.trans_le ?_ hp)
  rw [Real.sqrt_eq_rpow,linkRoom_sq hv, show (-(1/4):ℝ) = -(3/4)+ (1/2:ℝ) by norm_num,
    Real.rpow_add hv]; ring
end YM.PhysicalNext.PhysicalGuard7f546.Curved
