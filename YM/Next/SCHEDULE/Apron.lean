import YM.Next.SCHEDULE.Final
import YM.Next.SCHEDULE.Resize


/-!
# Some further scale prices incl Jhcost and higher-stage Jwr type footprints

Every stage above first can also require prices *using the preceding physical
scale* (e.g. log(\mathcal J) of order C P^D in E eq:Jhcost). After L rates fixed. Illustrate enforcing these
along with our other prices. Not an assertion that replicas with their
required calibrations etc. are thereby ready. Work for cutoffs on first
plateau unaffected; asymptotic prices here NOT asserted there. Finer-period
costs independent of R, wraps still charged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Precision Lattice Clock Instrument
open scoped Topology

variable {G : Gauge}

/-- Model POLYNOMIAL log-costs AFTER L. `x,y` both included.
Any resulting little-o claim needs charging the degrees/constants of that
actual estimate. NO accumulation `C_L^copies` in here. -/
def border (x y : ℝ) := (1+plain.P x+↑(plain.body x))+(1+plain.P y+↑(plain.body y))

private lemma postSize (g b c : ℝ) (hg : 0<g) (H) (d : ℕ) (ε : ℝ) (he : 0<ε) : ∀ᶠ s : ℝ in atTop,
    let x:=b+g*s; H*(border x (x+c))^d ≤ ε*s := by
  by_cases hH : 0 ≤ H
  · let x:=fun s:ℝ => b+g*s
    have hx : Tendsto x atTop atTop := tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop hg tendsto_id)
    have ht := (light 2 (d:ℝ) 2 two_pos).comp hx
    have hh : Tendsto (fun s : ℝ => x s/s) atTop (nhds g) := by
      have he := ((tendsto_const_nhds (x:=b)).div_atTop tendsto_id).add (tendsto_const_nhds (x:=g)); rw [zero_add] at he
      apply he.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs; change b/s+g=_; unfold x; field_simp
    have hpL : Tendsto (fun s : ℝ => H*6^d*((plain.P (x s))^d/s)) atTop (nhds 0) := by
      have hw := (ht.mul hh).const_mul (H*6^d); rw [zero_mul,mul_zero] at hw; apply hw.congr'
      filter_upwards [hx.eventually (eventually_gt_atTop (0:ℝ))] with s hs
      change H * 6^d * ( (plain.P (x s)^ ((d:ℕ):ℝ)* gap (x s)^ (2:ℝ))*(x s/s)) =_
      rw [Real.rpow_two,Real.rpow_natCast,gap,inv_pow, Real.sq_sqrt hs.le];
      by_cases h : s=0
      · simp [h]
      field_simp
    have h1 : ∀ᶠ x in atTop, 1+((plain.body x):ℝ)≤plain.P x := by
      filter_upwards [(ceiling_cheaper 2 1 1 one_lt_two zero_lt_one).eventually (ge_mem_nhds zero_lt_one)] with x hx
      simp only [Real.rpow_one,pow_one] at hx
      rw [Instrument.body]; simp only [plain,pow_one]
      simpa [P,plain] using (div_le_iff₀ (wp _ _)).1 hx
    have hz : ∀ᶠ x in atTop, 0 ≤ border x (x+c) ∧ border x (x+c) ≤ 6*plain.P x := by
      filter_upwards [advance h1,just_near c,plain.support 2 one_lt_two] with x hh hc hp
      have hx := hh x (Clock.same x)
      have hy := hh (x+c) hc
      unfold border
      have ht:= (hp x (x+c) (Clock.same x) hc).peek.2
      have hb:0<plain.P x:=wp _ _; have hw:0<plain.P (x+c):=wp _ _
      exact ⟨by positivity,by linarith⟩
    filter_upwards [hx.eventually hz,hpL.eventually (ge_mem_nhds he),eventually_gt_atTop (0:ℝ)] with s hz hr hs
    intro a; change 0 ≤ border a (a+c) ∧ _ ≤ 6*plain.P a at hz
    have hh:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.1 hz.2 d) hH
    refine hh.trans ?_; rw [mul_pow]; change H*6^d*(_/_)≤_ at hr; rw [← mul_div_assoc] at hr
    rw [← mul_assoc]; exact (div_le_iff₀ hs).1 hr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  intro y
  have hx : 0 ≤ border y (y+c) := by
    unfold border; have hh : 0<plain.P y:=wp _ _; have he:0<plain.P (y+c):=wp _ _; positivity
  calc
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hH) (pow_nonneg hx _)
    _ ≤ _ := by positivity

variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {F : ℕ → ℕ → Postage}

/-- Assess post-L bills at every higher stage, both β references and
including the incoming transition between smoothing indices. Use at actual
periods. -/
def Extent (d : ℕ → ℕ) (H : ℕ → ℝ) (W : Delays Θ) := ∀ i,
    ∀ b r : ℝ, W.scaleEntry i b ≤ r →
    let x := b+G.slopeConstant*r
    H i * (border x (x+G.slopeConstant * Real.log (D.L i).val))^(d i) ≤ ((i:ℝ)+1)⁻¹ * r

lemma Extent.fills (hG : G.Simple) (d : ℕ → ℕ) (H : ℕ → ℝ) (V : Delays Θ) :
    ∃ W : Delays Θ, Boost V W ∧ Extent d H W := by
  choose x hx using fun i b => eventually_atTop.1 (postSize G.slopeConstant b (G.slopeConstant * Real.log (D.L i).val)
    (Gauge.slopeConstant_pos hG) (H i) (d i) (((i:ℝ)+1)⁻¹) (by positivity))
  let W : Delays Θ := { V with scaleEntry := fun i r => max (V.scaleEntry i r) (x i r) }
  exact ⟨W,⟨le_rfl,fun i r => le_max_left ..,le_rfl,le_rfl⟩,fun i b r he => hx i b r (le_trans (le_max_right ..) he)⟩



/-- Pair of extra gates doable jointly. Also exposes that optional use of
Ringing doesn't restrict these MORE costly choices. Loaded from main issue
before using either. Continues BILLED Theta, with updated waits. -/
lemma combined (hG : G.Simple) {V : Delays Θ} {B : Beam K D} {k f} (h : Loaded B V e F k f)
    (d : ℕ → ℕ) (H : ℕ → ℝ) :
    ∃ W : Delays Θ, Boost V W ∧ Loaded B W e F k f ∧ Bumper e W ∧ Extent d H W ∧
      ∀ R : Radios K D, Transmitting R V → Transmitting R W := by
  obtain ⟨V',ha,ha'⟩:=Bumper.bump e V
  obtain ⟨W,hW,hW'⟩:=Extent.fills hG d H V'
  have hh := ha.chain hW
  exact ⟨W,hh, h.later hh, fun i b hx => ha' i b (le_trans (hW.beta i) hx), hW',
    fun _ ht i j hj => (ht i j hj).trans (hh.beta i)⟩
end YM.Next.Scheduling
