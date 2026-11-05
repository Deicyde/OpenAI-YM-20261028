import YM.Work.E09.Budget
import YM.Work.E09.Scales


/-!
# Drow assembly

E:5793–5810, in this orientation-local interface. `m` below is a rate AFTER
L and W but fixed before the x-tail. Use it even in the payment for flags.
The Lapse fees proportional to the *sum* of large fine tolls and to the noise
sum are dealt with differently: bend L and W respectively against pre-L and
pre-W costs. `Z`, which can depend on both L and W, will be paid on the x-tail
instead.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.E09
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open YM.Pressure YM.Pressure.Stores YM.Pressure.Tube YM.Pressure.Teller Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ComplexOrder Classical

private lemma bank (G : Gauge) (L : Side) (m Z B δ : ℝ) (K : ℕ)
    (hm : 0 < m) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      let t := fiery G x L; let u := largeT G x L; let s := temp x; let b : ℝ := radiusB x
      0 ≤ s ∧ s ≤ δ ∧ 0 ≤ t ∧ t ≤ u ∧ t ≤ 2*s ∧
      (4*m*K + Z*b^4)*t^2 ≤ m*t*u ∧ B*s^4*K*b^4 ≤ m/4*t^2 := by
  have hs : Tendsto temp atTop (𝓝 0) := by simpa using radiusB_temp 0
  have hr : Tendsto (fun x : ℝ => fiery G x L / temp x) atTop (𝓝 1) := temp_ratio _
  have hq : Tendsto (fun x : ℝ => fiery G x L / largeT G x L) atTop (𝓝 0) := by
    simpa using radiusB_fiery_largeT G L 0
  have hy := ((hq.const_mul (4*m*K)).add ((radiusB_fiery_largeT G L 4).const_mul Z))
  rw [mul_zero, mul_zero, add_zero] at hy
  have hz := (((radiusB_temp 4).mul hs).const_mul (4*B*K))
  rw [mul_zero, mul_zero] at hz
  filter_upwards [eventually_gt_atTop 0, (betaF_growth G L).eventually (eventually_gt_atTop 0),
    hs.eventually (ge_mem_nhds hδ), hr.eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num)),
    hr.eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)),
    hq.eventually (ge_mem_nhds zero_lt_one), hy.eventually (ge_mem_nhds hm),
    hz.eventually (ge_mem_nhds (show 0 < m/4 by positivity))] with x hx he hsd hrt hrs hqu hY hZ
  let t := fiery G x L
  let u := largeT G x L
  let s := temp x
  let b : ℝ := radiusB x
  have hs : 0 < s := temp_pos hx
  have ht : 0 < t := temp_pos he
  have hu : 0 < u := by
    unfold u; rw [largeT_eq _ _ _ he.le]; exact Real.rpow_pos_of_pos he _
  refine ⟨hs.le,hsd,ht.le,?_,(div_le_iff₀ hs).mp hrt,?_,?_⟩
  · exact (le_trans ((div_le_iff₀ hu).mp hqu) (one_mul u).le)
  · change (4*m*K + Z*b^4)*t^2 ≤ m*t*u
    change (4*m*K)*(t/u) + Z*(b^4*(t/u)) ≤ m at hY
    have h : (4*m*K + Z*b^4)*t ≤ m*u := by
      apply (div_le_iff₀ hu).mp; apply le_trans _ hY; exact le_of_eq (by ring)
    linarith only [mul_le_mul_of_nonneg_right h ht.le]
  change B*s^4*K*b^4 ≤ m/4*t^2
  change 4*B*K*((b^4*s)*s) ≤ m/4 at hZ
  have h : s ≤ 2*t := by linarith only [(le_div_iff₀ hs).mp hrs]
  have hP : 0 ≤ B*s^2*K*b^4 := by positivity
  linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le h 2) hP,
    mul_le_mul_of_nonneg_right hZ (sq_nonneg t)]

variable {G : Gauge} {c f : Side}

/-- Single cue, no need for bounds outside the provided estimates.
Second-range tides pay flags directly at rate m; for third-range tides the
C-loss is in Lapse, but there's a *separate* charge for flags against spend. -/
lemma assemble {S : StepData c f} (A : Stores S) (T : Tube G S)
    (U : Config G f) (Q V : Config G c) (x m t cF C W Z B δ d : ℝ) (K : ℕ)
    (hm : 0 ≤ m) (hf : m ≤ T.high.linear/8) (hd : m ≤ d)
    (hi : m ≤ S.kernel.penalty/32) (hc : m ≤ T.low.direct/64)
    (hF : cF ≤ T.high.linear/4) (hC : C ≤ S.kernel.penalty/16 * W)
    (hw : 1 ≤ W) (hlist : ∀ i ∈ A.aisles, W*t ≤ wire Q V i)
    (ht : 0 ≤ t) (hu : t ≤ largeT G x S.patch.L) (hB : 0 ≤ B)
    (hs : 0 ≤ temp x) (hst : t ≤ 2*temp x) (hx : temp x ≤ δ)
    (hspend : (4*m*K + Z*(radiusB x:ℝ)^4)*t^2 ≤ m*t*largeT G x S.patch.L)
    (herr : B*temp x^4*K*(radiusB x:ℝ)^4 ≤ m/4*t^2)
    (a : T.high.linear/2*t*(∑ i ∈ A.swell U t, toll U i) +
      d*t^2*((A.costs \ A.swell U t).card:ℝ) ≤ A.tally T x U V)
    (a' : S.kernel.penalty/8*(∑ i∈A.aisles, wire Q V i^2) ≤ A.talli T x Q V)
    (b : Bid.Payments δ A x U Q V K) (e : Bid.Crowds δ B T x V)
    (g : talll T x U Q V (A.hit U Q V x) + cF*t*(∑ i ∈ A.swell U t,toll U i) +
        C*t*(∑ i∈A.aisles, wire Q V i) + Z*t^2*(radiusB x:ℝ)^4*(A.spend U Q V x).shares ≥
          (T.low.linear*temp x)*(∑ i ∈ A.tides V x δ,toll V i))
    (g' : talll T x U Q V (A.outs x \ A.hit U Q V x) ≥ -(m/4*t^2*A.shares)) :
    m/2*t^2*A.shares ≤ A.assessed T x U Q V := by
  let D := A.spend U Q V x
  have h₁ := fine_budget A T U V x m d cF Q t ht hu hm hf hd hF a
  have h₂ := noise_budget A T U Q V x m C W t hw hlist ht hu hm hi hC a'
  have h₃ := coarse_budget A T V x m B δ t hs hx hB ht hst hc e
  have h₄ : (A.flags.card:ℝ) ≤ 4 *
      (((A.tides V x (temp x) \ A.tides V x δ).card:ℝ) + K*(D.shares:ℝ)) := by
    exact_mod_cast flags_budget A V Q U x δ hx K b
  have hn : 0 ≤ A.talln T x V := sum_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (by norm_num))
  have heq : talll T x U Q V (A.outs x \ A.hit U Q V x) + talll T x U Q V (A.hit U Q V x) =
      talll T x U Q V (A.outs x) :=
    sum_sdiff (show A.hit U Q V x ⊆ A.outs x from filter_subset ..)
  have hflags := mul_le_mul_of_nonneg_left h₄ (mul_nonneg hm (sq_nonneg t))
  have hy := mul_le_mul_of_nonneg_right hspend (show 0 ≤ ((D.shares):ℝ) by positivity)
  have hz : B*temp x^4*(A.outs x).card ≤ m/4*t^2*A.shares := by
    have h : ((A.outs x).card:ℝ) ≤ K*(radiusB x:ℝ)^4*A.shares := by exact_mod_cast b.ours
    linarith only [mul_le_mul_of_nonneg_left h (mul_nonneg hB (show 0 ≤ temp x^4 by positivity)),
      mul_le_mul_of_nonneg_right herr (show 0 ≤ (A.shares:ℝ) by positivity)]
  have hnot : ((A.spend U Q V x).shares:ℝ) = (D.costs.card:ℝ) + D.aisles.card := by
    simp [shares, D, spend]
  dsimp only [D] at *
  rw [hnot] at g hflags hy
  simp only [assessed, shares, Nat.cast_add] at g' hz ⊢
  linarith only [h₁,h₂,h₃, hflags, hn, heq, hz, hy, g, g']

theorem answer : Bid.E09 := by
  intro a G P J δ hδ H Q w
  obtain ⟨K, hK⟩ := a P δ hδ
  obtain ⟨B, hB, hCover⟩ := H
  obtain ⟨C, _, hC⟩ := Q
  obtain ⟨N, hN⟩ := J
  -- Pre-L work. No dependence on W or x.
  have hp : 0 < P.top.clip.linear := P.top.clip.tail_pos
  have he : Tendsto (fun n : ℕ => C/(n:ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by decide)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := eventually_atTop.mp
    (he.eventually (ge_mem_nhds (show 0 < P.top.clip.linear/4 by positivity)))
  refine ⟨max n N, fun L hL => ?_⟩
  have hr : 0 < P.bind.penalty := P.bind.penalty_pos
  have hh : Tendsto (fun W : ℝ => P.bind.penalty/16*W) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_id
  -- After L. Use eventually W, even when m needs to depend on W.
  filter_upwards [eventually_ge_atTop 1, hh.eventually_ge_atTop C,
    hN L ((le_max_right ..).trans hL)] with W hW hh hA
  have hw : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨Z, _, hZ⟩ := hC L W hw
  obtain ⟨d, hd, hs⟩ := hA
  let m := min (min (P.top.clip.linear/8) d) (min (P.bind.penalty/32) (P.below.clip.direct/64))
  have hm : 0 < m := by unfold m; have ha := P.below.clip.quadratic_pos; positivity
  refine ⟨m/2, by positivity, ⟨?_⟩⟩
  -- Now use ALL estimates on the same tail of x. No cost depending on the live period.
  filter_upwards [hs.late, (hCover L W).late, hZ.late, (hK L W hw).late,
    (w L W hw (m/4) (by positivity)).late, bank G L m Z B δ K hm hB.le hδ]
    with x ha ha' hz hb he hx
  obtain ⟨hst, hx, ht, hu, ht', hbank, herr⟩ := hx
  intro c f S hL' hSize T hT F A U k V hF hPlot
  obtain ⟨hS,hS'⟩ := ha c f S hL' hSize T hT F A U k V hF hPlot
  refine assemble A T U (S.prediction U k) V x m (fiery G x L) (C/(L.val:ℝ)^2) C W Z B δ d K
    hm.le ?_ ?_ ?_ ?_ ?_ ?_ hW ?_ ht ?_ hB.le hst ht' hx ?_ herr hS hS'
    (hb c f S hL' hSize T hT F A U k V hF hPlot).1
    (ha' c f S hL' hSize T hT F A U k V hF hPlot)
    (hz c f S hL' hSize T hT F A U k V hF hPlot)
    (he c f S hL' hSize T hT F A U k V hF hPlot)
  · rw [hT.high]; exact le_trans (min_le_left ..) (min_le_left ..)
  · exact le_trans (min_le_left ..) (min_le_right ..)
  · rw [hT.knobs]; exact le_trans (min_le_right ..) (min_le_left ..)
  · rw [hT.low]; exact le_trans (min_le_right ..) (min_le_right ..)
  · rw [hT.high]; exact hn L.val ((le_max_left ..).trans hL)
  · rw [hT.knobs]; exact hh
  · rw [← hL']; exact wire_listed A U V k x W hPlot
  · rw [hL']; exact hu
  rw [hL']; exact hbank

end YM.Work.E09
