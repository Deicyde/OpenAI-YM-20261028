import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pockets
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Reheat
/-!
# Verified revenue receipt for the seed tally at Rank heater

For large L, post-L w for Plot (eventually high enough). Actual coarse x.
Outputs uniform for any Slice, Plot with retimed x; no forest freezing.
Keep Rank τ including M-tests on the fine F rows, but annotations use
a different fine threshold, relaying the core census via `selections`.
This is *before* things like affine-quadratic subtraction and
production of Body. See Opacity/Hulls and downstream revenue uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Wax
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Paint Filter Finset Precision Tree
open Pressure.Tube Pressure.Teller Pressure.Stores YM.Bid UVNext.PricedKernels Work
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} (P : Teller G)
    {w x t C u r s d : ℝ} (T : Tube G S) (A : Stores S) {U : Config G f} {Q V : Config G c} {k : S.Choices}
    (hP : Plot A U k V x w)
lemma reserve_lane (G : Gauge) (L : Side) (d : ℝ) (h : 0<d) : ∀ᶠ x in atTop, till x+1 ≤ radiusB x/50 ∧
    ∀ k : ℕ, fiery G x L/2*Real.exp (k/d) < 2 → k+1 ≤ radiusB x/50:=by
  let δ:=G.slopeConstant*Real.log L.val
  -- spend factor 1/2 also from `hat` rate, not via comparing triggers across arms
  filter_upwards [E04.eventually_room δ d h, Real.tendsto_log_atTop.eventually_ge_atTop (100*d+100),eventually_ge_atTop (max δ 64),(Work.E01.betaF_tendsto G L).eventually (eventually_gt_atTop 0)] with x hi hl hx hβ
  let a:= Real.sqrt (betaF G x L); have ha : 0<a:= Real.sqrt_pos.mpr hβ
  have hb:x≥64∧δ≤x:= ⟨(le_max_right ..).trans hx,(le_max_left ..).trans hx⟩
  have h1:x>0:= by linarith only [hb.1]
  have hq: 4*a≤x:= by
    have hh : a^2=x+δ:= Real.sq_sqrt hβ.le; nlinarith only [hb.1,hb.2,hh]
  refine ⟨hi.1,fun k hk=>?_⟩
  have he : a⁻¹ ≤ fiery G x L := le_mul_of_one_le_right (inv_nonneg.mpr ha.le) (Real.one_le_exp (sq_nonneg _))
  let b:=Real.exp (k/d)
  have hh : b < x:= by
    have hr : b/a< 4:= by
      rw [div_eq_inv_mul]; linarith only [mul_le_mul_of_nonneg_right he (Real.exp_pos (k/d:ℝ)).le,hk]
    exact lt_of_lt_of_le ((div_lt_iff₀ ha).mp hr) hq
  have ht: (k:ℝ) / d < Real.log x:= by apply Real.exp_lt_exp.mp; rw [Real.exp_log h1]; exact hh
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  have hB : (Real.log x)^2 ≤ radiusB x:=Nat.le_ceil _
  exact_mod_cast (show ((k:ℝ)+1)*50 ≤ (radiusB x:ℝ) by nlinarith only [hB,h,(div_lt_iff₀ h).mp ht,hl])

private lemma boost (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
    let d := 2*C/(n:ℝ)^2; let a := P.top; let v := d * ((1+scarf a.clip)*E04.capacity a)
    d ≤ Real.sqrt a.clip.direct / 16 ∧ d*Real.sqrt a.clip.direct ≤ a.clip.linear/4 ∧ v ≤ a.clip.linear/4:=by
  have ht : Tendsto (fun n:ℕ=> (2*C)/(n:ℝ)^2) atTop (𝓝 0):= tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
  have h1 := Real.sqrt_pos.mpr P.top.clip.quadratic_pos; have h2:=P.top.clip.tail_pos
  refine Eventually.and (ht.eventually (ge_mem_nhds ?_)) (Eventually.and ((ht.mul_const _).eventually (ge_mem_nhds ?_)) ((ht.mul_const _).eventually (ge_mem_nhds ?_)))
  all_goals linarith

private lemma lid (x : ℝ) (α : Finset (Cell f)) (U : Config G f) (hi : s ≤ 2*x) (_h : 0 ≤ s): ∑ i ∈ α,toll U i ≤ ∑ i∈α.filter (fun j=>s<toll U j), toll U i + ((α\α.filter (fun j=>s<toll U j)).card:ℝ) * (2*x):=by
  let f:=α.filter fun i=>s<toll U i
  change _ ≤ (∑ i∈ f,toll U i)+_
  calc
    _ = ∑ i∈ f,toll U i + ∑ i∈ α \ f,toll U i := (sum_sdiff (f:=toll U) (show f⊆α from filter_subset ..)).symm.trans (add_comm ..)
    _ ≤ _ := add_le_add_right (by
      refine Eq.trans_le rfl ((sum_le_sum (show ∀ i∈ α \ f, toll U i ≤ 2*x from fun i hi'=> (le_of_not_gt (fun h=> (mem_sdiff.mp hi').2 (mem_filter.mpr ⟨(mem_sdiff.mp hi').1,h⟩))).trans hi)).trans_eq ?_)
      rw [sum_const,nsmul_eq_mul]) _
private lemma selections (T : Tube G S) (t s b d C m x : ℝ) (h : 0≤t) (hi : 0≤s) (hs : t≤largeT G x S.patch.L) (h1 : t/2 ≤ s) (h2 : s ≤2*t)
    (hb : 0≤b) (hm : 0≤m) (hC :0≤C) (hp : 2*(3*m+C) ≤ b) (hQ : m+2*(m+C) ≤ d/4) (hD : 0 ≤ d)
    (he : b*s*(∑ j∈ A.swell U s,toll U j) + d*s^2*((A.costs\A.swell U s).card:ℝ) ≤ fineCharge T A x s U V) (Q : Config G c) :
    m*t^2*A.costs.card + m*t*largeT G x S.patch.L*(A.spend U Q V x).costs.card + C*t*(∑ i∈ A.swell U t,toll U i) ≤ fineCharge T A x s U V:= by
  apply le_trans _ he
  let N:=A.swell U s; let V' := A.swell U t; let L:= largeT G x S.patch.L
  let z : ℝ := (A.costs\N).card; let r:=∑ i∈ N,toll U i; let v:=∑ i∈V',toll U i
  let K:= (A.spend U Q V x).costs
  have hu: v ≤ r+z*(2*t) := (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _=>G.chord_nonneg _)).trans (lid t A.costs U h2 hi)
  have h3:L*(K.card:ℝ) ≤ v:=by
    have hh:∀ i∈ K,L≤toll U i:= fun i hi=> (mem_filter.mp (show i∈ A.swell U (largeT G x S.patch.L) from hi)).2.le
    have hs':K⊆ V':=fun i hi => mem_filter.mpr (by obtain ⟨ht,he⟩:=mem_filter.mp (show i∈ A.swell U (largeT G x S.patch.L) from hi); exact ⟨ht,lt_of_le_of_lt hs he⟩)
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hs' (fun _ _ _=>G.chord_nonneg _)); rw [mul_comm]; simpa only [nsmul_eq_mul] using! card_nsmul_le_sum _ _ _ hh
  have hr : (N.card:ℝ)*s ≤ r:= by
    have hC:= sum_le_sum (s:=N) (fun _ hi=> (mem_filter.mp (show _∈ A.swell U s from hi)).2.le)
    rwa [sum_const,nsmul_eq_mul] at hC
  have ht: (N.card:ℝ)*t ≤ 2*r := by linarith only [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N.card),hr]
  have ha : z+(N.card:ℝ)=A.costs.card:= by unfold z; exact_mod_cast card_sdiff_add_card_eq_card (show N⊆ A.costs from filter_subset ..)
  change m*t^2*_+m*t*L*↑K.card+C*t*v ≤ b*s*r+d*s^2*z
  rw [← ha]; have hv:= (sum_nonneg (s:=N) (fun i _=>G.chord_nonneg (faceValue U i)))
  have hh₁:(2*m+(m+C))*t*r≤ b*s*r:= by
    apply mul_le_mul_of_nonneg_right _ hv; nlinarith only [mul_le_mul_of_nonneg_right hp h,mul_le_mul_of_nonneg_left h1 hb]
  have hh₂: (m+2*(m+C))*t^2*z ≤ d*s^2*z:= by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _); linarith only [mul_le_mul_of_nonneg_right hQ (sq_nonneg t),mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 2) hD]
  linarith only [hh₁,hh₂,mul_le_mul_of_nonneg_left ht (mul_nonneg hm h),mul_le_mul_of_nonneg_left (h3.trans hu) (mul_nonneg hm h),mul_le_mul_of_nonneg_left hu (mul_nonneg hC h)]
-- reconcile a t0 income *here*: replace the original F, dropping its revenue.
-- (Can't use continuity in t.) E09 assembled other estimates from same Teller.
-- hulls use till x, cost arithmetic even with E04.B parameters.
def stakeBook (T : Tube G S) (A : Stores S) (x t:ℝ) (U : Config G f) (Q V : Config G c) :=
    A.assessed T x U Q V-A.tally T x U V + fineCharge T A x t U V

section numeric
local notation "ν" => fiery G x S.patch.L
-- memberships census lemma used in the comparison assembly
include hP
private lemma icehouse (t : ℝ) (ht : ν/2≤t) (hs : t≤2*ν)
    (Q : Config G c) (hy : Q=S.prediction U k) (d m C b δ Z : ℝ) (K : ℕ)
    (hν : 0 < ν) (h : 1 ≤ w) (hv : 0 < m)
    (hF : T.high.linear/2*t*(∑ i∈ A.swell U t,toll U i) + T.high.direct/512*t^2*((A.costs \ A.swell U t).card:ℝ) ≤ fineCharge T A x t U V)
    (hV : S.kernel.penalty/8*(∑ i∈A.aisles, wire Q V i^2) ≤ A.talli T x Q V)
    (hN : m ≤ S.kernel.penalty/32) (hi : C ≤ S.kernel.penalty/16*w) (hM : ν ≤ largeT G x S.patch.L)
    (hA : 0≤d) (hB : 2*(3*m+d)≤ T.high.linear/2) (hY : m+2*(m+d) ≤ (T.high.direct/512)/4)
    (hE : temp x≤δ) (hδ : m ≤ T.low.direct/64) (hb : 0≤ b) (hc : ν ≤ 2*temp x) (hC : Crowds δ b T x V)
    (hS : talll T x U Q V (A.hit U Q V x) + d*ν*(∑ i∈ A.swell U ν,toll U i) + C*ν*(∑ i∈A.aisles, wire Q V i) + Z*ν^2*(radiusB x:ℝ)^4*(A.spend U Q V x).shares ≥ T.low.linear*temp x*(∑ i ∈ A.tides V x δ,toll V i))
    (hz : talll T x U Q V (A.outs x \ A.hit U Q V x) ≥ -(m/4*(fiery G x S.patch.L)^2*A.shares))
    (hD : Bid.Payments δ A x U Q V K)
    (hW : (4*m*K+ Z*(radiusB x:ℝ)^4)*ν^2 ≤ m*ν*largeT G x S.patch.L)
    (hf : b*(temp x)^4*K*(radiusB x:ℝ)^4 ≤ m/4*ν^2) :
    m/2*ν^2*A.shares ≤ stakeBook T A x t U Q V:= by
  let y:=ν^2
  obtain ⟨χ₁,χ₂⟩:= And.intro T.high.tail_pos.le T.high.quadratic_pos.le
  have h1:=selections A T ν t _ _ d m x hν.le ((by positivity : 0≤ν/2).trans ht) hM ht hs (div_nonneg χ₁ (by norm_num)) hv.le hA hB hY (div_nonneg χ₂ (by norm_num)) hF Q
  have h2:= E09.noise_budget A T U Q V x m C w ν h (hy.symm ▸ E09.wire_listed _ _ _ _ _ _ hP) hν.le hM hv.le hN hi hV
  have h3:= E09.coarse_budget A T V x m b δ ν (E04.temp_nonneg x) hE hb hν.le hc hδ hC
  have h4:(A.flags.card:ℝ) ≤4 *(((A.tides V x (temp x) \ A.tides V x δ).card:ℝ) + K*((A.spend U Q V x).shares:ℝ)):=by exact_mod_cast E09.flags_budget A V Q U x δ hE K hD
  have hflags := mul_le_mul_of_nonneg_left h4 (mul_nonneg hv.le (sq_nonneg ν))
  have hn : 0 ≤ A.talln T x V:= sum_nonneg (fun i _=> div_nonneg (sq_nonneg _) (by norm_num))
  have heq := (sum_sdiff (show A.hit U Q V x⊆ A.outs x from filter_subset ..) (f:=fun i=>T.workL (till x) U Q V (temp x) i+T.workD (till x) V (temp x) i))
  have hsp := mul_le_mul_of_nonneg_right hW (show 0≤ ((A.spend U Q V x).shares:ℝ) by positivity)
  have hr : b*temp x ^ 4 * (A.outs x).card ≤ m/4*ν^2*A.shares:=by
    have hc : ((A.outs x).card:ℝ) ≤ K*(radiusB x:ℝ)^4*A.shares:=by exact_mod_cast hD.ours
    linarith only [mul_le_mul_of_nonneg_left hc (show 0 ≤ b*(temp x)^4 by positivity), mul_le_mul_of_nonneg_right hf (show 0≤(A.shares:ℝ) by positivity)]
  have he : ((A.spend U Q V x).shares:ℝ) = (A.spend U Q V x).costs.card+(A.spend U Q V x).aisles.card:= by simp [shares,spend]
  rw [he] at hsp hflags hS
  change talll T x U Q V (A.outs x\A.hit U Q V x)+talll T x U Q V (A.hit U Q V x)= talll T x U Q V (A.outs x) at heq
  simp only [stakeBook, assessed, shares,Nat.cast_add] at hz hr ⊢
  linarith only [hz,hr,h1,h2,h3,hflags,hsp,hS,heq,hn]
end numeric

private lemma ice (G : Gauge) (L : Side) (m Z b δ : ℝ) (hm : 0 < m) (hb : 0 < b) (hd : 0<δ) (K : ℕ):
    ∀ᶠ x in atTop, let t:=fiery G x L; let u:=largeT G x L; let s:=temp x; let a:ℝ:=radiusB x
    0 ≤ x ∧ 0<t ∧ t≤u ∧ t≤2*s ∧ s≤2*t ∧ s≤δ ∧
    (4*m*K+Z*a^4)*t^2 ≤ m*t*u ∧ b*s^4*K*a^4 ≤ m/4*t^2:=by
  let k:=G.slopeConstant * Real.log L.val
  have h:=E09.temp_ratio k; have hr:=E09.radiusB_temp 4; have he:=E09.radiusB_temp 0
  simp only [pow_zero,one_mul] at he
  have hu:=E09.radiusB_fiery_largeT G L 0; simp only [pow_zero,one_mul] at hu; have hv:=E09.radiusB_fiery_largeT G L 4
  have ht:=(hu.const_mul (4*m*K)).add (hv.const_mul Z); rw [mul_zero,mul_zero,add_zero] at ht
  have hp:=(hr.mul he).const_mul (4*b*K); rw [mul_zero,mul_zero] at hp
  filter_upwards [eventually_gt_atTop 0,(E09.betaF_growth G L).eventually (eventually_gt_atTop 0), he.eventually (ge_mem_nhds hd), h.eventually (le_mem_nhds (show (1/2:ℝ)<1 by linarith)),h.eventually (ge_mem_nhds (show (1:ℝ)<2 by linarith)), ht.eventually (ge_mem_nhds hm),hu.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)), hp.eventually (ge_mem_nhds (show 0<m/4 by linarith))] with x hx hf hh hL hM ht hQ hz
  intro t u s a; have h':0<t :=E09.temp_pos hf; have hv : 0 < s:= E09.temp_pos hx
  have hr : 0<u:=by unfold u; rw [E09.largeT_eq G L x hf.le]; positivity
  have hs : s ≤ 2*t:=by change _≤t/s at hL; rw [le_div_iff₀ hv] at hL; linarith only [hL]
  refine ⟨hx.le,h',by simpa using (div_le_iff₀ hr).mp (show t/u ≤ 1 from hQ), (div_le_iff₀ hv).mp hM,hs,hh,?_,?_⟩
  · change (4*m*K)*(t/u)+Z*(a^4*(t/u))≤ m at ht
    rw [← show (4*m*K+Z*a^4)*t/u=_ from (show (4*m*K+Z*a^4)*t/u=(4*m*K)*(t/u)+Z*(a^4*(t/u)) by ring)] at ht
    rw [div_le_iff₀ hr] at ht; linarith only [mul_le_mul_of_nonneg_right ht h'.le]
  change (4*b*K)*(a^4*s*s) ≤ _ at hz
  have hs : s^4 ≤ s^2 * (4*t^2) := calc
    _ = s^2*s^2:=by ring
    _ ≤ _:= mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hv.le hs 2).trans_eq (by ring)) (sq_nonneg _)
  linarith only [mul_le_mul_of_nonneg_right hz (sq_nonneg t),mul_le_mul_of_nonneg_right hs (show 0≤ b*K*a^4 by positivity)]

/-- Use for all forests and Stores, still with hypotheses of `live`
(including size, Plot and actual slice). -/
def RankMeter (t w γ : ℝ) (L : Side) := live P L w (fun S T _ A z U k V=> γ*(fiery G z S.patch.L)^2*A.shares≤ stakeBook T A z (phase (betaF G t S.patch.L)) U (S.prediction U k) V) (retime t)
lemma chamber : ∃ n : ℕ,∀ L : Side,n ≤ L.val→∀ᶠ W in atTop, ∃ m : ℝ, 0<m ∧ ∀ᶠ x in atTop, RankMeter P x W m L:= by
  obtain ⟨δ,hδ,B,hB,h⟩:=E05.answer P
  obtain ⟨C,hC,H⟩:= E04.answer E03.answer P
  obtain ⟨D,hD,hZ⟩:= E07.answer E01.answer E03.answer E04.answer P δ hδ
  obtain ⟨n',hn'⟩:= E06.answer E03.answer E04.answer P
  let ℓ:= P.top.clip.linear; let d:=P.top.clip.direct/512
  have hd:0<d:=div_pos P.top.clip.quadratic_pos (by norm_num); have hl:0<ℓ:=P.top.clip.tail_pos
  let m:=min (min (P.bind.penalty/32) (P.below.clip.direct/64)) (min (ℓ/32) (d/32))
  have hm:0<m:=lt_min (lt_min (by exact div_pos P.bind.penalty_pos (by norm_num)) (by exact div_pos P.below.clip.quadratic_pos (by norm_num))) (by unfold d; exact lt_min (by positivity) (div_pos hd (by norm_num)))
  obtain ⟨K,hx⟩:= E01.answer P δ hδ
  have hT:Tendsto (fun n:ℕ=> D/(n:ℝ)^2) atTop (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨n,hn⟩ := eventually_atTop.mp ((boost P C).and (hT.eventually (ge_mem_nhds hm)))
  refine ⟨max n n',fun L hL=>?_⟩
  let a : ℝ:= P.bind.penalty/16; have ha:0<a:= div_pos P.bind.penalty_pos (by norm_num)
  filter_upwards [hn' L ((le_max_right ..).trans hL),eventually_ge_atTop (1:ℝ),eventually_ge_atTop (D/a)] with W hU hW he
  have hr:= LT.lt.trans_le zero_lt_one hW
  obtain ⟨z,hz,hζ⟩:=hZ L W hr; obtain ⟨e,he',hE⟩:=hU
  have ht := Next.Fluctuations.bare E03.answer E04.answer P L W hr (E08.answer E01.answer E02.answer P L W hr) (m/4) (by positivity)
  refine ⟨m/2,by positivity,?_⟩
  let A:=P.top
  filter_upwards [tall_limit.eventually (hE.late.and ((hx L W hr).late.and hζ.late)),tall_limit.eventually ((h L W).late.and ((H L W).late.and ht.late)),tall_limit.eventually (ice G L m z B δ hm hB hδ K), crossfade G L,tall_limit.eventually (reserve_lane G L A.clip.relaxation A.clip.radius_pos)] with x h1 h2 h3 h4 h5
  intro c f S hL' hSize T H F Θ U k V hF hP
  obtain ⟨_,hv⟩:=h1.1 _ _ _ hL' hSize _ H _ _ _ _ _ hF hP; subst L
  let u:= retime x; let t:=phase (betaF G x S.patch.L); let v:=fiery G u S.patch.L
  have hx := min_le_left (a:=ℓ/32) (b:=d/32); have hA:m ≤ ℓ/32:= (min_le_right ..).trans hx
  have hd' : m ≤ d/32:= (min_le_right ..).trans (min_le_right ..)
  obtain ⟨hf,hv',hU,hQ,hX,hC',hl,hz'⟩:= h3; obtain ⟨hu,hμ,he₀,hz₀⟩:= h4
  have hBy := h1.2.2 _ _ _ rfl hSize _ H _ _ _ _ _ hF hP
  have hY := h2.2.1 _ _ _ rfl hSize _ H _ _ _ _ _ hF hP
  obtain ⟨hs,hG⟩:=hn (S.patch.L.val) ((le_max_left ..).trans hL)
  let K₀:=(S.patch.L.val:ℝ); let r:=2*C/K₀^2
  obtain ⟨h₁,h₂,h₃⟩:=hs
  have ht' : LaneCounts T.up u t T.high (Work.E04.capacity P.top) 1 S.ratio.parent:= by
    obtain ⟨A,B,hf,hV⟩:=H.feeds; rw [H.high]; refine Work.E04.lanes hf le_rfl hu.le one_pos (Work.E04.parent_separation _) ⟨h5.1,fun k hk => h5.2 k ?_⟩; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right he₀ (Real.exp_pos _).le) hk
  have hT:0 ≤ K₀:=by unfold K₀; positivity
  have hp:0 ≤ r:=by unfold r; positivity
  refine icehouse T Θ hP t he₀ hz₀ _ rfl (D/K₀^2) m D B δ z K hv' hW hm (flickers T Θ hP ht' he₀ hz₀ hu.le (d:=r) (fun i=> ?_) hp (Work.E04.capacity_pos _).le (H.high.symm ▸ h₁) (H.high.symm ▸ h₂) (H.high.symm ▸ h₃)) hv ?_ ?_ hU (by positivity) ?_ ?_ hC' ?_ hB.le hQ ?_ hBy ?_ (h1.2.1 _ _ _ rfl hSize _ H _ _ _ _ _ hF hP).1 hl hz'
  · apply (hY.2.2.phi _).trans
    have hx : v ≤ 2*t:= by linarith only [he₀]
    refine (mul_le_mul_of_nonneg_left hx (div_nonneg hC.le (sq_nonneg _))).trans_eq ?_; unfold r K₀; ring
  · rw [H.knobs]; exact (min_le_left ..).trans (min_le_left ..)
  · rw [H.knobs]; change D ≤ a* _; linarith only [(div_le_iff₀ ha).mp he]
  · rw [H.high]; change _≤ ℓ/2; change D/K₀^2≤m at hG; linarith only [hA,hG,hm]
  · rw [H.high]; change _≤ d/4; change D/K₀^2≤m at hG; linarith only [hd',hG,hm]
  · rw [H.low]; exact (min_le_left ..).trans (min_le_right ..)
  · exact h2.1 _ _ _ rfl hSize _ H _ _ _ _ _ hF hP
  exact h2.2.2 _ _ _ rfl hSize _ H _ _ _ _ _ hF hP
end YM.PhysicalNext.InteractingRank.Wax
