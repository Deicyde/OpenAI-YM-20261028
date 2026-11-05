import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Salary

/-!
# Delay gates on a weak-comparison stage

Distinct lowering of the threshold (comparison τ), larger cover
`chorus.body` = B².

Never assert `p^θ ≤ check_p`; buy BEFORE all Φ using
*one-time* power estimates instead.

Reserve/Coefficients here in actual
`Clock` functions, cover ceilings.

Include simultaneous bounds for all
levels in the funded interval, not just adjacent scales (h varies with
β̂ by the work mode).

Aims E eq:kdom and Eq:ksize with tolerances.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Weak
open Filter Function RG RG.Supply Bid Precision Lattice Real Clock Instrument
open scoped Topology

local notation "p₀" => plain.P
local notation "p₁" => chorus.P
local notation "M₁" => chorus.body

/-- Numerical bills through the stretch (pick accuracy and powers
appropriately for each stage). x = center level k, y,z actual hats anywhere
between k and endpoint. Include the corresponding orders for geometry A and
B *together*. .income is a ONE-TIME p^ε expenditure. -/
structure Chorus (F : Focus) (L θ x : ℝ) : Prop where
  shape (a b : ℝ) : near x a → near x b → Alike chorus a b 2 ∧ Alike plain a b 2
  start :
    let D : ℝ := F.funds.D
    F.funds.H + Real.log L +
        D*Real.log (1+(M₁ x:ℝ)) + D*Real.log (p₁ x) ≤ F.accuracy*Real.log (p₀ x)
  income : ∀ a, near x a →
    F.funds.bundle chorus θ a a ≤ p₀ x ^ F.accuracy
  toll (a b : ℝ) : near x a → near x b →
    let M := 1+(M₁ a:ℝ); let g := Clock.gap a; let p:=p₁ a; let k:=F.funds.D
    let H:=F.funds.H; let c:=F.funds.rate; let d:=F.accuracy
    1 ≤ p ∧ 1 < a ∧ 9 ≤ M₁ a ∧
    (H*g^F.funds.power)*(M^k*p₀ x^k) ≤ d ∧
    H*g⁻¹^k*Real.exp (-c*(M₁ a:ℝ)) ≤ d ∧
    H*M^k/p ≤ d ∧ H*M^k*Real.log g⁻¹/p^ (2:ℕ) ≤ d ∧
    H*g⁻¹^k*Real.exp (-c*p^ (2:ℕ)/M^k+(k:ℝ)*p₁ b^((1:ℝ)/5)) ≤ d

namespace Focus
variable (F : Focus)

/-- θ gate, post-L finite powers. Can strengthen to include any stages
neighboring this. -/
def thin := F.accuracy / (8*((F.funds.D:ℝ)+1))
lemma tp : 0 < F.thin := by unfold thin; have h:=F.toll; positivity

/-- `M₁ = plain cover²`. -/
private lemma bump {x : ℝ} :
    1+(M₁ x:ℝ) ≤ (1+(Clock.cover x:ℝ))^ (2:ℕ) := by
  unfold Instrument.body chorus; push_cast; have hp : 0 ≤ (Clock.cover x:ℝ) := by positivity
  nlinarith only [hp]

-- domination of scale-only charges
lemma minor (ε : ℝ) (he : 0<ε) : Tendsto (fun a => p₁ a/(p₀ a^ε)) atTop (𝓝 0) := by
  let f (t : ℝ) := t^((3:ℝ)/2)
  have h : (fun t : ℝ => t^((3:ℝ)/2)) =o[atTop] (fun t => t^ (2:ℕ)) := by
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    let q := (2:ℝ)-3/2
    have ht : Tendsto (fun y : ℝ => c * y^q) atTop atTop := Tendsto.const_mul_atTop hc (tendsto_rpow_atTop (by norm_num [q]))
    filter_upwards [ht.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with y hy hw
    have hv := Real.rpow_pos_of_pos hw ((3:ℝ)/2)
    have hz := mul_le_mul_of_nonneg_right hy hv.le
    have hk : c * y ^ q * y ^ ((3:ℝ)/2) = c * y ^ (2:ℕ) := by
      rw [mul_assoc, ← Real.rpow_add hw,show q+3/2=(2:ℝ) by norm_num [q], Real.rpow_two]
    change ‖y^((3:ℝ)/2)‖≤ c*‖y^ (2:ℕ)‖; rw [norm_of_nonneg hv.le,norm_of_nonneg (by positivity)]
    linarith
  have hp := Clock.negative (c:=ε) (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)) h he
  refine ((tendsto_exp_atBot.comp hp).comp clock).congr ?_
  intro x; dsimp only [comp_apply,P,plain,chorus,watch]; rw [rpow_two,exp_sub,← exp_mul,mul_comm ε]

private lemma cheap (k : ℕ) : Tendsto (fun a => (1+(M₁ a:ℝ))^k/(p₁ a)) atTop (𝓝 0) := by
  have hx := ceiling_cheaper chorus.center 1 (2*k) chorus.above zero_lt_one
  simp only [rpow_one] at hx
  apply squeeze_zero' _ _ hx
  · filter_upwards with x; have hp : 0<p₁ x := wp _ _; positivity
  filter_upwards with x
  have hp :0<watch chorus.center x := wp _ _
  apply div_le_div_of_nonneg_right _ hp.le; rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) bump k

private lemma switchUp : ∀ᶠ x : ℝ in atTop, p₁ x ≥ 1 ∧ 1+(M₁ x:ℝ) ≤ p₁ x ∧ 9 ≤ M₁ x ∧ 1 < x := by
  filter_upwards [chorus.pitched,(cheap 1).eventually (ge_mem_nhds zero_lt_one)] with x hx hz
  have he : (1+(M₁ x:ℝ)) / p₁ x ≤ 1 := by simpa using hz
  exact ⟨hx.2.2.1,by have hh0 : 0<p₁ x:=wp _ _; simpa using (div_le_iff₀ hh0).1 he,hx.2.1,hx.1⟩

private lemma ln_charge (L : ℝ) :
    ∀ᶠ x : ℝ in atTop,F.funds.H + Real.log L + (F.funds.D:ℝ)*Real.log (1+(M₁ x:ℝ)) +
      (F.funds.D:ℝ)*Real.log (p₁ x) ≤ F.accuracy*Real.log (p₀ x) := by
  have hh:=F.tp
  have hl := (minor F.thin hh).eventually (ge_mem_nhds zero_lt_one)
  have ht := F.toll
  have hp := tendsto_log_atTop.comp (growing (d:=2) (by norm_num))
  filter_upwards [hl,switchUp, hp.eventually_ge_atTop (max ((F.funds.H+Real.log L)/(F.accuracy/2)) 0)] with x hx hy hz
  have hu : 0<p₀ x := wp _ _
  have hv : 0<p₁ x := wp _ _
  have h1 : Real.log (p₁ x) ≤ F.thin*Real.log (p₀ x) := by
    rw [← Real.log_rpow hu]; apply Real.log_le_log hv
    simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hu F.thin)).1 hx
  have h2 := Real.log_le_log (show 0 < 1+(M₁ x:ℝ) by positivity) hy.2.1
  change _ ≤ Real.log (p₀ x) at hz
  have hu := (div_le_iff₀ (half_pos ht)).1 ((le_max_left ..).trans hz)
  have h0 : 0 ≤ Real.log (p₀ x):= (le_max_right ..).trans hz
  have hA : (F.funds.D:ℝ)*F.thin ≤ F.accuracy/8 := by
    unfold thin; field_simp; nlinarith
  have hk := mul_le_mul_of_nonneg_right hA h0
  have he := mul_le_mul_of_nonneg_left h1 (show 0≤(F.funds.D:ℝ) by positivity)
  have hx := mul_le_mul_of_nonneg_left h2 (show 0≤(F.funds.D:ℝ) by positivity)
  nlinarith only [ht,h0,hu,hk,he,hx]

private lemma surplus {θ : ℝ} (ht : θ ≤ F.thin) :
    Tendsto (fun x => F.funds.bundle chorus θ x x / p₀ x ^ F.accuracy) atTop (𝓝 0) := by
  have hp := F.tp; have hg := F.toll
  let y : ℝ := F.funds.D
  have ha : F.accuracy-y*F.thin>0 := by
    unfold thin
    field_simp; unfold y; nlinarith
  have hl := ((tendsto_const_nhds (x := F.funds.H*(4:ℝ)^F.funds.D)).div_atTop
    ((tendsto_rpow_atTop ha).comp (growing (d:=plain.center) (by norm_num [plain]))))
  apply squeeze_zero' _ _ hl
  · filter_upwards with x
    have he:= lt_of_lt_of_le zero_lt_one F.funds.h_ge
    have hu : 0<p₀ x := wp _ _; have hv : 0<p₁ x := wp _ _
    have hg : 0 < LevelCost θ x := Real.rpow_pos_of_pos hu _
    unfold Postage.bundle; positivity
  filter_upwards [(minor F.thin hp).eventually (ge_mem_nhds zero_lt_one),switchUp,(growing (d:=2) (by norm_num)).eventually_ge_atTop 1] with x h hy hP
  let A := p₀ x; let q:=A^F.thin
  have he : 1 ≤ A := hP; have hd : 0 < A := lt_of_lt_of_le zero_lt_one he
  have hu :0<q := Real.rpow_pos_of_pos hd _
  have hp' : p₁ x ≤ q := by simpa using (div_le_iff₀ hu).1 h
  have hy' : LevelCost θ x ≤ q := Real.rpow_le_rpow_of_exponent_le he ht
  have hA := hy.2.1
  have hF:= lt_of_lt_of_le zero_lt_one F.funds.h_ge
  calc
    _ ≤ F.funds.H*(4*q)^F.funds.D/A^F.accuracy := by
      have hc:0<LevelCost θ x:=Real.rpow_pos_of_pos hd _
      have hM:0<p₁ x:=wp _ _
      unfold Postage.bundle; change _/A^_ ≤ _; gcongr; linarith
    _ = _ := by
      change _=F.funds.H*(4:ℝ)^F.funds.D/A^(F.accuracy-y*F.thin)
      unfold q; rw [mul_pow, ← Real.rpow_mul_natCast hd.le, Real.rpow_sub hd,mul_comm y F.thin]
      unfold y; field_simp

private lemma kcover (A : Postage) (ε : ℝ) (he : 0<ε) : ∀ᶠ x : ℝ in atTop,
    let k:=A.D; let H:=A.H; let p:=p₁ x; let B:=1+(M₁ x:ℝ)
    H*B^k/p ≤ ε ∧ H*B^k*Real.log (gap x)⁻¹/p^ (2:ℕ) ≤ ε := by
  have hx : Tendsto (fun x => A.H*((1+(M₁ x:ℝ))^A.D/p₁ x)) atTop (𝓝 0) := by simpa using (cheap A.D).const_mul A.H
  filter_upwards [switchUp,hx.eventually (ge_mem_nhds he)] with x hx H
  obtain ⟨hx,hB,hp,hg⟩:=hx
  have ha :0<A.H:=lt_of_lt_of_le zero_lt_one A.h_ge
  let B := 1+(M₁ x:ℝ)
  have hh0 : 0<p₁ x := wp _ _
  have ht : Real.log (gap x)⁻¹ ≤ p₁ x := by
    rw [Real.log_inv,log_gap (by linarith)]
    have h := Real.log_pos hg
    have he := Nat.le_ceil (Real.log x^ (2:ℕ))
    let m : ℝ := Clock.cover x
    have hh : (Real.log x)^ (2:ℕ) ≤ m := he
    have hD : 1+m^ (2:ℕ) ≤ p₁ x := by simpa only [Instrument.body,chorus,m,Nat.cast_pow] using hB
    nlinarith only [hh,hD,sq_nonneg (m-1),sq_nonneg (Real.log x-1)]
  intro k F p B'
  have hF : F*B'^k/p ≤ ε := by change A.H*(_/ _ ) ≤ ε at H; simpa only [mul_div_assoc] using H
  refine ⟨hF,le_trans ?_ hF⟩
  have hQ:0 ≤ B' := by unfold B'; positivity
  calc
    _ ≤ F*B'^k*p/p^ (2:ℕ) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (mul_nonneg ha.le (pow_nonneg hQ k))) (by positivity)
    _ = _ := by field_simp

private lemma negk (k : ℕ) {P : ℝ → ℝ} (h : Tendsto (fun x => gap x ^ (-(k:ℝ))*P x) atTop (𝓝 0)) :
    Tendsto (fun x => (gap x)⁻¹^k*P x) atTop (𝓝 0) := by
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.rpow_neg (gp hx).le,Real.rpow_natCast,inv_pow]

private lemma revenue (A : Postage) (ε : ℝ) (he : 0<ε) : ∀ᶠ y : ℝ in atTop,
    let k:=A.D; let H:=A.H; let p:=p₁ y; let B:= (M₁ y:ℝ); let g:=gap y
    (H*g^A.power)*((1+B)^k*(2*p₀ y)^k) ≤ ε ∧
    H*g⁻¹^k*Real.exp (-A.rate*B) ≤ ε ∧
    H*g⁻¹^k*Real.exp (-A.rate*p^ (2:ℕ)/(1+B)^k+(k:ℝ)*(2*p^((1:ℝ)/5))) ≤ ε := by
  let B y : ℝ := M₁ y
  have hl := (light 2 ((A.D+A.D:ℕ):ℝ) A.power A.pos_p).const_mul (A.H*2^A.D)
  rw [mul_zero] at hl
  simp only [Real.rpow_natCast, pow_add] at hl
  have hp := (negk A.D (shadows (-(A.D:ℝ)) A.rate A.pos)).const_mul A.H
  rw [mul_zero] at hp
  have hw := (negk A.D (incinerate (-↑A.D) A.rate chorus.center (((A.D:ℝ))*2) (2*A.D) A.pos chorus.above)).const_mul A.H
  rw [mul_zero] at hw
  filter_upwards [hl.eventually (ge_mem_nhds he), hp.eventually (ge_mem_nhds he), hw.eventually (ge_mem_nhds he),
    switchUp, counting.eventually (eventually_gt_atTop 0),clock.eventually (eventually_ge_atTop (1:ℝ))] with y hl hp hw hy hB hC
  intro k H p X g
  have hH :0<H:=lt_of_lt_of_le zero_lt_one A.h_ge
  have hg : 0<g:=gp (by have := hy.2.2.2;linarith)
  have ha : 0<A.rate:=A.pos
  have hz := bump (x:=y)
  have ht : p₁ y ≤ p₀ y := Real.exp_monotone (Real.rpow_le_rpow_of_exponent_le hC chorus.below)
  have hN : 0<p₀ y := wp _ _
  constructor
  · apply le_trans _ hl
    calc
      _ ≤ H*g^A.power*(p₀ y^k*(2*p₀ y)^k) := by gcongr; exact hy.2.1.trans ht
      _ = _ := by change _ = H*2^k*((p₀ y)^k*(p₀ y)^k*g^A.power); rw [mul_pow]; ring
  have hb' : 1 ≤ (Clock.cover y:ℝ) := by exact_mod_cast (show 1 ≤ Clock.cover y from hB)
  constructor
  · apply le_trans _ hp
    change _ ≤ H*(g⁻¹^k*Real.exp _); rw [← mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Real.exp_monotone (mul_le_mul_of_nonpos_left ?_ (by linarith))
    change (Clock.cover y:ℝ) ≤ X; unfold X chorus body; push_cast; nlinarith
  apply le_trans _ hw
  change _ ≤ H*(g⁻¹^k*Real.exp _); rw [← mul_assoc H]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_monotone
  have hz := pow_le_pow_left₀ (show (0:ℝ) ≤ 1+X by unfold X; positivity) hz k
  rw [← pow_mul] at hz
  change -A.rate*p^ (2:ℕ)/_+k*(2*p^_) ≤ -A.rate*p^ (2:ℕ)/_+(k:ℝ)*2*p^_
  rw [← mul_assoc]
  simp only [neg_mul,neg_div]
  apply add_le_add_left (neg_le_neg ?_)
  exact div_le_div_of_nonneg_left (by positivity) (by unfold X; positivity) hz

/-- At the same x, both threshold regimes affordable; incl uniformity even
when x is selected near highest requested work stretch. -/
lemma performs (L θ : ℝ) (ht : θ ≤ F.thin) : ∀ᶠ x in atTop, Chorus F L θ x := by
  have hm := F.surplus ht
  have hh := chorus.support 2 one_lt_two
  have ha := plain.support 2 one_lt_two
  have hp : Similar (fun t => p₀ t^F.accuracy) := similar_watch_power 2 F.accuracy
  have ht : Similar (fun t => p₁ t^((1:ℝ)/5)) := similar_watch_power _ _
  filter_upwards [F.ln_charge L,ha,hh,hp 2 one_lt_two,ht 2 one_lt_two,
    advance (hm.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))),advance switchUp,
    advance (kcover F.funds F.accuracy F.toll),advance (revenue F.funds F.accuracy F.toll)] with x hl hA hh hp ht hK hB hM hX
  refine ⟨fun a b hx hy => ⟨hh a b hx hy,hA a b hx hy⟩,hl,fun a hx => ?_,fun a b hx hy => ?_⟩
  · have hm := hK a hx
    have he := hp a x hx (same x)
    have ho : F.funds.bundle chorus θ a a ≤ 1/2 * p₀ a^F.accuracy := by
      apply (div_le_iff₀ (Real.rpow_pos_of_pos (wp plain.center a) _)).mp hm
    linarith
  intro M g p k H c d
  obtain ⟨h1,h2⟩:=hM a hx
  obtain ⟨h3,h4,h5⟩:= hX a hx
  obtain ⟨hB,-,hB',hu⟩:=hB a hx
  have hi : 0 ≤ H:= (lt_of_lt_of_le zero_lt_one F.funds.h_ge).le
  have hk : 0<g:=gp (by linarith)
  refine ⟨hB,hu,hB',le_trans ?_ h3,h4,h1,h2,le_trans ?_ h5⟩
  · have he : p₀ x ≤ 2*p₀ a := (hA _ _ (same x) hx).peek.1
    have ha : 0<p₀ x := wp _ _
    change _ ≤ H*g^F.funds.power*(M^k*(2*p₀ a)^k)
    gcongr
  change _ ≤ H*g⁻¹^k*Real.exp (-c*p^ (2:ℕ)/M^k+(k:ℝ)*(2*p^((1:ℝ)/5)))
  have he : p₁ b^((1:ℝ)/5) ≤ 2*p^((1:ℝ)/5) := ht b a hy hx
  gcongr
end Focus
end YM.Next.Scheduling.Weak
