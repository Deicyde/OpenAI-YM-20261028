import YM.Next.SCHEDULE.Chorus

/-!
# Work reservation clocks

Charged from waits after L & Bar (physical spacings e^-s). Afford the
*whole* window: h log L ≤ (bMax+4)*log p(x), x=hatBeta(k), both directions
of a plateau. Require one station pegged for every finite set of simultaneous
calls. Focusing params post-L, upper b pre-L. Whole region periods to be
rechecked by caller: can request larger Stalls, growth/hyper-logs but NOT
adaptively choose new k later for unplanned estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Weak
open Filter Function RG RG.Supply Bid Precision Lattice Real Clock Instrument
open scoped Topology
local notation "p₀" => plain.P
local notation "M₀" => plain.body

variable {G : Gauge}

def population (g b x : ℝ) := b+g*x -- g=β slope b=bar here

def spread (B x : ℝ) := (B+4)*Real.log (p₀ x) -- B max b exponent here

def stop (B L x : ℝ) := Nat.ceil (spread B x/Real.log L)

private lemma increasing (b g : ℝ) (hg : 0<g) : Tendsto (population g b) atTop atTop :=
  tendsto_atTop_add_const_left _ b (Tendsto.const_mul_atTop hg tendsto_id)

lemma sqrt_sublog : Tendsto (fun x : ℝ => Real.log (p₀ x)*gap x) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => p₀ x * gap x) atTop (𝓝 0) := by
    simpa [P,plain] using light 2 1 1 (by norm_num)
  apply squeeze_zero' _ _ hp
  · filter_upwards [eventually_gt_atTop (0:ℝ),(growing (show 0<plain.center by norm_num [plain])).eventually_ge_atTop 1]
      with x hx hh using mul_nonneg (Real.log_nonneg hh) (gp hx).le
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact mul_le_mul_of_nonneg_right (le_trans (Real.log_le_sub_one_of_pos (wp plain.center x)) (by linarith)) (gp hx).le

lemma speed (b g : ℝ) (hg : 0<g) : Tendsto (fun s => Real.log (p₀ (population g b s))/s) atTop (𝓝 0) := by
  let x := population g b
  have hx := increasing b g hg
  have hh : Tendsto (fun s : ℝ => x s/s) atTop (𝓝 g) := by
    have ht := ((tendsto_const_nhds (x:=b)).div_atTop tendsto_id).add (tendsto_const_nhds (x:=g))
    rw [zero_add] at ht; apply ht.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    change b/s+g=_; unfold x population; field_simp
  have hp := ((sqrt_sublog.comp hx).mul (checks_gauge.comp hx)).mul hh
  rw [zero_mul,zero_mul] at hp
  refine hp.congr' ?_
  filter_upwards [hx.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℝ)] with s hs hz
  change Real.log (p₀ (x s))*gap (x s)*gap (x s)*(x s/s)=_
  unfold Clock.gap; have he:=Real.sq_sqrt hs.le; field_simp
  unfold x; rw [he,mul_div_cancel_right₀ _ hs.ne']

lemma within (B b g L : ℝ) (h : 0 ≤ B) (hg : 0 < g) (hL : 1<L) :
    Tendsto (fun s : ℝ => (stop B L (population g b s):ℝ)/s) atTop (𝓝 0) := by
  let x := population g b
  let F (s : ℝ) := spread B (x s)/Real.log L
  have hh : Tendsto (fun s => F s/s) atTop (𝓝 0) := by
    have hu:= ((speed b g hg).const_mul (B+4)).div_const (Real.log L); rw [mul_zero,zero_div] at hu
    apply hu.congr; intro s
    unfold F spread x; ring
  have ht := hh.add ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop tendsto_id)
  rw [add_zero] at ht
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs using div_nonneg (by positivity) hs
  have hl:=Real.log_pos hL
  have hm := (growing (d:=plain.center) (by norm_num [plain])).comp (increasing b g hg)
  filter_upwards [eventually_gt_atTop (0:ℝ),hm.eventually_ge_atTop 1] with s hs hX
  have hx : 0 ≤ F s := div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hX)) hl.le
  rw [id_eq,← add_div]; exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hx).le hs.le

/-- Choose at a large s.For vision ranges pre-L. Expect to use
`Roster` only with 0 ≤ B (`e j j` maximum b; not B=cover). `ample` and
`pace` pay period and zoom bounds in E\S k including b=0 corner. `volume`
can assume ghat from realized scale later. -/
structure Roster (F : Focus) (θ L B b g s : ℝ) : Prop where
  runway :
    let x:=population g b s
    1 ≤ (M₀ x:ℝ) ∧ 1 ≤ p₀ x ∧ 0 < x ∧ 0 < s ∧ 4096 ≤ x
  length : -- include the last price volatility
    let x:=population g b s
    L^ (2:ℕ)*(M₀ x:ℝ)^ (10:ℕ) ≤ p₀ x^ (2:ℕ) ∧ (M₀ x:ℝ)^ (10:ℕ)*L ≤ F.lower*p₀ x^F.positive
  bill : -- adjacent clocks across *all* indices needed
    let x:=population g b s
    g*spread B x ≤ Real.sqrt x
  ample : -- R/a at end can pay MUCH more than any of these P powers
    let x:= population g b s
    F.funds.H*p₀ x ^ ((B+4)*((F.funds.D:ℝ)+1)) ≤ Real.exp (s-spread B x)
  pace : spread B (population g b s) ≤ s/2
  songs : Chorus F L θ (population g b s)

private lemma runway_shape (L : ℝ) (F : Focus) (hL : 1<L) : ∀ᶠ x : ℝ in atTop,
    L^ (2:ℕ)*(M₀ x:ℝ)^ (10:ℕ) ≤ p₀ x^ (2:ℕ) ∧ (M₀ x:ℝ)^ (10:ℕ)*L ≤ F.lower*p₀ x^F.positive := by
  have hm : 0<F.lower := F.posL
  have hl : 0<L:=by linarith
  have hh := (ceiling_cheaper 2 2 10 one_lt_two (by norm_num))
  have ha := ceiling_cheaper 2 F.positive 10 one_lt_two F.pos
  filter_upwards [hh.eventually (ge_mem_nhds (show 0 < 1/L^ (2:ℕ) by positivity)),
    ha.eventually (ge_mem_nhds (show 0<F.lower/L by positivity))] with x hx hz
  let M : ℝ := Clock.cover x
  have he : 0<p₀ x := wp _ _
  have hP:= (div_le_iff₀ (Real.rpow_pos_of_pos he 2)).1 hx
  have hu:= (div_le_iff₀ (Real.rpow_pos_of_pos he F.positive)).1 hz
  have hK : M=(M₀ x:ℝ) := by simp [M,Instrument.body,plain]
  have hx : (M₀ x:ℝ)^ (10:ℕ) ≤ (1+(Clock.cover x:ℝ))^(10:ℕ) := pow_le_pow_left₀ (by positivity) (by rw [← hK]; unfold M; linarith) _
  exact ⟨(mul_le_mul_of_nonneg_left (hx.trans hP) (by positivity)).trans_eq (by rw [Real.rpow_two]; field_simp),
    (mul_le_mul_of_nonneg_right (hx.trans hu) hl.le).trans_eq (by field_simp)⟩

lemma Roster.eventual (F : Focus) (θ L B b g : ℝ) (hf : θ ≤ F.thin) (_h : 0 ≤ B) (hg : 0 < g) (hL : 1<L) :
    ∀ᶠ s in atTop, Roster F θ L B b g s := by
  let x := population g b
  have hx:=increasing b g hg
  let A := (B+4)*((F.funds.D:ℝ)+1)
  have hA : Tendsto (fun s => (Real.log F.funds.H+(A+B+4)*Real.log (p₀ (x s)))/s) atTop (𝓝 0) := by
    have hu := ((tendsto_const_nhds (x:=Real.log F.funds.H)).div_atTop tendsto_id).add ((speed b g hg).const_mul (A+B+4))
    rw [mul_zero,add_zero] at hu
    apply hu.congr; intro s; unfold x; simp only [id_eq]; ring
  have hb := hA.eventually (ge_mem_nhds zero_lt_one)
  have hm := ((speed b g hg).const_mul (B+4)).eventually (ge_mem_nhds (show (B+4)*0 < 1/2 by norm_num))
  have hr := ((sqrt_sublog.const_mul (g*(B+4))).comp hx).eventually (ge_mem_nhds (show g*(B+4)*0<1 by norm_num))
  have hp:=plain.pitched
  filter_upwards [hx.eventually (hp.and ((runway_shape L F hL).and (F.performs _ θ hf))),hb,hm,hr,eventually_gt_atTop (0:ℝ), hx.eventually_ge_atTop 4096] with s hx hb hm hr hs tall
  obtain ⟨⟨hx,hI,hP,H⟩,hR,hF⟩:=hx
  have hx' : 0<x s := by unfold x; linarith
  refine ⟨⟨?_, hP,hx',hs,tall⟩,hR,?_,?_,?_,hF⟩
  · exact_mod_cast (le_trans (by norm_num) hI : 1 ≤ _)
  · intro x
    have he:= Real.sqrt_pos.2 hx'
    let P := g*((B+4)*Real.log (p₀ x))
    have h : P/Real.sqrt x ≤ 1 := by
      unfold P; change _*(Real.log _*gap _)≤1 at hr; unfold Clock.gap at hr
      simp only [div_eq_mul_inv,mul_assoc] at *; exact hr
    simpa [P,spread] using (div_le_iff₀ he).1 h
  · intro y
    have he :0<F.funds.H:=lt_of_lt_of_le zero_lt_one F.funds.h_ge
    have hG:= (Real.rpow_pos_of_pos (wp plain.center y) A)
    apply (Real.log_le_log_iff (mul_pos he hG) (Real.exp_pos _)).mp
    rw [Real.log_mul he.ne' hG.ne',Real.log_rpow (wp plain.center y), Real.log_exp]
    have hb:= (div_le_iff₀ hs).1 (show (Real.log F.funds.H+(A+B+4)*Real.log (p₀ y))/s ≤ 1 from hb)
    unfold spread; change log F.funds.H+A*Real.log (p₀ y) ≤ _; linarith
  unfold spread
  change (B+4)*(Real.log _/s) ≤ 1/2 at hm; rw [← mul_div_assoc] at hm
  have hh := (div_le_iff₀ hs).1 hm; linarith
end YM.Next.Scheduling.Weak
