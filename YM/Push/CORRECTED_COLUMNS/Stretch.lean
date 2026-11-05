import YM.Overlay.Terminal


/-!
# Placement affordability: the numerical sublinear windows used in RankWidths

Only these placement requests priced here, not any promises of estimates
from the RG/marks producers. Intended to be included with those costs when
choosing `Wait`, not purchasing run length after using `Family`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Zone
open RG RG.Supply Lattice Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- Least power step for target x (>0), L>1. -/
def leaps (L x : ℝ) := Nat.ceil (Real.log x / Real.log L)
lemma buy {L x : ℝ} (hL : 1 < L) (hx : 0 < x) (n : ℕ) : leaps L x≤n ↔ x ≤ L^n := by
  have hh := zero_lt_one.trans hL
  unfold leaps; rw [Nat.ceil_le, div_le_iff₀ (Real.log_pos hL), ← Real.log_pow,
    Real.log_le_log_iff hx (pow_pos hh _)]

namespace Demand

def cal (β : ℝ) := Real.exp ((Real.log (Real.log β))^2)
def long (β b L : ℝ) := leaps L ((cal β)^(b+2))
def halo (β L : ℝ) := leaps L ((Nat.ceil (Real.log β^2):ℝ)^(10:ℕ))
def need (β b L : ℝ) := long β b L+halo β L



-- All ratio/other costs already fixed at EACH plateau when using this.
lemma ratio_sub (b L : ℝ) (hb : 0≤b) (hL : 1<L) :
    Tendsto (fun β : ℝ => (need β b L : ℝ) / β) atTop (𝓝 0) := by
  have hx : ∀ᶠ β : ℝ in atTop, (cal β)^(b+2) ≤ β := by
    filter_upwards [YM.Vac.Numbers.cost (b+2) 1 (by norm_num)] with β h
    rw [Real.rpow_one] at h; exact h
  have hh : ∀ᶠ β : ℝ in atTop, (Nat.ceil (Real.log β^ (2:ℕ)):ℝ) ≤ β := by
    have hp := (Real.isLittleO_pow_log_id_atTop (n:=2)).def (c:=1/2) (by norm_num)
    filter_upwards [hp,eventually_ge_atTop (2:ℝ)] with s hs h
    have hS : 0 ≤ s := by linarith
    have ht : ‖Real.log s^2‖ ≤ 1/2*‖s‖ := hs
    rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg hS] at ht
    linarith [Nat.ceil_lt_add_one (sq_nonneg (Real.log s))]
  have H : ∀ᶠ β : ℝ in atTop, (need β b L : ℝ) ≤ 11*(Real.log β / Real.log L)+2 := by
    filter_upwards [hx,hh,eventually_gt_atTop (1:ℝ)] with s hs h hp
    have hz := Real.log_pos hL
    have hg : 1 ≤ (cal s)^(b+2) := by
      have hq : 0≤b+2 := by linarith
      exact Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) hq
    have ha : 0<Nat.ceil (Real.log s^2) := Nat.ceil_pos.mpr (sq_pos_of_pos (Real.log_pos hp))
    have hr : 1 ≤ ((Nat.ceil (Real.log s^(2:ℕ)):ℝ)) := by exact_mod_cast ha
    have he (x q : ℝ) (h₁ : 1≤x) (h₂ : x≤q) : (leaps L x:ℝ) ≤ Real.log q/Real.log L+1 :=
      (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg h₁) hz.le)).le.trans (by
        gcongr)
    have Hu := he _ s hg hs
    have Hw := he _ (s^10) (show 1 ≤ (Nat.ceil (Real.log s^2):ℝ)^(10:ℕ) from one_le_pow₀ hr)
      (pow_le_pow_left₀ (by positivity) h _)
    rw [Real.log_pow] at Hw; unfold need long halo; rw [Nat.cast_add]; push_cast at Hw
    exact (add_le_add Hu Hw).trans_eq (by ring)
  have he : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n:=1)).tendsto_div_nhds_zero
  have hv : Tendsto (fun x : ℝ => (11*(Real.log x/Real.log L)+2)/x) atTop (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => 2/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    convert (he.const_mul (11/Real.log L)).add ha using 1
    · funext x; ring
    simp
  apply squeeze_zero' ?_ ?_ hv
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs; positivity
  filter_upwards [H,eventually_gt_atTop (0:ℝ)] with s hs hp
  exact div_le_div_of_nonneg_right hs hp.le

lemma sub (b B M L : ℝ) (hb : 0≤b) (h : 0<M) (hL : 1 < L) :
    Tendsto (fun x : ℝ => (need (B+M*x) b L : ℝ)/x) atTop (𝓝 0) := by
  let y x := B+M*x
  have hp : Tendsto y atTop atTop := tendsto_atTop_add_const_left _ B (tendsto_id.const_mul_atTop h)
  have ht : Tendsto (fun x : ℝ => y x/x) atTop (𝓝 M) := by
    have hv := (tendsto_const_nhds (x:=B)|>.div_atTop (tendsto_id (x:=(atTop: Filter ℝ)))).add (tendsto_const_nhds (x:=M))
    rw [zero_add] at hv; apply hv.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    change B / s + _ = _
    unfold y; field_simp
  have he := ((ratio_sub b L hb hL).comp hp).mul ht
  rw [zero_mul] at he; apply he.congr'
  filter_upwards [hp.eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with s hs hv
  change (need (y s) b L : ℝ)/y s * _=↑(need (y s) _ _)/s
  field_simp
end Demand

namespace Coverage
variable {S : Sheet G} {w : Rolls S} {T : Protection w} {W : Delays T} {Y : Bar W}

-- extension (only before choosing calendar). Incorporate arbitrarily
-- many other sublinear gatings via `U` in scope. j exponent pays any
-- fixed b on some stage onward.
def seats (h : G.Simple) (U : Wait Y) : Wait Y where
  readyHere := U.readyHere
  window j x := U.window j x + Demand.need (Y.value+G.slopeConstant*x) (j:ℝ) (w.L j).val
  sublin j := by
    have hL : (1:ℝ) < (w.L j).val := by exact lt_of_lt_of_le (by norm_num : (1:ℝ)<3) (by exact_mod_cast (w.large j).size)
    simp_rw [Nat.cast_add,add_div]
    simpa only [add_zero] using (U.sublin j).add (Demand.sub (j:ℝ) Y.value G.slopeConstant (w.L j).val
      (Nat.cast_nonneg _) (G.slopeConstant_pos h) hL)
  minLength := U.minLength
lemma paysEarlier (h : G.Simple) (U : Wait Y) {A} (H : Paid (seats h U) A) : Paid U A := by
  refine { H with run := ?_ }
  intro j hj
  obtain ⟨k,hk,hi,hR⟩ := H.run j hj
  have hx : U.window j (A.S.scale k) ≤ (seats h U).window j (A.S.scale k) := Nat.le_add_right ..
  exact ⟨k,hk,hx.trans hi,fun i he hf => hR _ (by omega) (by omega)⟩
end Coverage

section
variable (A : Levels G) (b : ℝ)
def factor (k : ℕ) := (A.clock.factor (A.clock.J k)).val
def boxes (k : ℕ) := Demand.long (A.clock.hatBeta k) b (factor A k)
def cube (k : ℕ) := Demand.halo (A.clock.hatBeta k) (factor A k)
def stretch (k : ℕ) := boxes A b k+cube A k
def base (k : ℕ) := k-stretch A b k

def gain (k : ℕ) := A.clock.monitor k^b
def scale (k : ℕ) := A.S.a k*gain A b k

structure Allows (k : ℕ) : Prop where
  positive : 0 < k
  onward : stretch A b k ≤ k
  plateau (i : ℕ) : base A b k ≤ i → i ≤ k → A.clock.J i=A.clock.J k





lemma exp_size (k : ℕ) (hk : 0<k) : 3 ≤ factor A k := by
  obtain ⟨i,he⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [factor,he, A.fits.sameFactor i]; exact A.S.block_large i

lemma width {k : ℕ} (h : Allows A b k) :
    A.S.a k * (factor A k:ℝ)^stretch A b k=A.S.a (base A b k) := by
  let s := base A b k
  have HH : s + stretch A b k=k := Nat.sub_add_cancel h.onward
  have he (i) (hi : i≤stretch A b k) :
      A.S.a (s+i)*(factor A k:ℝ)^i=A.S.a s := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hx := ih (by omega)
      rw [← Nat.add_assoc, A.S.a_step,pow_succ]
      have hy : (A.S.block (s+i)).val=factor A k := by
        unfold factor; rw [← h.plateau (s+i+1) (show s≤_ by omega) (by omega),← A.fits.sameFactor (s+i)]
      rw [hy]; have hL := exp_size A k h.positive
      have hv : 0 < (factor A k : ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) (by exact_mod_cast hL)
      rw [show _ / _ * ((factor A k:ℝ)^i*_) = A.S.a (s+i)*(factor A k:ℝ)^i by field_simp]
      exact hx
  simpa only [HH] using he (stretch A b k) le_rfl

-- Overshoot, ratios; explicitly use monitoring rho. Comparison exponents distinct.

lemma inflation {k} (h : Allows A b k) (p : ℕ) :
    (A.clock.coverSize k:ℝ)^(10:ℕ) ≤ (factor A k:ℝ)^p ↔ cube A k≤p :=
  let hi : 0 < (A.clock.coverSize k:ℝ) := Nat.cast_pos.mpr (A.budget k).B_pos
  let he : (1:ℝ) < factor A k := lt_of_lt_of_le (by norm_num : (1:ℝ)<3) (by exact_mod_cast exp_size A k h.positive)
  (buy he (pow_pos hi _) p).symm



lemma rising (h : G.Simple) : Tendsto A.clock.monitor atTop atTop := by
  have he : Tendsto A.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
  exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp he)))
lemma thin (h : G.Simple) (hb : 0<b) : Tendsto (gain A b) atTop atTop :=
  (tendsto_rpow_atTop hb).comp (rising A h)
lemma pointed (k) : 0 < gain A b k := Real.rpow_pos_of_pos (Real.exp_pos _) _
lemma positive (k) : 0 < scale A b k := mul_pos (A.S.a_pos _) (pointed A b k)

lemma goesZero (h : G.Simple) : Tendsto (scale A b) atTop (𝓝 0) := by
  have he : Tendsto A.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
  have hz : Tendsto (fun k => A.S.a k * A.clock.hatBeta k) atTop (𝓝 0) := by
    have ha : Tendsto (fun s : ℝ => s / Real.exp s) atTop (𝓝 0) := by
      simpa using (isLittleO_pow_exp_pos_mul_atTop 1 (zero_lt_one' ℝ)).tendsto_div_nhds_zero
    have hh := ((A.S.shrinks.mul_const A.clock.bar).add ((ha.comp A.S.divergent).mul_const G.slopeConstant))
    rw [zero_mul,zero_mul,zero_add] at hh
    apply hh.congr
    intro i
    change A.S.a i*A.clock.bar+A.S.scale i/Real.exp (A.S.scale i)*_= _
    change _=A.S.a i*(A.clock.bar+G.slopeConstant*A.S.scale i)
    rw [Stock.a_log A.S i,Real.exp_neg]; ring
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => (positive A b i).le) ?_ hz
  filter_upwards [he.eventually (YM.Vac.Numbers.cost b 1 zero_lt_one)] with i hi
  rw [Real.rpow_one] at hi
  exact mul_le_mul_of_nonneg_left hi (A.S.a_pos _).le
end
end YM.Push.Corrected.Zone
