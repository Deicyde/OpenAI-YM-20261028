import YM.Bid.Fuels
import YM.Next.WARD_BIN.Flush
import YM.Org.Input



/-!
# Tail checks independent of the cylinder/readout problem

Includes native geometry gate and suppression of t powers vs κ, γ and scale s.
Constants finite in requested stencil; column sizes are the actual trajectory
commitments. Nothing constructs a schedule with any *new* requirements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Filter Set Lattice Wilson RG Source MeasureTheory
open scoped Topology BigOperators
variable {G : Gauge} {T : History G} {C : Family G} {n : Side}

section Cheap
variable {I J : Type*} {f : Filter I} {s u v : I → ℝ}

def Cheap (f : Filter I) (s b : I→ℝ) := ∀ ε : ℝ,0 < ε → ∀ᶠ i in f, ‖b i‖ ≤ Real.exp (ε*s i)
namespace Cheap
lemma trans (h : Cheap f s u) (hv : ∀ᶠ i in f, ‖v i‖ ≤ ‖u i‖) : Cheap f s v := by
  intro ε he; filter_upwards [h ε he,hv] with i hi hh; exact hh.trans hi









end Cheap

end Cheap

section Hats
variable (T : Levels G) (hG : G.Simple)
open Real
lemma hot (n) : 0 < T.clock.hatBeta n := zero_lt_one.trans (T.fits.delayed _)
lemma stepG (n) : 0 < T.clock.hatCoupling n := inv_pos.mpr (sqrt_pos.mpr (hot T n))
lemma stepGle (n) : T.clock.hatCoupling n ≤ T.clock.threshold n :=
  le_mul_of_one_le_right (stepG T n).le (one_le_exp (sq_nonneg _))
lemma mon1 (n) : 1 ≤ T.clock.monitor n := one_le_exp (sq_nonneg _)
lemma force_pos (n) : 0<T.clock.forcedAllowance n := exp_pos _
include hG
lemma bell : Tendsto T.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _ (T.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma mid : Tendsto T.clock.monitor atTop atTop :=
  tendsto_exp_atTop.comp ((tendsto_pow_atTop (n := 2) (by decide)).comp (tendsto_log_atTop.comp (tendsto_log_atTop.comp (bell T hG))))

lemma abyss : Tendsto (fun i => (T.clock.coverSize i:ℝ)) atTop atTop := by
  have h := (tendsto_pow_atTop (n := 2) (by decide)).comp (tendsto_log_atTop.comp (bell T hG))
  exact tendsto_atTop_mono' _ (Eventually.of_forall fun _ => Nat.le_ceil _) h




lemma tiny : Tendsto T.clock.threshold atTop (𝓝 0) := by
  let a n := log (T.clock.hatBeta n)
  have ha : Tendsto a atTop atTop := tendsto_log_atTop.comp (bell T hG)
  have ht := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp (tendsto_log_atTop.comp ha)
  have hh : ∀ i,T.clock.threshold i=exp ((log (a i))^2-(1/2:ℝ)*a i) := by
    intro i
    have hg : Calendar.hatCoupling T.clock i = exp (- (1/2:ℝ)*a i) := by
      let y := T.clock.hatBeta i
      rw [← Real.exp_log (stepG T i)]; unfold Calendar.hatCoupling; rw [log_inv,Real.log_sqrt (hot T i).le]; unfold a; ring_nf
    unfold Calendar.threshold; rw [hg, show T.clock.monitor i=exp ((log (a i))^2) from rfl, ← Real.exp_add]; ring_nf
  rw [funext hh]; refine Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' _ ?_
    (ha.const_mul_atTop_of_neg (by norm_num : -(1/4:ℝ)<0)))
  filter_upwards [ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4)),ha.eventually (eventually_gt_atTop 0)] with i hi he
  change (log (a i))^2 * exp (-log (a i)) ≤ _ at hi
  rw [exp_neg,exp_log he, ← div_eq_mul_inv, div_le_iff₀ he] at hi; linarith
lemma pale (d : ℕ) : Tendsto (fun i => (T.clock.hatCoupling i)⁻¹^d*sqrt (T.clock.forcedAllowance i)) atTop (𝓝 0) := by
  let a n := log (T.clock.hatBeta n)
  have ht : Tendsto a atTop atTop := tendsto_log_atTop.comp (bell T hG)
  let u (i : ℕ) := d*(a i/2) - exp ((log (a i))^2*(1/5:ℝ))/2
  have hv (i) : (T.clock.hatCoupling i)⁻¹^d*sqrt (T.clock.forcedAllowance i)=exp (u i) := by
    have he := hot T i
    rw [← Real.exp_log (mul_pos (pow_pos (inv_pos.mpr (stepG T i)) _) (sqrt_pos.mpr (force_pos T i))),
      Real.log_mul (pow_pos (inv_pos.mpr (stepG T i)) _).ne' (sqrt_pos.mpr (force_pos T i)).ne',
      log_pow,Real.log_sqrt (force_pos T i).le, Calendar.hatCoupling, Calendar.forcedAllowance, inv_inv,Real.log_sqrt he.le,Calendar.monitor,← exp_mul, log_exp]
    unfold u a; ring_nf
  simp_rw [hv]; apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot_mono' _ _ (ht.const_mul_atTop_of_neg (by norm_num : (-1:ℝ) < 0))
  filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop (10:ℝ)),
    ht.eventually (eventually_ge_atTop (d+2:ℝ))] with i hi hp
  change 10 ≤ log (a i) at hi; change _ ≤ a i at hp
  have hh : 0 < a i := Real.log_pos (T.fits.delayed _)
  have hm : (a i)^2 ≤ exp ((log (a i))^2*(1/5:ℝ)) := by
    rw [← Real.log_le_iff_le_exp (pow_pos hh _), Real.log_pow]; norm_num; nlinarith
  change u i ≤ _; unfold u; nlinarith
lemma subm (c : ℝ) (hc : 0≤c) (d : ℕ) :
    Tendsto (fun i => (T.clock.hatCoupling i)⁻¹^d*(exp (c*T.clock.forcedAllowance i)-1)/sqrt (T.clock.forcedAllowance i)) atTop (𝓝 0) := by
  let g (i : ℕ) := T.clock.forcedAllowance i
  have hz (i) : sqrt (g i)^ (2:ℕ)=g i := sq_sqrt (force_pos T i).le
  have h : Tendsto (fun i => c*g i) atTop (𝓝 0) := by
    have ht : Tendsto (fun i => sqrt (g i)) atTop (𝓝 0) := by simpa [g] using! pale T hG 0
    have hv : Tendsto g atTop (𝓝 0) := by
      have he := ht.pow 2; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,hz] at he; exact he
    simpa using! hv.const_mul c
  have he : Tendsto (fun i => (2*c)*((T.clock.hatCoupling i)⁻¹^d*sqrt (g i))) atTop (𝓝 0) := by simpa [g] using! (pale T hG d).const_mul (2*c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he (Eventually.of_forall fun i => ?_) ?_
  · have hp := force_pos T i; apply div_nonneg (mul_nonneg _ (sub_nonneg_of_le (one_le_exp (mul_nonneg hc hp.le)))) (sqrt_nonneg _)
    exact pow_nonneg (inv_pos.mpr (stepG T i)).le _
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))] with i hi
  change c*g i ≤ 1 at hi; have hp : 0 ≤ c*g i := mul_nonneg hc (force_pos T i).le
  have hH : exp (c*g i)-1 ≤ 2*(c*g i) := by
    have hr := Real.norm_exp_sub_one_sub_id_le (x:=c*g i) (by simpa only [Real.norm_of_nonneg hp] using hi)
    have hx := (Real.le_norm_self _).trans hr; rw [Real.norm_of_nonneg hp] at hx
    generalize c*g i=t at *; nlinarith only [hx,hp,hi]
  change _ ≤ _; rw [div_le_iff₀ (sqrt_pos.mpr (force_pos T i))]
  exact le_trans (mul_le_mul_of_nonneg_left hH (pow_nonneg (inv_pos.mpr (stepG T i)).le _))
    (le_of_eq (by change _ = 2*c* (_*sqrt (g i))*sqrt (g i); generalize hs : √(g i)=x; have hx : x^2=g i := hs ▸ hz i;
                  linear_combination (norm:=ring) -(2*c *((T.clock.hatCoupling i)⁻¹^d))*hx))

end Hats

-- geometry & actual band at the cutoff, without increasing local index
lemma fits_event (S : Finset Cover) (T : Schedule) : ∀ᶠ i in atTop, ∀ p, FitsIn S (T.side i p) := by
  obtain ⟨k,H⟩ := large_fits S
  filter_upwards [T.den_strict.tendsto_atTop.eventually (eventually_ge_atTop k)] with i hi p
  exact H _ (hi.trans (le_mul_of_one_le_left (Nat.zero_le _) (T.period p).property))

def cord (S : Finset Cover) := S.sup fun x => Finset.univ.sup fun i => (x i).natAbs
lemma contained (S : Finset Cover) (o : Site n) : footprint S o ⊆ halo (cord S) {o} := by
  intro i hi; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
  refine halo_spec.mpr ⟨o,by simp,?_⟩
  rw [separation_comm,separation, add_sub_cancel_right]
  apply Finset.sup_le; intro i _
  exact (Corona.lap x i).trans ((Finset.le_sup (f:=fun i => (x i).natAbs) (Finset.mem_univ i)).trans (Finset.le_sup (f:=fun x => Finset.univ.sup fun i => (x i).natAbs) hx))
lemma cover_le_one (S : Finset Cover) (o : Site n) (b) (hb : cord S ≤ b) : coverNumber b (footprint S o) ≤ 1 := by
  let Y := footprint S o
  refine le_trans (Corona.list_cost b (X:=Y) (D:={o}) ⟨fun _ hk => ?_, Corona.ship_halo b ?_⟩) (by simp)
  · exact Corona.halo_mono hb (Finset.Subset.refl _) (contained S o hk)
  intro i hi j hj; rw [Finset.mem_singleton.mp hi, Finset.mem_singleton.mp hj]

lemma tooth (hc : C.Makes) (S : Finset Cover) (hG : G.Simple) : ∀ᶠ i in atTop, ∀ p, ∀ o : Site (C.side i p),
    coverNumber (face C i p).B (footprint S o) ≤ 1 := by
  filter_upwards [(abyss C.path.levels hG).eventually (eventually_ge_atTop (cord S:ℝ))] with i hi p o
  refine cover_le_one S o _ ?_
  unfold face roof; rw [(hc.wilson.represents _ _ _ le_rfl).vac]; exact_mod_cast hi

lemma rated (hc : C.Makes) (p N) : 0 < C.beta N p ∧ (C.beta N p)⁻¹/(face C N p).threshold^(2:ℕ) ≤
    2*(C.path.levels.clock.monitor N)⁻¹^2 := by
  let T := C.path.levels; let x := T.clock.hatBeta N
  have ht : 0 < x := hot _ _
  have hv : 0 < x/2 := half_pos ht
  have hx : x/2 ≤ C.beta N p := (hc.wilson.represents N p N le_rfl).band.1
  let s := T.clock.monitor N
  have hp : 0 < s := zero_lt_one.trans_le (mon1 _ _)
  have he : (face C N p).threshold = T.clock.threshold N := by unfold face roof; rw [(hc.wilson.represents _ _ _ le_rfl).vac]; rfl
  refine ⟨hv.trans_le hx, (div_le_div_of_nonneg_right (inv_anti₀ hv hx) (pow_nonneg (face C N p).threshold_pos.le _)).trans_eq ?_⟩
  rw [he]; change (x/2)⁻¹ / ((Real.sqrt x)⁻¹ * s)^2 = 2*s⁻¹^2
  rw [mul_pow, inv_pow, Real.sq_sqrt ht.le]; field_simp

lemma covers_coupling (hc : C.Makes) (p N) : (C.beta N p)⁻¹/(face C N p).threshold^(2:ℕ) ≤ 2 := calc
    _ ≤ 2*(C.path.levels.clock.monitor N)⁻¹^2 := (rated hc ..).2
    _ ≤ _ := by
      have hv := mon1 C.path.levels N
      rw [inv_pow]; exact mul_le_of_le_one_right (by norm_num) (inv_le_one_of_one_le₀ (one_le_pow₀ hv))

/-- Actual joint parameters at top approach, uniformly before the period extraction. -/
lemma headway (hc : C.Makes) (hG : G.Simple) {Q : ℝ×ℝ → Prop} (h : ∀ᶠ x in 𝓝 0,Q x) :
    ∀ᶠ i in atTop, ∀ p, let t := (face C i p).threshold; Q (t,(C.beta i p)⁻¹/t^(2:ℕ)) := by
  let T := C.path.levels
  obtain ⟨ε,hε,H⟩ := Metric.eventually_nhds_iff.mp h
  have ht := tiny T hG
  have he : Tendsto (fun N => 2*(T.clock.monitor N)⁻¹^2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (mid T hG)
    simpa using! (h.pow 2).const_mul (2:ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds hε),he.eventually (gt_mem_nhds hε)] with i hi hE p
  apply H
  obtain ⟨hp,hq⟩ := rated hc p i
  let u := (face C i p).threshold
  have hg : 0 < u := (face C i p).threshold_pos
  rw [Prod.dist_eq]; simp only [Prod.fst_zero,Prod.snd_zero,dist_zero_right]; refine max_lt ?_ ?_
  · rw [Real.norm_of_nonneg hg.le]; unfold u face roof; rw [(hc.wilson.represents _ _ _ le_rfl).vac]; exact hi
  rw [Real.norm_of_nonneg (show 0 ≤ _ from div_nonneg (inv_pos.mpr hp).le (pow_nonneg hg.le _))]; exact hq.trans_lt hE

lemma ink_event (S : Finset Cover) (d : ℕ) (hc : C.Makes) (hG : G.Simple) : ∀ᶠ N in atTop,
    ∀ p, inkage (face C N p) (native C N p S) d (cash C N) (κ C.path N) := by
  let T := C.path.levels
  filter_upwards [(subm T hG S.card (Nat.cast_nonneg _) d).eventually (ge_mem_nhds zero_lt_one)] with i hi p
  let Y := native C i p S
  have hv := force_pos T i
  have hx : T.clock.hatCoupling i ≤ (face C i p).threshold := by
    unfold face roof; rw [(hc.wilson.represents _ _ _ le_rfl).vac]; exact stepGle T i
  unfold inkage; apply le_trans _ (show (T.clock.hatCoupling i)⁻¹ ^d * _ ≤ _ from (div_le_one (Real.sqrt_pos.mpr hv)).mp hi)
  apply mul_le_mul
  · exact pow_le_pow_left₀ (inv_nonneg.mpr ((stepG T i).le.trans hx)) (inv_anti₀ (stepG T i) hx) d
  · refine sub_le_sub (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hv.le)) le_rfl
    exact_mod_cast (Finset.card_image_le : Y.card ≤ S.card)
  · exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hv.le))
  exact pow_nonneg (inv_pos.mpr (stepG T i)).le d
end YM.WardBin
