import YM.SharpGram.Weak.Reading
import YM.SharpGram.Clauses
import YM.OPE.Levy.Invoice
import YM.Extra.WILSON_STARTUP.Fast
/-!
# Exact quota ratios, residual costs of crossing

Transport from r = atK k up to actual k costs a single coefficient price
power; not optimizing exponent. Inverse/readout bound applies even after
cutoff-dependent reps and on auxiliary sublimits. Cost explicit.
No claim about all-order physical coefficients; keep each marked observable's
frame costs for when paying perturbative comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak.Portfolio
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Next.Rank.East Further.CorrectedLift Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Price
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)}{H:C.Makes} (X : Portfolio C H D u)
local notation "A" => C.path.levels
local notation "P" => C.path.levels.clock.hatBeta
local notation "a" => C.S.a
local notation "F"=> standard C
local notation "σ"=> U.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels
variable {W r T0} (T : OPE.TableTickets C W r T0) (hG:G.Simple)

section microscopeB
include H
include T
lemma reverseWalk {d m k N p : ℕ} (x : C.label d) (he : C.ref d ≤ m) (hk : m ≤ k) (hp : k ≤ N) :
    quota C d k N p x ≤ a m / a k * quota C d m N p x := by
  induction k,hk using Nat.le_induction with
  | base => rw [div_self (C.S.a_pos m).ne',one_mul]
  | succ i hi ih =>
    let K := C.path.levels
    let ℓ : ℝ := (C.S.block i).val
    have hL : 0 < ℓ := by unfold ℓ; positivity
    have hs : (K.params (i+1)).columns ≤ ℓ := OPE.Columns.column_small T.system.costs.back
    calc
       _ ≤ _ := (H.calibrated _ _ p ((he.trans hi).trans ((Nat.le_succ i).trans hp))).back i (he.trans hi) hp _
       _ ≤ ℓ * (a m / a i * quota C d m N p x) := mul_le_mul hs (ih (by omega)) (quota_nonneg _) hL.le
       _ = _ := by rw [Schedule.a_step]; unfold ℓ; field_simp [(C.S.a_pos i).ne'];

omit T in
lemma resqueeze : ∀ᶠ k : ℕ in atTop, a (X.atK k) / a k ≤ P k := by
  filter_upwards [X.onLevel] with k ⟨_,h,_⟩
  have hP : 0 < P k := zero_lt_one.trans ((A).fits.delayed k)
  rw [Stock.a_log C.S k,Stock.a_log C.S (X.atK k),← Real.exp_sub]
  exact (Real.le_log_iff_exp_le hP).mp (by linarith only [h])

include hG
omit T in
lemma narrowed : ∀ᶠ k : ℕ in atTop, ∀ N p : ℕ, k ≤ N → Price.shrink C k N p ≤ 1 := by
  have he : Tendsto (A).clock.monitor atTop atTop := (Station.mag_rate _ hG (show (0:ℝ)<1 from zero_lt_one)).congr (fun i => Real.rpow_one _)
  filter_upwards [he.eventually_ge_atTop 2] with k hk N p hN
  have hP := zero_lt_one.trans ((A).fits.delayed k); have hw := (H.wilson.represents N p k hN).band.1
  have hb := Overlay.beta_positive (N:=N) (p:=p) H.wilson hN
  have hh : Real.sqrt (P k) ≤ 2 * Real.sqrt (C.path.β N p k) := by
    nlinarith only [hw,hb,Real.sqrt_nonneg (P k),Real.sqrt_nonneg (C.path.β N p k),Real.sq_sqrt hb.le, Real.sq_sqrt hP.le]
  have hs := Real.sqrt_pos.2 hP
  unfold Price.shrink Calendar.threshold Calendar.hatCoupling
  rw [div_le_one (mul_pos (inv_pos.mpr hs) (lt_of_lt_of_le zero_lt_two hk))]
  rw [inv_le_comm₀ (Real.sqrt_pos.2 hb) (mul_pos (inv_pos.mpr hs) (lt_of_lt_of_le zero_lt_two hk))] 
  rw [mul_inv_rev,inv_inv]
  refine (inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_two hk)).2 ?_
  exact hh.trans (mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg _))

omit hG
local notation "g!" => X.atK
-- solve for ANY label, no assumption it's detectable
lemma undo {d : Fin (D+1)} {k N p : ℕ}
    (q : C.label d) (hm : (g! k) ≤ k) (hn : k ≤ N) (hr : C.ref d ≤ g! k)
    (hy : Tested C d (g! k) N p (X.matrix k N p d)) (hl : Price.shrink C (g! k) N p ≤ 1)
    (hL : 1 ≤ mag A X.aperture (g! k)) :
    ∃ y : C.label d, microscope C X.aperture (X.atK k) (X.matrix k) d (N,p) y = q ∧
       ‖y‖ ≤ 2 / a k ^ d.val * quota C d k N p q := by
  let b:=shrink C (g! k) N p; let mu0 := mag A X.aperture (g! k)
  let l := C.labels.level d; let t := X.matrix k N p d
  have hb : 0 < b := shrink_pos C H (hm.trans hn) _
  have hu : 0 < mu0 := zero_lt_one.trans_le hL
  let w := l.scaled b (t q)
  let y := weightTag C d mu0⁻¹ w
  have hf : Solves C mu0 d (X.atK k) N p t y q := by
    change w = weightTag C _ mu0 y
    unfold y; rw [← LinearMap.comp_apply,← facsimile,mul_inv_cancel₀ hu.ne']; ext i; simp [weightTag]
  obtain ⟨z,hz,ht⟩:=solve C H hr (hm.trans hn) hy y mu0
  refine ⟨y,(ht _ (poured H hr (hm.trans hn) mu0 t hy y)).trans (ht _ hf).symm,?_⟩
  let x := awake C d (X.atK k) N p q
  let s := l.coeffSize; have hs : s (t q) ≤ 2*s x:= by linarith only [Work.G08.size_triangle l (t q) x, Work.G08.size_sub_rev l (t q) x, hy.score q, Work.G08.size_nonneg l x]
  have hw : s w ≤ s (t q) := by
    unfold s Labels.Frame.coeffSize
    apply Finset.sum_le_sum; intro i hi
    change ‖((↑(b^(l.grades i).2):ℂ)) * t q i‖ ≤ _
    rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (pow_pos hb _|>.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb.le hl)
  have hx0 : s y ≤ s w := by
    unfold s Labels.Frame.coeffSize
    apply Finset.sum_le_sum; intro i hi
    change ‖(↑mu0⁻¹:ℂ)^(l.grades i).1 * w i‖ ≤ _
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hu|>.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ((inv_pos.mpr hu).le) (inv_le_one_of_one_le₀ hL))
  have ha : s x = quota C d (g! k) N p q / a (g! k)^d.val := by
    unfold x Price.awake s; rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]; exact (div_eq_inv_mul ..).symm
  apply ((Size.norm_le l y).trans (hx0.trans (hw.trans hs))).trans
  rw [ha]
  calc
    _ ≤ 2 * _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (passPrice T q hr hm hn) (pow_pos (C.S.a_pos _) d.val).le) zero_le_two
    _ = _ := by rw [div_pow];field_simp [(C.S.a_pos k).ne',(C.S.a_pos (g! k)).ne']

include hG
lemma unzoom (d : Fin (D+1)) : ∀ᶠ k : ℕ in atTop, ∀ N p : ℕ, k < N → ∀ q : C.label d,
    ∃ y : C.label d, microscope C X.aperture (X.atK k) (X.matrix k) d (N,p) y = q ∧
       ‖y‖ ≤ 2 / a k ^ d.val * quota C d k N p q := by
  filter_upwards [X.onLevel, X.admits.eventually (narrowed (H:=H) hG),
    ((mag_rate _ hG X.apertures).comp X.admits).eventually_ge_atTop 1] with k ⟨hk,_,hy,_⟩ h0 hb N p hN q
  exact undo X T q hk hN.le (hy.early _ (Nat.le_of_lt_succ d.isLt)) (hy.charts N p (hk.trans_lt hN) d|>.1) (h0 _ _ (hk.trans hN.le)) hb

-- Stronger horizon-independent price exponents. Useful diagonally in k with bigger D(y) calibration,
-- same meters via physical reflected forms after crossing allowance.
omit T in
lemma energy_clock (d : ℕ) : OPE.RateLE atTop (fun k : ℕ=>Real.log (P k))
    (fun k => OPE.Levy.preExpense C d (X.atK k) X.aperture) 0:= by
   have hp := (Station.hat_rate C.path.levels hG)
   let t(k:ℕ) := Real.log (P k)
   have hr : Tendsto t atTop atTop:=Real.tendsto_log_atTop.comp hp
   let m(i:ℕ) := 2*((A).clock.monitor (X.atK i))
   have hh (b : ℝ) : OPE.RateLE atTop t (fun i=> mag C.path.levels b (X.atK i)) 0:=by
      intro r hr
      filter_upwards [X.onLevel, (hp.comp X.admits).eventually (Vac.Numbers.cost b r hr)] with k ⟨hk,_⟩ he
      change mag C.path.levels b (X.atK k) ≤ P (X.atK k) ^ r at he
      dsimp only [t]; rw [Real.norm_of_nonneg (Station.mag_pos ..).le, mul_comm r, ← Real.rpow_def_of_pos (zero_lt_one.trans ((A).fits.delayed k))]
      exact he.trans (Real.rpow_le_rpow (zero_le_one.trans ((A).fits.delayed (X.atK k)).le) (WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos hG).le hk) hr.le)
   have hm : OPE.RateLE atTop t (fun i => (A).clock.monitor (X.atK i)) 0 := (hh 1).congr (Eventually.of_forall fun i => Real.rpow_one _)
   have he : OPE.RateLE atTop t m 0 := by simpa only [zero_add] using (OPE.RateLE.const (2:ℝ) hr).mul hm
   let u (i : ℕ) (k :(C.labels.level d).Index) := (m i)^((C.labels.level d).grades k).2 * ((mag C.path.levels X.aperture (X.atK i))^((C.labels.level d).grades k).1)
   have ha i : OPE.RateLE atTop t (fun k=>u k i) 0 := by
     simpa only [mul_zero,zero_add] using! ((he.pow _ hr).mul ((hh X.aperture).pow ((C.labels.level d).grades i).1 hr) : OPE.RateLE _ _ (fun k=>u k i) (↑((C.labels.level d).grades i).2*(0:ℝ)+↑((C.labels.level d).grades i).1*0)) -- maybe
   have hx:= (OPE.RateLE.sum (f:=fun i k=>‖u k i‖) (S:=Finset.univ) hr (fun k _=>(ha k).norm))
   simpa only [zero_add] using! (OPE.RateLE.const (2:ℝ) hr).mul hx

omit T in
lemma energy_cap (d : ℕ) : ∀ᶠ i in atTop, ‖OPE.Levy.preExpense C d (X.atK i) X.aperture‖ ≤ P i ^ (1:ℕ) := by
   refine (X.energy_clock hG d 1 zero_lt_one).mono fun i hi=>?_ -- lemma/dot issue
   rw [one_mul, Real.exp_log (zero_lt_one.trans ((A).fits.delayed i))] at hi
   simpa only [pow_one] using hi

-- retained adapter
omit T in
lemma energy (d : ℕ) : OPE.Wallet atTop P (fun k => OPE.Levy.preExpense C d (X.atK k) X.aperture) :=
   ⟨_, energy_cap X hG d⟩

-- crossing used before zoomPrice; sharp local geometric price
omit T in
lemma length_power : ∀ᶠ k in atTop, a k ≤ X.radius k ∧ X.radius k ≤ a k*P k^2 := by
   filter_upwards [X.onLevel, (hp.comp X.admits).eventually (Vac.Numbers.cost X.aperture 1 zero_lt_one), X.resqueeze]
     with k ⟨hk,_⟩ he hw
   let b := X.atK k
   have hu : mag (A) X.aperture b ≤ P b ^ (1:ℝ):=he
   let v := mag (A) X.aperture b
   have hv : 1 ≤ v := Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) X.apertures.le
   have hP : 0 < P k := zero_lt_one.trans ((A).fits.delayed k)
   have hx : v ≤ P k := (hu.trans_eq (Real.rpow_one (P b))).trans (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos hG).le hk)
   have hf := C.S.a_pos k
   refine ⟨(C.S.strictAnti.antitone hk).trans (le_mul_of_one_le_right (C.S.a_pos b|>.le) hv),?_⟩
   change a b * v ≤ a k * (P k)^2
   exact (mul_le_mul ((div_le_iff₀ hf).mp hw) hx (mag_pos ..|>.le) (by positivity)).trans_eq (by ring)
where hp := Station.hat_rate (A) hG
lemma zoom_price (d : Fin (D+1)) : ∀ᶠ k in atTop, ∀ N p : ℕ, k < N → ∀ x,
    quota C d k N p (microscope C X.aperture (X.atK k) (X.matrix k) d (N,p) x) ≤ P k ^ (1+(d.val+1)) * a k ^ d.val * ‖x‖ := by
   let e : ℕ := 1
   have hc := energy_cap X hG d
   filter_upwards [hc,X.onLevel,X.resqueeze] with k hc ⟨hk,_,hY,hZ⟩ he N p hN x
   let b := g! k
   let m := OPE.Levy.preExpense C d b X.aperture
   have hp' := zero_lt_one.trans ((A).fits.delayed k); have ha':= C.S.a_pos k;have hb' := C.S.a_pos b
   have hf := OPE.Levy.quotation C (b:=X.aperture) (p:=p) d b H (hY.early _ (Nat.le_of_lt_succ d.isLt)) (le_trans hk hN.le) (X.matrix k N p d) (hY.charts _ _ (hk.trans_lt hN) _).1 x
   apply le_trans (reverseWalk (H:=H) T _ (hY.early _ (Nat.le_of_lt_succ d.isLt)) hk hN.le)
   have he : a b / a k ≤ P k:=he; let y:=microscope C X.aperture b (X.matrix k) d (N,p) x
   calc
      _ ≤ P k * _ := mul_le_mul he (le_refl (quota C d b N p y)) (quota_nonneg _) hp'.le
      _ ≤ P k * (a b ^ d.val * m * ‖x‖) := mul_le_mul_of_nonneg_left hf hp'.le
      _ ≤ P k * ((P k * a k)^d.val * (P k ^ e) * ‖x‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hc) (pow_pos hb' d.val).le) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb'.le ((div_le_iff₀ ha').mp he) _) (pow_pos hp' e).le)) (norm_nonneg _)) hp'.le
      _ = _ := by rw [pow_add,pow_succ,mul_pow];ring
lemma zoomPrice (d : Fin (D+1)) : ∃ e : ℕ, ∀ᶠ k in atTop, ∀ N p : ℕ, k < N → ∀ x,
    quota C d k N p (microscope C X.aperture (X.atK k) (X.matrix k) d (N,p) x) ≤ P k ^ e * a k ^ d.val * ‖x‖ := ⟨_, zoom_price X T hG d⟩
end microscopeB
end YM.SharpGram.Weak.Portfolio
