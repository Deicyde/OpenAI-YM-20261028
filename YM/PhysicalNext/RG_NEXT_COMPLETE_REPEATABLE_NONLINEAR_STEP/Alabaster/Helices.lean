import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Beet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Thatch
/-!
# Uniform fixed-volume Gaussian moments payoff on F and variation in FULL.
 No growth bound outside f,c.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {O : ChartRatio G} {A : Matrix (Tubular f G) (Tubular f G) ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f} {E : Type} {j Z m : ℕ} {M B B' K' η r t p c' : ℝ}
local notation "Y" => Air f G
local notation "φ" => facescale (univ : Finset (Bond f))
local notation "L'" => low R I
section odds
variable (X : Coat T F) (h : Rotator P L η r M B X)
local notation "S'" => X.relating
lemma entire : lensS (univ:Finset (Bond f)) G= univ:= by ext; simp [lensS]
lemma lo_phi (I : Finset (Bond f)) (z:Y): facescale I z≤φ z:= by
  unfold facescale; simp only [entire]; apply add_le_add
  · gcongr <;>  exact Finset.subset_univ _
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> abs_nonneg _)
include h X
lemma ups : Allow S' (along S) (tubularPrice G L) (retain η r M) (M⁻¹/2) (1+payE η r M (tubularPrice G L)):= by
  have hf:=h.scale; exact ⟨hf.census,Window.twin ..,hf.weather.1,half_pos (inv_pos.mpr hf.fuel),add_pos_of_pos_of_nonneg zero_lt_one hf.disc,(Control.increase (hf.mate X.shutter) le_rfl (le_add_of_nonneg_left zero_le_one)).1, hf.ground_C X.shutter h.cap⟩
variable {X h}
def warpK (G : Gauge) (L : Side) (η r M : ℝ) := payE (retain η r M) (M⁻¹/2) (1+payE η r M (tubularPrice G L)) (tubularPrice G L)
def lunar (G : Gauge) (f L : Side) (η r M : ℝ):= let m:= (Fintype.card (Tubular f G):ℝ); (m*(2+warpK G L η r M)*m)
variable (X h)
-- sphere growth energy
lemma rhapsodic (z:Y) : |dotProduct z.ofLp (S'⁻¹ *ᵥ z.ofLp)| ≤ lunar G f L η r M*(φ z)^2 := by
  let K:=warpK G L η r M; have hk : 0 ≤ K:=(ups X h).disc
  let M':=Fintype.card (Tubular f G); let p:=φ z
  have hh i j : |S'⁻¹ i j| ≤ K:= only_price (ups X h).flatup.1 (ups X h).weather.1.le i j
  have hz i : |z.ofLp i|≤p:= (Flux.expenses (Finset.univ: Finset (Bond f)) z).2.2.2 i ((by rw [entire]; exact mem_univ _))
  have hv: 1 ≤ p:= (Flux.expenses _ _).1
  unfold dotProduct Matrix.mulVec; simp_rw [dotProduct,mul_sum]; apply le_trans (Finset.abs_sum_le_sum_abs ..); apply le_trans (Finset.sum_le_sum (fun _ _=>Finset.abs_sum_le_sum_abs ..))
  apply le_trans (Finset.sum_le_sum (fun _ _=> Finset.sum_le_sum (fun i _=> by simp_rw [abs_mul]; exact mul_le_mul (hz _) (mul_le_mul (hh _ _) (hz i) (abs_nonneg _) hk) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (zero_le_one.trans hv))))
  simp only [sum_const,nsmul_eq_mul,card_univ]; unfold lunar
  change M'* (M'*(p*(K*p))) ≤ (M'*(2+K)*M')*p^2; nlinarith only [sq_nonneg ((M':ℝ)*p)]

omit X h
def massQ (G : Gauge) (f L : Side) (η r M : ℝ) :ℝ := 2*(Fintype.card (Tubular f G):ℝ)+lunar G f L η r M /2
lemma logC {a ε : ℝ} (h : 0<a) (ht : ε ≤ 1/4) (hg : |a^2-1|≤ε) : 1/2 ≤ a ∧ a≤2 ∧ |Real.log a|≤2*ε:= by
  have hA:= abs_le.mp hg; have ha:1/2≤a:=by nlinarith [hA.1]
  have hb:a≤2:=by nlinarith [hA.2]
  have hv:0≤ ε:=(abs_nonneg _).trans hg
  refine ⟨ha,hb,abs_le.mpr ⟨?_,?_⟩⟩
  · rw [neg_le, ← Real.log_inv]; apply (Real.log_le_sub_one_of_pos (inv_pos.mpr h)).trans
    have hg' : 1-a ≤ ε:= by nlinarith only [hv,hA.1,h]
    suffices hi:a⁻¹ ≤ 2*ε+1 by linarith only [hi]
    apply (inv_le_iff_one_le_mul₀ h).mpr; nlinarith only [hg',mul_le_mul_of_nonneg_left ha hv]
  apply (Real.log_le_sub_one_of_pos h).trans; nlinarith only [sq_nonneg (a-1), hA.2,hv]
include h X
lemma walksWorth {z₀:Y} (ha:0<c') (ht:t≤ 1/4) (hg : |c'^2-1| ≤ t) : ‖Real.log (walk S' c' z₀)‖ ≤ (t*massQ G f L η r M)*(φ z₀)^2 := by
  obtain ⟨ha',hb,hH⟩:= logC ha ht hg; let z:= z₀; let n:=Fintype.card (Tubular f G)
  rw [walk,temper]; simp_rw [mul_comm (lens₀ _ z₀),mul_div_cancel_right₀ _ (fullFuel S' z₀).ne',Real.log_mul (pow_pos ha _|>.ne') (Real.exp_pos _).ne',Real.log_exp, Real.log_pow]
  have hv := rhapsodic X h z₀; let Z:= φ z₀; have hZ:1≤Z:=(Flux.expenses _ z₀).1; have hp:0≤t:=(abs_nonneg _).trans hg
  -- abs euro
  apply (abs_add_le ..).trans; rw [abs_mul,abs_div,abs_mul,abs_sub_comm, Nat.abs_cast,abs_of_pos (by norm_num : 0<(2:ℝ))] -- check
  apply (add_le_add (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)) (div_le_div_of_nonneg_right (mul_le_mul hg hv (abs_nonneg _) hp) (by norm_num))).trans; unfold massQ; nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) hZ) (show 0≤ (n:ℝ)*t from mul_nonneg (Nat.cast_nonneg _) hp)]
end odds
section log
lemma log_peak_A {a : ℝ} (h:0<a): |a-1|≤ |Real.log a| * (a+1) := by
  have he := Real.log_le_sub_one_of_pos h; have hd:= Real.log_le_sub_one_of_pos (inv_pos.mpr h); rw [Real.log_inv] at hd
  rcases le_total 1 a with hp|hp
  · rw [abs_of_nonneg (sub_nonneg.mpr hp),abs_of_nonneg (Real.log_nonneg hp)]; nlinarith only [mul_le_mul_of_nonneg_left hd h.le, mul_inv_cancel₀ h.ne', Real.log_nonneg hp]
  rw [abs_of_nonpos (sub_nonpos.mpr hp),abs_of_nonpos (Real.log_nonpos h.le hp)]; nlinarith only [he,mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos h.le hp) h.le]
end log
end YM.PhysicalNext.Repeat.Alabaster
