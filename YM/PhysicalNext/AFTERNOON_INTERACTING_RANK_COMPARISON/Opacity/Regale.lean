import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.PairTokens
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Campus
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Stamen
/-!
# Purchase tree exponents in exponent (retimed window)

Deals after chosen B inbound expenditure. Real point pricing through weakened
retimed band. Charges in EXPORT panel, supports in all landmarks at same S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Aff Cab Coverage Calls Win Bid Jewels Exterior
    Next.Rank Value Next.Rank.Perch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {c f n : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W d t a C Y θ : ℝ} {B : ℕ} {p q : Pilot G S x} {v : Dyed G S}
lemma Petty.walk {Z : ℕ} {F : Pilot G S x→ℝ} (h : Petty v W B a t F) (he : 0≤a) (hr : B≤Z): Petty v W Z a t F:= by
  obtain ⟨u,g,hq,hA,hH,hR⟩:= h; exact ⟨u,g,hq,Grid.coverPays hA hH hr he,hH,hR⟩
lemma slack (C : ℝ) {a b : ℝ} (h : a<b): ∀ᶠ x:ℝ in atTop,C*x^a ≤ x^b:= by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop C, eventually_gt_atTop (0:ℝ)] with x hx ht
  exact (mul_le_mul_of_nonneg_right (show C ≤ x^(b-a) from hx) (Real.rpow_pos_of_pos ht a).le).trans_eq (by rw [← Real.rpow_add ht,sub_add_cancel])
namespace Ancestor
private lemma altitude (G : Gauge) (D : Patch) (C : ℝ) (hc : 0≤C): ∀ᶠ x in atTop,∀ (p:BudgetPoint) β (L : ℝ), p.threshold ≤ 2*fiery G x D.L → 0≤ β → β≤4*x → 0≤ L → L ≤ betaF G x D.L^(1/8:ℝ) →
    let z:= amend G D x (1/8); let w:=Aff.weight
    |w| *p.threshold^2*L ≤ z ∧ |β*w| *p.threshold^3*C≤z ∧ |β*w| *p.threshold^4*C≤z := by
  let E : Tempo:=⟨1/4,by norm_num,by norm_num⟩
  filter_upwards [Cab.amend_b G D C hc E,Jewels.instills G D 16 _ _ 0 (by norm_num) (by norm_num : (1/8:ℝ)<1/4),eventually_gt_atTop (0:ℝ)] with x hp hv hx p β L ht he hh hL hs
  intro z w; rw [pow_zero,mul_one] at hv
  let s:= betaF G x D.L; let u:=amend G D x (1/4); let m:= p.threshold; let q:=fiery G x D.L
  have hk : x≤ s:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hA : 0<s:=hx.trans_le hk
  obtain ⟨hx,hy,h⟩:=hp (4*s) L (⟨by linarith only [show 0<betaF G x D.L from hA],le_rfl⟩: Wages.OnBand ..) hs
  have hu : 0≤u:= (pos_ac G D x _ hA).le
  have hH : |β*w|≤ |4*s*w|:= by rw [abs_mul, abs_mul (4*s),abs_of_nonneg he,abs_of_nonneg (by positivity:0≤4*s)]; exact mul_le_mul_of_nonneg_right (by linarith only [hh,hk]) (abs_nonneg _)
  have hm :0 ≤ m:=p.threshold_pos.le
  have he (n : ℕ) (r r' M : ℝ) (hr : 0≤r) (h : r≤ r') (hR : 0≤M) : r*m^n*M ≤ 2^n*(r'*q^n*M):= by
    have h₁ : r*m^n ≤ r'*(2*q)^n:=mul_le_mul h (pow_le_pow_left₀ hm ht n) (pow_nonneg hm n) (hr.trans h)
    apply (mul_le_mul_of_nonneg_right h₁ hR).trans_eq; rw [mul_pow]; ring
  refine ⟨(he 2 |w| |w| L (abs_nonneg _) le_rfl hL).trans ?_,(he 3 |β*w| |4*s*w| C (abs_nonneg _) hH hc).trans ?_,(he 4 |β*w| |4*s*w| C (abs_nonneg _) hH hc).trans ?_⟩
  change |w| *q^2*L ≤ u at hx
  exact (mul_le_mul_of_nonneg_left hx (by norm_num:(0:ℝ)≤2^2)).trans ((mul_le_mul_of_nonneg_right (by norm_num:(2:ℝ)^2≤16) hu).trans hv)
  change |4*s*w| *q^3*C≤u at hy; exact (mul_le_mul_of_nonneg_left hy (by norm_num:(0:ℝ)≤2^3)).trans ((mul_le_mul_of_nonneg_right (by norm_num:(2:ℝ)^3≤16) hu).trans hv)
  change |4*s*w| *q^4*C≤u at h; exact (mul_le_mul_of_nonneg_left h (by norm_num:(0:ℝ)≤2^4)).trans ((mul_le_mul_of_nonneg_right (by norm_num:(2:ℝ)^4≤16) hu).trans hv)
open Footprint
private lemma cache (L : Side) {a ε : ℝ} (he : 0< ε): ∀ᶠ x:ℝ in atTop,∀ (d : ℝ) (B : ℕ), d≤x^(-(1/2):ℝ) → B ≤ walls x → Footprint.payment (L.val^4) (extentCost 1 B) 0 ε 1 d a (preCost 1) ≤ x^(-(1/8):ℝ) := by
  let f:= Footprint.payment (L.val^4) 0 0 ε 1 1 a (preCost 1)
  have hf : 0≤f:= by
    have hM :0 ≤ 1-Real.exp (-ε):= sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.le)); unfold f Footprint.payment degreeIncome; positivity
  filter_upwards [Grid.grows_size 8 (f*43^4) (by positivity) (3/8) (by norm_num),Work.E01.radiusB_tendsto.eventually_ge_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx ht hp d B h hy
  let w:ℕ:= extentCost 1 B; let p:ℕ:=walls x; let z:= x^(-(1/2):ℝ); let F:ℝ:= radiusB x
  rw [show Footprint.payment (L.val^4) (extentCost 1 B) 0 ε 1 d a (preCost 1) = f*↑(Animals.ballCost w)*d from by unfold f Footprint.payment degreeIncome Footprint.spread Animals.ballCost w; push_cast; ring]
  have hg : (Animals.ballCost w:ℝ) ≤ (43*F^2)^4:= by
    have ht : 1 ≤ p:= one_le_pow₀ ht -- nat finances
    have hh : Animals.ballCost w ≤ (43*p)^4:= by apply Nat.pow_le_pow_left (show w+w+1 ≤ 43*p from by unfold w extentCost; change B≤p at hy; omega)
    apply (Nat.cast_le.mpr hh).trans_eq; unfold p walls; push_cast; rfl
  have h' : f*(43*F^2)^4 ≤ x^(3/8:ℝ):= le_trans (le_of_eq (show _=f*43^4*F^8 by ring)) hx
  have hA := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hg hf).trans h') (Real.rpow_pos_of_pos hp (-(1/2):ℝ)).le
  exact (mul_le_mul_of_nonneg_left h (mul_nonneg hf (Nat.cast_nonneg _))).trans (hA.trans_eq (by rw [← Real.rpow_add hp]; norm_num))

lemma abound (P : Teller G) (D : Patch) (a t : ℝ) (ha : 0≤a) (ht : 0<t): ∀ᶠ x in atTop,
    ∀ (c f : Side) (S : StepData c f) (v:Dyed G S) (W C : ℝ), S.patch=D →Chips v P W x → LaneCounts v.source.path x v.source.p.threshold v.source.clip C 1 S.ratio.parent →
    v.bp.B ≤ Perch.walls x → Footprint.reserve v.source.p.supportExponent a (Footprint.conversion S.ratio 1) t → v.source.p.B≤2*v.bp.B → 25*radiusB x+30≤ v.bp.B →
    v.source.beta≤ 4*x → v.source.p.threshold ≤ 2*fiery G x S.patch.L → ∀ Γ δ w, v.source.Lawful P.top.width P.top.paths Γ δ w →
      Γ ≤ betaF G x D.L^(1/8:ℝ) → δ ≤ x^(-(1/2):ℝ) → Petty v W v.bp.B a (x^(-(1/24):ℝ)) (terra v (x:=x)):= by
  let k:ℝ:=Fintype.card Signed; let l:ℝ:=Fintype.card PlaqAxes; have hk:0≤k:=Nat.cast_nonneg _; have hl:0≤l:=Nat.cast_nonneg _
  have hf n:= universes G D n a P.top.width ha P.top.width_pos
  filter_upwards [altitude G D P.top.paths P.top.paths_pos.le,hf 2,hf 3,hf 4,credits P D a ha,cache D.L (a:=a) ht,slack (1+2*k*l+3*k) (by norm_num : (-(1/12):ℝ)< -(1/24)), eventually_ge_atTop (1:ℝ)] with x hx hh hw hf hc ht he h₁ c f S v W C hD hT hV hB hY hi hm hq hQ Γ δ w hR hΓ hδ
  subst D
  let r:=v.source; let n:=x^(-(1/12):ℝ); let b:=x^(-(1/8):ℝ); let K:=amend G S.patch x 1; let o:=amend G S.patch x (1/12)
  have hg:0≤Γ:= budget_nonneg hR.paths.two
  obtain ⟨hz,hy,h⟩:=hx v.source.p v.source.beta Γ hQ hT.beta.le hq hg hΓ
  have H:radiusB x≤v.bp.B:=by omega
  obtain ⟨hu,hr⟩:=hc c f S v W C rfl hT hq hV
  have hp := (hh S v W P rfl hT r.path.loop _ Γ hR.paths.two hz).plus (((hw S v W P rfl hT r.path.cubic _ P.top.paths hR.paths.three hy)).plus (hf S v W P rfl hT r.path.quartic _ P.top.paths hR.paths.four h))
  apply (((pre hT hm hR.labels.boundE hY hi).across (ht δ v.bp.B hδ hB)).plus ((hu.plus hr).walk ha H) |>.plus (hp.walk ha H)).traded (fun p _ _=> patrons v p) |>.across
  have hb:x≤ betaF G x S.patch.L:=le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hx : 0<x:=zero_lt_one.trans_le h₁
  have hK:K ≤ n:= (Real.rpow_le_rpow_of_nonpos hx hb (by norm_num : -(1:ℝ) ≤0)).trans (Real.rpow_le_rpow_of_exponent_le h₁ (by norm_num))
  have h':o ≤ n:= Real.rpow_le_rpow_of_nonpos hx hb (by norm_num : -(1/12:ℝ) ≤0)
  have hf:k* (l*K) ≤ k*(l*n):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hl) hk
  change b+(k*(l*K)+k*(l*K))+(k*o+(k*o+k*o)) ≤ _
  refine le_trans ?_ (show (1+2*k*l+3*k)*n ≤ _ from he)
  linarith only [hf,mul_le_mul_of_nonneg_left h' hk, (show b≤n from Real.rpow_le_rpow_of_exponent_le h₁ (by norm_num))]
end Ancestor
end YM.PhysicalNext.InteractingRank.Pump
