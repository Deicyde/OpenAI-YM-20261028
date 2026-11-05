import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Infinitesimal
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada
import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
/- books based on actual μ,d; slot scale-W post; not Θ petition. -/

def grow (G : Gauge) (L : Side) (s : ℝ) := betaF G s L ^ (3/8:ℝ)
def asset (T' : ConnectedActivityE6.Target.Expense Q) := (Q.exp - T'.earn)/2

lemma asset_pos (T' : ConnectedActivityE6.Target.Expense Q) : 0<asset T' := by unfold asset; linarith [T'.worth,T'.first,T'.second]

lemma pressureYoung (G : Gauge) (L : Side) {r i : ℝ} {B : ℝ→ℝ} (h : ConnectedActivityE6.Rate G L r B) (hr : 3/8+r<0) : ∀ᶠ s in atTop,
    degreePrice (radiusB s) (grow G L s*B s) i ≤ 1/2 := by
  have he := Census.width_rate G L 1 0; simp only [one_mul,add_zero] at he
  have hx := he.mul ((Rate.power (G:=G) (L:=L) (a:=3/8)).mul h)
  have hS : Rate G L (0+(3/8+r)) (fun x=> degreePrice (radiusB x) (grow G L x*B x) i) := by unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; exact ((hx.mul_right i⁻¹).mul_left 4)
  exact (hS.below (by linarith only [hr]) (1/2) (by norm_num)).mono fun s hs=> (le_abs_self (degreePrice ..)).trans hs
lemma probed (Q : YM.ConnectedActivityE6.Target G P) (L : Side) {μ : ℝ} (hm : 0<μ) : ∀ᶠ x in atTop,
    grow G L x ^ 3 ≤ Real.exp (Q.mark L μ x) := by
  let d x:= grow G L x; let g x:= Q.mark L μ x
  have hf : Rate G L (-2) (fun x=> Real.exp (-g x)) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x
    dsimp only; rw [Real.rpow_two]; unfold g; change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  have hx := (Rate.power (G:=G) (L:=L) (a:=3/8)).pow 3|>.mul hf
  filter_upwards [hx.below (by norm_num) 1 zero_lt_one] with x h
  suffices hs : d x^3/Real.exp (g x) ≤ 1 from (div_le_one (Real.exp_pos _)).1 hs
  rw [div_eq_mul_inv, ← Real.exp_neg]; exact (le_abs_self _).trans h

lemma highPay (G : Gauge) (L : Side) {φ β : ℝ} (hv : φ < -(3/8:ℝ)) {D : ℝ → ℝ} (hD : Rate G L 0 D) (hp : 0 < β) : ∀ᶠ x in atTop,
    (grow G L x ^ 3)⁻¹ * D x * (grow G L x * (betaF G x L^φ)) ≤ β * δE x := by
  let f:= grow G L
  have he := Rate.power (G:=G) (L:=L) (a:=3/8)
  have hs: Rate G L (-(9/8)) (fun x=> (f x^3)⁻¹) := by
    apply Rate.congr Rate.power
    filter_upwards [Delay.shift_pos G L] with x hx
    unfold f grow; rw [show (9/8:ℝ)=3/8*3 by norm_num, Real.rpow_neg hx.le, Real.rpow_mul hx.le]; norm_num
  have hy := ((hs.mul hD).mul (he.mul (Rate.power (a:=φ))))
  have hr := (hy.mul (Rate.power (G:=G) (L:=L) (a:=11/10)))
  filter_upwards [hr.below (by linarith only [hv]) _ hp,eventually_gt_atTop (0:ℝ),Delay.shift_pos G L] with x hx hw ha
  let z:=betaF G x L
  have hi : δE z=z^(-(11/10):ℝ) := by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg ha.le,← Real.rpow_mul ha.le]; norm_num; rfl
  let F:ℝ:= (f x ^ 3)⁻¹ * D x * (f x * z ^ φ)
  have he:F ≤ β*δE z := by rw [hi,Real.rpow_neg ha.le,← div_eq_mul_inv]; exact (le_div_iff₀ (show 0 < z^(11/10:ℝ) by positivity)).mpr ((le_abs_self _).trans hx)
  apply he.trans (mul_le_mul_of_nonneg_left _ hp.le)
  unfold δE; refine Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num)
  have hm : x ≤ z := le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)
  exact inv_anti₀ (Real.sqrt_pos.mpr hw) (Real.sqrt_le_sqrt hm)

-- allow arbitrary provided Armada reserve: monotone substitute
variable (Q)
lemma cruising (T' : ConnectedActivityE6.Target.Expense Q) (L : Side) {μ : ℝ} (hm : 0 < μ) (j n : ℕ)
    (he : T'.wanting < -(3/8:ℝ)) (β : ℝ) (hβ : 0<β) : ∀ᶠ s : ℝ in atTop,
      let D:=grow G L s
      1≤D ∧ D^3 ≤ Real.exp (Q.mark L μ s) ∧ degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2 ∧
      ∀ (A i' : ℝ) (k : ℕ), Armada Q L μ T'.earn s i' A j k → 0 ≤ A →
        collars G i' s j n*(salary Q L μ A s j k*(1-1/2)⁻¹) ≤ betaF G s L^T'.wanting →
        let y:= asset T'
        Armada Q L μ T'.earn s y A j k ∧ degreePrice (radiusB s) (D*salary Q L μ A s j k) y ≤ 1/2 ∧
          (D^3)⁻¹*collars G y s j n*(D*salary Q L μ A s j k*(1-1/2)⁻¹) ≤ β* δE s := by
  let y:= asset T'
  have hy:0<y:=asset_pos T'
  let c := y⁻¹^(n*j)* (n*j).factorial
  have hc:0<c:=by unfold c; positivity
  let f s:=c⁻¹*betaF G s L ^ T'.wanting
  have hp := pressureYoung G L (i:=y) (Rate.power (G:=G) (L:=L) (a:=T'.wanting)|>.mul_left c⁻¹) (by linarith only [he]);
  have hK := highPay (D:=fun x=> Real.exp y) G L he (Rate.const _) hβ
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,probed Q L hm,pressureYoung G L (i:=Q.δ) (Q.rate_root L hm (β:=1) (C:=0)) (by linarith only [he,T'.reach]),hp,hK]
    with s hs hT hz ht hR D
  have hD:1≤D:=Real.one_le_rpow hs (by norm_num)
  have hr:0<D:=zero_lt_one.trans_le hD
  refine ⟨hD,hT,hz,?_⟩
  intro B i k hA ha H y
  let Y:=asset T'; let a:=salary Q L μ B s j k
  have he':0<a:=by unfold a salary; have hv:=hA.earned; positivity
  have hL:0 < i:=hA.delta
  have hg : i≤Y:=by have hz:=hA.little; unfold Y asset; linarith
  let r:=i⁻¹^(n*j)*((n*j).factorial:ℝ)
  have hu:c ≤ r := by unfold c r; gcongr
  have hvol : c ≤ collars G i s j n := by
    have hK':1 ≤ shiftG s:= by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB s)]
    apply hu.trans
    exact (le_mul_of_one_le_right (hc.le.trans hu) (Real.one_le_exp hL.le)).trans
      (le_mul_of_one_le_left (show 0≤ r * Real.exp i by positivity) (one_le_pow₀ hK'))
  have hE : a≤ f s := by
    unfold f; rw [mul_comm,← div_eq_mul_inv]
    apply (le_div_iff₀ hc).mpr; apply le_trans _ H
    norm_num; change a*c ≤ collars G i s j n*(a*2); nlinarith only [hvol,he',hc]
  have hU : degreePrice (radiusB s) (D*a) Y ≤ 1/2 := by
    refine le_trans ?_ ht; unfold degreePrice Trees.stretch; change _ ≤ 4*((_*(D*f s)) / Y); gcongr
  refine ⟨⟨hA.gain,hy,by unfold y asset; linarith,hA.earned,?_⟩,hU,le_trans ?_ hR⟩
  · apply le_trans _ hU; change degreePrice _ a _≤_; unfold degreePrice Trees.stretch; gcongr; exact le_mul_of_one_le_left he'.le hD
  have hW : collars G Y s j n ≤ Real.exp Y * collars G i s j n := by
    unfold collars Reserves.polyPrice
    have hS:0 ≤ shiftG s ^(n*j):=pow_nonneg (by unfold shiftG; positivity) _
    change _*(c*_ ) ≤ _*(_*(r*_))
    rw [mul_left_comm (Real.exp Y) (shiftG s^(n*j))]; apply mul_le_mul_of_nonneg_left _ hS; rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hu.trans (le_mul_of_one_le_right (hc.le.trans hu) (Real.one_le_exp hL.le))) (Real.exp_pos _).le
  change (D^3)⁻¹*_* (D*a*_ ) ≤ _
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) (by positivity : 0≤ D*a*(1-1/2)⁻¹)).trans
  calc _ = ((D^3)⁻¹*Real.exp Y)*(D*(collars G i s j n*(a*(1-1/2)⁻¹))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left H hr.le) (by positivity : 0 ≤ (D^3)⁻¹ * Real.exp Y)
end YM.PhysicalNext.Repeat.Height
