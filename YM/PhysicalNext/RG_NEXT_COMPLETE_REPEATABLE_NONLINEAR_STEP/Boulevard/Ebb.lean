import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Oro
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
import YM.Planned.STATIONARY_JET_PORT.Tariff
/-!
 # Boundary traces. Any SMALL chart V: radial immediately strict.
 Uses norm increments estimate not smoothness of chord. Eventually of
 the purchased VACTOR, any actual factor if order/template fixed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond  Fare Lapis Metric Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X t : ℝ} {f : Config G c→ℝ}
section gap
local notation "W" => (𝓝[<] (1:ℝ))
lemma retreats {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : ℝ→E} {t:ℝ} (h : ∀ i∈ Set.Icc (0:ℝ) 1, Brush 2 T p X i) (hp:‖X 1-X 0‖≤t) (hz: T*p^2<t): ∀ᶠ x in W, ‖X x-X 0‖<t:= by
  have h0:= h 1 ⟨zero_le_one,le_rfl⟩; have hc : ContinuousAt (fun x=>‖X x-X 0‖) 1:= (h0.smooth.continuousAt.sub continuousAt_const).norm
  obtain hP|hP:= lt_or_eq_of_le hp; · exact hc.continuousWithinAt (gt_mem_nhds hP)
  let D:=X 1-X 0; let K:=T*p^2; let Z (t:ℝ):= fderiv ℝ X t; let g (x:ℝ):= X x-x • D; let f x:= X x-Z 1 x
  have hv i (hi:i∈ Set.Icc (0:ℝ) 1): DifferentiableAt ℝ X i := (h i hi).smooth.differentiableAt (by norm_num)
  have hE : ‖D-Z 1 1‖≤ K := by
    have he i (hi:i∈Set.Icc (0:ℝ) 1) : HasFDerivAt f (Z i-Z 1) i := ((hv i hi).hasFDerivAt).sub ((Z 1).hasFDerivAt)
    have hD i (hi:i∈Set.Icc (0:ℝ) 1) : ‖Z i-Z 1‖ ≤ K := by
      have hc i (hi:i∈Set.Icc (0:ℝ) 1): ContDiffAt ℝ 1 Z i:= (h i hi).smooth.fderiv_right (by norm_num)
      have hj i (hi:i∈Set.Icc (0:ℝ) 1): ‖fderiv ℝ Z i‖ ≤ K:= by
        rw [← norm_iteratedFDeriv_one]; exact (norm_iteratedFDeriv_fderiv).symm.symm.trans_le ((h i hi).order 2 le_rfl)
      have hb:= (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (hc i hi).differentiableAt (by norm_num)) hj (show (1:ℝ)∈Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩) hi
      have hV : ‖i-1‖ ≤ 1:= by rw [Real.norm_of_nonpos (sub_nonpos.mpr hi.2)]; linarith only [hi.1]
      exact hb.trans (mul_le_of_le_one_right (mul_nonneg h0.nonneg (sq_nonneg _)) hV)
    have ht := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_fderiv_le (fun i hi=>(he i hi).differentiableAt) (fun i hi=> (he i hi).fderiv.symm ▸ hD i hi) (show (0:ℝ)∈ Set.Icc 0 1 from ⟨le_rfl,zero_le_one⟩) (show (1:ℝ)∈Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
    simp only [f,map_zero,sub_zero,norm_one,mul_one] at ht; rwa [sub_right_comm] at ht
  have hg : HasDerivAt g (Z 1 1 - D) 1:= by
    convert ((hv 1 ⟨zero_le_one,le_rfl⟩).hasFDerivAt.hasDerivAt.sub (((hasDerivAt_id' (1:ℝ)).smul_const D))) using 1; · rfl
    rw [one_smul]
  have he : ‖Z 1 1-D‖ < t := by rw [norm_sub_rev]; exact hE.trans_lt hz
  filter_upwards [(hasDerivAt_iff_tendsto_slope_left_right.mp hg).1.norm (gt_mem_nhds he), (show ∀ᶠ x:ℝ in W, 0≤x from Eventually.filter_mono nhdsWithin_le_nhds (eventually_ge_nhds zero_lt_one)), self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Set.Iio 1)] with x hx hX hm
  have hs:= sub_neg.mpr (show x<1 from hm); have hK:= mul_lt_mul_of_pos_left (show ‖slope g 1 x‖<t from hx) (show 0<1-x from sub_pos.mpr hm)
  unfold slope at hK; rw [vsub_eq_sub,norm_smul,norm_inv,Real.norm_of_nonpos hs.le, neg_sub, ← mul_assoc,mul_inv_cancel₀ (by linarith), one_mul] at hK
  have hf : X x-X 0=x • D+(g x-g 1):= by unfold D g; simp only [D,one_smul]; abel
  change ‖D‖=t at hP
  rw [hf]; refine lt_of_le_of_lt (norm_add_le ..) ?_; rw [norm_smul,Real.norm_of_nonneg hX,hP]; linarith only [hK]

lemma parsimony (t:ℝ) (V:Positions (Uniform.Primary c G)) : ∀ i: Pressure.Bond c, actual (t • V) i=G.lieExp (t • Uniform.tint G _ V (pole i)) := fun i=> by rw [actual,Work.F03.represent_link, map_smul]; rfl
lemma radiator (t:ℝ) (V:Positions (Uniform.Primary c G)) (i:Pressure.Bond c): ContDiffAt ℝ ω (fun y:ℝ=>G.mat (actual (y • V) i)) t:= by simp_rw [parsimony]; exact (G.exp_jet.comp (contDiff_id.smul contDiff_const)).contDiffAt
-- σ enough for each link Lie. may choose J pre-parameters
variable (J w : ℝ) (hJ : ∀ v:G.Color, ‖v‖≤1→Brush 2 J 1 (fun a=> G.mat (G.lieExp a)) v)
    (V:Positions (Uniform.Primary c G)) (hw: Uniform.shade G * ‖V‖ ≤ w) (hV:w≤1)
def sunLength (J w:ℝ) := (1+Nat.factorial 2*J)*((1+1)*w)
include hJ hw hV
lemma apt (x:ℝ) (hx:x∈Set.Icc (0:ℝ) 1): Mode (fun y:ℝ=> actual (y • V)) x 2 (Boulevard.sunLength J w) := by
  have hw':0 ≤ w:= (mul_nonneg (Uniform.shade_pos G).le (norm_nonneg _)).trans hw; have h':0≤J:=(hJ 0 (by simp)).nonneg
  refine ⟨by unfold sunLength; positivity, fun i=>?_⟩
  let u:= tint G _ V (pole i); let s:ℝ→L[ℝ] G.Color := (ContinuousLinearMap.id ℝ ℝ).smulRight u; have he : ‖u‖ ≤ w:= (norm_le_pi_norm (tint G _ V) _).trans ((Uniform.tint_le V).trans hw)
  have hp : ‖s x‖≤1:= by change ‖x • u‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hx.1]; exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans (he.trans hV)
  have hp' : Brush 2 1 w s x:= Brush.linearB s hp (by
    rw [one_mul]; apply ContinuousLinearMap.opNorm_le_bound s hw'; intro z; change ‖z • u‖≤_; rw [norm_smul, mul_comm w]; exact mul_le_mul_of_nonneg_left he (norm_nonneg _)) hw'
  simp_rw [parsimony]; exact Blaze.thicken (f:=fun z=> G.lieExp (s z)) (hp'.pine (hJ _ hp))
set_option maxHeartbeats 500000 in
lemma sunnySoon (hF: flags P.threshold (actual V)=∅)
    (hp: royalty G*(4*((sunLength J w)*royalty G))^2 < P.threshold *royalty G):
    ∀ᶠ x in (𝓝[<] (1:ℝ)), actual (x • V) ∈ sunny P:= by
  apply eventually_all.mpr; intro i
  let f (x:ℝ):= G.mat (faceValue (actual (x • V)) i)
  let r:=royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge _)
  have he : f 0=1:=by simp [f,actual,faceValue,travel,square,posDir,negDir, Lattice.Step.read]
  have hv k: G.chord (faceValue (actual (k • V)) i)=‖f k-f 0‖/r:= by rw [he]; rfl
  have hz x (hx:x∈ Set.Icc (0:ℝ) 1): Brush 2 r (4*((sunLength J w)*r)) f x:= by
    have hf:= apt J w hJ V hw hV _ hx; convert tour (U:=fun x:ℝ=> actual (x • V)) (square i.2.val.1 i.2.val.2) i.1 hf.pos hf.atLink using 1; rw [show (square i.2.val.1 i.2.val.2).length=4 from rfl]; norm_num [r]
    rfl
  have hh: G.chord (faceValue (actual ((1:ℝ) • V)) i)≤ P.threshold:=by rw [one_smul]; exact Pane.lucid P _ hF _
  have hv':= retreats hz ((div_le_iff₀ hr).1 ((hv 1).symm.trans_le hh)) hp
  exact hv'.mono fun i hi=> (hv i).trans_lt ((div_lt_iff₀ hr).2 hi)
end gap
end YM.PhysicalNext.Repeat.Boulevard
