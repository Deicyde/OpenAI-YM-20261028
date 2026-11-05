import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Station
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Apertures
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Terms
import YM.Push.COMMON_WITNESSES.Early
import YM.Push.RELAY_MARK.Dollar
import YM.Push.STATIONARY_UNIFORM.Cost
import YM.Push.STRESS_FLUX.Pairing



/-!
# Quantitative stage procurement on every matching Desk

Here and below chart widths and cutoffs used by this step must be fixed PRIOR
to delaying the height. The polynomial bills entering `rebates` are per
*distinct* physical trigger endpoint; take even with arbitrary repeated uses
(only earns once then). Doesn't purport to meet the pre-L cost structure
of a stationary Rack, nor does it set these thresholds retroactively.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Metric Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice
open AnalyticBridge.Sharp AnalyticBridge.AnnulusRatioInsertions.Prism AnalyticBridge.AnnulusRatioInsertions.Parade SectorNext.Remainder
open AnalyticBridge.AnnulusRatioInsertions.Portfolio Push.SectorMeasure Presented Wisps Schur Bid
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

structure Kiosk where
  v : Charges
  cap : ℝ
  outer : ℝ
  L : ℝ
  W : ℝ

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {K : Kiosk} {P : Patch} {Pt : Teller G}
    {Z : ChartRatio G} {q : Chi} {r x θ E : ℝ} {power k n : ℕ}

structure Calling (Pt : Teller G) (Z : ChartRatio G) (q : Chi) (power : ℕ) (r x : ℝ) (d : Desk G S) : Prop where
  place : 100*(1+radiusB x) ≤ c.val
  funds : Pt.Funds S d.tube
  height : x=d.betaHat
  beta : d.input.beta∈ Set.Icc (betaF G x S.patch.L/2) (2*betaF G x S.patch.L)
  radius : d.radius=r*fiery G x S.patch.L
  chart : Z=d.chart
  cut : q=d.broadCut
  powers : power=d.out.power
  threshold : d.out.threshold=temp x

structure Day (K : Kiosk) (θ E : ℝ) (k n : ℕ) (d : Desk G S) : Prop where
  beta : 0<d.input.beta
  radius : 0<d.radius
  larger : Larger (G:=G) S
  limits : Limits K.v S.patch G K.cap d.betaHat
  charts : Studio d.chart (4*d.radius) k K.L K.W
  allows : 4*d.radius < K.outer
  room : Curtain.Ready d.chart d.g K.outer
  capacity (A : Stores S) (F : Forest S.ratio) (l : S.Choices) (V : Config G c) : A.flags=RG.flags (temp d.betaHat) V →
    let u := spectacle d A F l
    Peak (u.C V) K.cap ∧ At K.v u V k
  marked : 0 < θ
  cost_nn : 0 ≤ E
  revenue : 0 < rateTrigger K.cap θ
  rebates (m : ℕ) : let x:=d.betaHat
    Arc.tail K.cap (anxious G S.patch.L x θ d.input.beta) m*tuck G^m*(E*Scales.b x^n)^m ≤
      Real.exp (-rateTrigger K.cap θ * Scales.p G S.patch.L x^2 * m)

private lemma shrink {t t' L W : ℝ} (h : Studio Z t' k L W) (he : t ≤ t') : Studio Z t k L W :=
  ⟨he.trans_lt h.size, he.trans_lt h.patch,fun _ hv => h.frame _ (image_mono (image_mono (closedBall_subset_closedBall he)) hv),
    fun _ hv => h.price _ (closedBall_subset_closedBall he hv)⟩

theorem stage (G : Gauge) (P : Patch) (Pt : Teller G) (Z : ChartRatio G) (q : Chi) (k power : ℕ) (r : ℝ)
    (hr : 0<r) (hZ : LocalRatio Z) (hP : P.Branches Pt.bind G) : ∃ K : Kiosk, ∀ (θ E : ℝ) (n : ℕ), 0<θ → 0 ≤ E →
      ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → ∀ d : Desk G S, Calling Pt Z q power r x d → Day K θ E k n d := by
  let t := min Z.radius (firstRadius G) / 2
  have ht : 0<t := by have := hZ.patch; have := first_pos G; unfold t; positivity
  have ht' : t<firstRadius G := lt_of_lt_of_le (by linarith : t<2*t) (by unfold t; linarith only [min_le_right Z.radius (firstRadius G)])
  have ht'' : t<Z.radius := lt_of_lt_of_le (by linarith : t<2*t) (by unfold t; linarith only [min_le_left Z.radius (firstRadius G)])
  obtain ⟨v,hv⟩ := capital G P Pt hP r hr q k power
  obtain ⟨cap,hcap,hC⟩ := Aperture.open_price Pt P hP
  obtain ⟨L,W,hT⟩ := Studio.make hZ ht' ht'' k
  refine ⟨⟨v,cap,t,L,W⟩,fun θ E n hθ hE => ?_⟩
  filter_upwards [hv,hC,fires G P.L cap θ E n hE hcap hθ, offload v P G hcap,Work.E01.fiery_le G P.L (4*r),
    (Work.E01.largeT_tendsto G P.L).eventually (gt_mem_nhds ht),(Work.E09.betaF_growth G P.L).eventually_gt_atTop 0,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR P)] with x hv hC hh hlim hfiery ht3 hβ hR
  intro c f S hS d hd
  obtain ⟨hsize,hPt,hx,hI,hD,hJ,hq,hp,hthreshold⟩ := hd; rw [hS] at hD hI
  subst Z x q power
  have hb : 0 < d.input.beta := (half_pos hβ).trans_le hI.1
  have ha : 4*d.radius<t := by rw [hD,←mul_assoc]; exact hfiery.trans_lt ht3
  have hcf : c.val ≤ f.val := by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
  have hF : Larger (G:=G) S := ⟨funds_branch hPt,by rw [hS]; omega,by omega⟩
  refine ⟨hb,hD ▸ mul_pos hr (hS ▸ d.paidScale),hF,hS.symm ▸ hlim,shrink hT ha.le,ha,⟨hZ,ht,ht''.le,ht'.le,coupling_pos hb⟩,
    fun A F l V hV => ?_,hθ,hE,rateTrigger_pos cap θ hcap hθ,fun m => ?_⟩
  · refine ⟨(hC S d.tube hS hsize hPt A F l V hV).2,?_⟩
    change Value v d.betaHat d.radius _ _ _ _ _ _ _ d.broadCut _
    rw [hD]; exact hv d.input.beta hb hI.2 d.out rfl hthreshold S d.tube hS hsize hPt A F V hV _
  dsimp only; rw [hS]; exact (hh _ hI.1).2 m

variable {A : Stores S} {F : Forest S.ratio} {l : S.Choices} {V : Config G c} {W Y B κ e' : ℝ}
    {R D N : ℕ}
private lemma native_pos (hT : Pt.Funds S d.tube) (hS : Larger (G:=G) S) : (Native.kinetic d.tube F l d.betaHat).PosDef := by
  obtain ⟨η,hη,he⟩ := Gap.stood G S.patch Pt
  rw [← Native.ground_gram _ _ _ _ hS.1]
  exact Matrix.PosDef.submatrix (Gap.solvent S d.tube _ _ _ _ _ _ hη
    (he S d.tube rfl hS.2.1 hS.2.2 hT _ _ F l)) (Native.lineEquiv F d.betaHat (G:=G)).injective

/-- Consumes on any of the TRUE shared annulus-portfolio price issues
(exact held-sector sponsors & value thresholds, same Charts). -/
lemma Day.certified (h : Day K θ E k n d) (hc : Calling Pt Z q power r x d)
    (hP : Rates Pt S.patch.L R D N d.W r B W Y κ e' x Z)
    (hr : ∃ σ w Λ δ τ, d.input.Lawful σ w Λ δ τ) (hs : Fits d.tube d.input d.betaHat)
    (hv : A.flags=RG.flags (temp d.betaHat) V) :
    d.Valid ∧ Clearing (spectacle d A F l) V ∧ Admitted A F d.betaHat V l Z d.allocation d.radius := by
  obtain ⟨σ,w,Λ,δ,τ,hr⟩ := hr
  obtain ⟨hx,hT,rfl,hβ,hd,rfl,-,-,ht⟩ := hc
  obtain ⟨-, -, ha, he, hQ, hp, hL⟩ := AnalyticBridge.AnnulusRatioInsertions.arrival A d.tube d.betaHat d.W V l d.broadCut d.radius d.chart
    d.input F hT hP.thermal rfl hx hd hv hβ d.allocation hr
  exact ⟨⟨⟨Pt,hT⟩,⟨_,_,_,_,_,hr⟩,hs,h.beta,ht,h.room.localPrice,h.radius,ha⟩,
    ⟨hv,hp,hQ,native_pos hT h.larger,hL⟩,he⟩
end YM.PhysicalNext.JointLoad
