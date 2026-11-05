import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Rutter
/-!
 # Ξ.T discrepancy tested even when CHAR.V6 compact vs V9.Q.Bounds.Consume after 
  proof of acquisition at all x heights. continuity budgets Book.Small.Old μ remain.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Baffle Prism Brim Lotus Peak
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (h : Intake P T X.x R) (hp : Scrim X a) (hP : Room P S T X.x)
variable (U: Lotus.Leaf R)(hg:U.turn= .logKey i)
variable (L' : Config G f→ℝ)(hL': R.p.Regular (R.activities.reg i).support L')(hm:U.ingredient= masked R.p.threshold (R.activities.reg i).support L')
variable {ζ d A t : ℝ} (ht : Canary G d A)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ} {v N Q K δ τ L M m m' : ℝ}
variable (A' : Anthem n) (hs : ∀ (u:Prices G I), ‖u‖≤ L→ Score X i R a q κ b D u K d ζ δ N Q A' Z p)
variable (hr : Ranks X i R a q κ b D Z d ζ p n) (hf : 0 < ζ*X.t) (hy : Tendsto Z (𝓝 p) (𝓝 X.V))
variable (hK : ∀ y, dotProduct y ((lamp6 X a X.V) *ᵥ y) ≤ M * dotProduct y y)
variable (hv : 0≤ v) (he : gStep R.beta*(Fintype.card G.ColorIndex:ℝ)*(v+δ)<(D.ε*R.p.threshold)/8) {Bt : BudgetPoint} {Ct : Libretto G n}
include h hp ht hr hK A' hs hf hy hP hv he U hg hm hL'
lemma wickets (hc : Plays Ct D Bt R.p P T X.x) (hz : Healthy Bt.threshold Y X.V) (hh : ∀ᶠ x in 𝓝 p, (vary X (Z x)).relating.PosDef ∧ Drivable X d A (Z x))
    (hA : ∀ i, Tendsto (volume9 X a q 1 b i ∘ Z) (𝓝 p) (𝓝 (volume9 X a q 1 b i X.V)))
    (he' : ∀ i, ‖volume9 X a q 1 b i X.V‖ ≤ m*X.t) (hw : m*X.t+D.ε*R.p.threshold ≤ ζ*X.t) (hb : 8*ζ*X.t ≤ d/2)
    (hvol : ∀ i,‖volume6 X a i X.V‖ ≤ m'*X.t) (hB : Baffle.screen ζ X.t m' (gStep R.beta) ≤ L) (hL : 0≤L) (h₁ : 0 ≤ K) (l : ℕ) (W : ℝ) (Ñ : ChartRatio G) :
    let y x:= U.cinema (vary X (Z x)) {Opacity.key S i} W ζ Ñ l (podium S G Y X.B)
    let u:= a.hymn T (gStep R.beta) q b X.k L' (magic D R.p R.beta κ) 1
    Brush n (U.weight * (2*Prism.blend A' N Q δ K v M)) 1 (fun x=> y x - u (Z x)) p := by
  intro g u; let f:= Mercury.both X i R a q κ b D U d ζ Z; let B:=Malachite.lamp6 X a X.V; let μ:= cloud B
  have h₀:= hs 0 (by rwa [norm_zero]); have hp₀ : (lamp6 X a X.V).PosDef := h₀.at_z ▸ (show (lamp6 X a (Z p)).PosDef from h₀.commits.sane)
  let V:=outage (ι:=I×G.ColorIndex) v; have hV : MeasurableSet V := outageSet ..
  have hT:= liveIn X a ht h.positive hc hz hp q κ b hy hA hf he' hw
  have hH:∀ᶠ x in 𝓝 p, ∀ s, veil X a q κ b D R.p d R.beta s (Z x)≠0 → coin X i R a d R.beta ζ (Z x) s=1:= hT.mono fun _ hh s hv=> (hh s hv).1
  obtain ⟨ha,hz'⟩:= corridor X i R a q κ b D h ht U hf hy μ hr hvol hH -- order
  let w:= |ground0 A' N Q δ K|; let r:= |altitude A' N Q δ|; let τ:=U.weight; have hU:0≤τ:=U.profit
  let s' (z : Prices G I):=τ*(2*w)+ V.indicator (fun _=>τ*(2*r)) z
  have hF : Brush n (U.weight * (2*Prism.blend A' N Q δ K v M)) 1 (fun x=> ∫ z,f x z ∂μ) p:=by
    have hr:0≤ τ*(2*r):=mul_nonneg hU (mul_nonneg zero_le_two (abs_nonneg _)); have hw:0≤τ*(2*w):=mul_nonneg hU (mul_nonneg zero_le_two (abs_nonneg _)); have hc:Integrable (V.indicator (fun _ : Prices G I=> τ*(2*r))) μ:= (integrable_const _).indicator hV
    refine ha.buds s' ((integrable_const _).add hc) zero_le_one ?_ (ae_of_all _ ?_)
    · unfold s'; rw [integral_add (integrable_const _) hc,integral_const,integral_indicator hV,setIntegral_const]; simp only [probReal_univ,smul_eq_mul,one_mul]; unfold blend; apply (add_le_add_right (mul_le_mul_of_nonneg_right (spent M v hp₀.posSemidef hK h₀.geom) hr) _).trans_eq
      unfold w r τ; ring
    intro z
    have hq : τ*(2*w) ≤ s' z:= by unfold s'; exact le_add_of_nonneg_right (indicator_nonneg (fun _ _=>hr) _)
    by_cases h' : ‖z‖ ≤ L
    · have H:=hs z h'; by_cases hh : z∈V
      · have hx:=crump X i R a q κ b D h ht U A' z H
        apply hx.climb _ le_rfl; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two) hU).trans ?_; unfold s'; rw [indicator_of_mem hh]; exact le_add_of_nonneg_left hw
      have hf:= seaward X i R a q κ b D h ht A' hs hH hv he z h' hh
      exact (crumb X i R a q κ b D h ht U A' z H h₁ hf).climb ((mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (le_mul_of_one_le_left (abs_nonneg _) one_le_two)) hU).trans hq) le_rfl
    apply zi _ (hw.trans hq) zero_le_one
    filter_upwards [silence X i R a h ht hy hf hvol hB hL,hH] with y ha he
    have hz':= ha z (lt_of_not_ge h'); have ht:veil X a q κ b D R.p d R.beta z (Z y)=0:=Classical.not_not.mp (fun hz=>zero_ne_one (hz'.symm.trans (he _ hz)))
    change box6 X i R a U d ζ (Z y) z-box9 X i R a q κ b D U d (Z y) z=_; unfold box6 box9; rw [ht,hz',zero_mul,mul_zero,mul_zero,sub_zero]
  apply hF.shimmy; filter_upwards [hz',hh,h₀.earns,hT] with z hh' hH hh hz
  unfold g u; rw [pop6 X i R a h hp hP ht hH.2 U hg hf hb l Ñ W hp₀ hH.1,pop9 X i R a q κ b D h hp ht hH.2 U L' hL' hm hf hb hp₀ hh.2 hz]; exact (integral_sub hh'.1 hh'.2).symm
end YM.PhysicalNext.Repeat.Mercury
