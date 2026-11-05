import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bourse
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Moire
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Press
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seller
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Silos



/-!
# Differentiating the full multiplier price along this R phase experiment

Top pack price PF at contour (supplied against actual perturbation next). No change
out of a common ChartRatio/L with retiming. Both connected and arbitrary matrix ancestry.
Direction derivatives NOT asserted. Signed storage schedules can use these for coupling influence;
neighborhood with V via separate fixed Uses gate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed Cab Presented Canvas Coverage
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} (T : Tube G S)
    (R : Rep G f) (x W r : ℝ) (N : ChartRatio G)
    (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (s : Finset (Tab S)) (L : Finset ℕ) (B : Chi)

private abbrev phot := dirPhoto S (surface S T R x s) G (radiusB x)
private abbrev rock := coRef T x V F A

def brief (X : Turns) := cord (phot T R x s) X.foot (takePaid X).expense

def metronome (t : ℂ) (p : F.Slice G × ArrayR G f) := abrupt (phot T R x s) (rock T x V A F) t p.2 *
    ∏ i∈s,galop T x W R N L (figure T x r B A F V k p.1) p.2 i t

def ferry (t : ℂ) := ∫ p, metronome T R x W r N V k A F s L B t p∂ (F.order G).prod (demand T x V F A)

variable {P : Teller G} {C : ℝ} (hf : P.Funds S T) (hC : Optic T x C) {σ C' Λ δ w : ℝ} (hR : R.Lawful σ C' Λ δ w)
    (hs : Fits T R x) (hN : Choice N r) (hr : 0<R.beta)

include hf hC hR hs hN hr


section earn

def Wake (X : Turns) (p : ℝ) (Z : Other S→Tilt (Vars G f)) (a γ : ℝ) := let t := oldTill (takePaid X)
    Token T x r t Z (fun _ L _ Y z => other T x W (retime R p) N L Y z) (pOther T x R) a γ t.expense

variable (t : Turns) (ht : t.Takes (eyes S G (radiusB x)) (gram T F x A V) (dcol S) (paceR x))
    (P Q : Other S → Tilt (Vars G f)) {a γ : ℝ} (hX : Wake T R x W r N t pit P a γ) (hY : Wake T R x W r N t ridge Q a γ)
    (p : Stores S → ℝ) (he : Mandatory S x s) (hh : cert S x A V) (hℓ : ∀ i∈panes S s,Installed i A (450*radiusB x))

variable (hv : ∀ i, Installed i A (450*radiusB x) → Packets.connected S 500 (radiusB x) i →
    ∀ L (Y : Mint T F A x) z, Y.V=V → Y.u= holdSize G S.patch x → Y.r=r →
      4^(pulp F G i x)*(|pulse T x W R N L Y z (.inl i) pit|+|pulse T x W R N L Y z (.inl i) ridge|) ≤ p i)

include ht hX hY he hh hℓ hv
omit hC in
lemma linen : let C := grant (takePaid t) P Q; let J := palet (takePaid t) t.foot; let D := ∏ i∈s, Mixed.costs S 500 (radiusB x) p C i; let F' := ferry T R x W r N V k A F s L B
    (∀ u∈ Metric.ball (0:ℂ) (brief T R x s t), Integrable (metronome T R x W r N V k A F s L B u)
      ((F.order G).prod (demand T x V F A))) ∧ room (brief T R x s t) F' (J*D) := by
  intro C' J D F'
  obtain ⟨hp,hs',hm⟩ := normalized_law t T x V F A ht
  let M := rock T x V A F; let m := demand T x V F A; let E := F.order G
  haveI : IsProbabilityMeasure m := hm; haveI : IsProbabilityMeasure E := by unfold E; infer_instance
  let Z := metronome T R x W r N V k A F s L B; let X := phot T R x s
  let w := takePaid t; let v := t.foot; let b := brief T R x s t; let fZ := levyBill X v w.expense
  let U y := figure T x r B A F V k y
  have ht' : 0<w.expense := half_pos t.carries
  have ho (i : Stores S) (hi : i∈s.toLeft) (y : F.Slice G) z (u : ℂ) (h : ‖u‖≤1/16) :
      ‖galop T x W R N L (U y) z (Sum.inl i) u‖ ≤ p i := ((massFare _ (evolution T x W R N L (U y) z i hr hN.h) h).trans
        (hv i (hℓ i hi) (he.1 i hi) L (U y) z rfl rfl rfl))
  have he' i y z u (h : ‖u‖≤1/16) : ‖galop T x W R N L (U y) z (Sum.inr i) u‖ ≤
      Ticket (souvenir (P i)) z + Ticket (souvenir (Q i)) z := by
    apply (counted _ (trails T x W R N L (U y) z i hr) h).trans; rw [mul_add]
    have h1 := hX.sound A L F (U y) ((1+pit) • z) hh rfl rfl i
    have h2 := hY.sound A L F (U y) ((1+ridge) • z) hh rfl rfl i
    exact add_le_add ((mul_le_mul_of_nonneg_left h1 (show 0≤(10:ℝ) by norm_num)).trans
        (payDilation (hX.positive i) _ (by norm_num [pit]) _))
      ((mul_le_mul_of_nonneg_left h2 (show 0≤(10:ℝ) by norm_num)).trans (payDilation (hY.positive i) _ (by norm_num [ridge]) _))
  let a' := ∏ i∈s.toLeft,p i
  let H := cobble s.toRight P Q fZ
  have h' : 0≤a' := Finset.prod_nonneg (fun i hi => le_trans (norm_nonneg _) (ho i hi (fun _=>1) 0 0 (by norm_num)))
  have hc i : 0 ≤ C' i := add_nonneg (mul_nonneg (by norm_num) (sale_nn _ (hX.positive _)))
    (mul_nonneg (by norm_num) (sale_nn _ (hY.positive _)))
  have hg (u : ℂ) (hu : u∈Metric.ball 0 b) (z : F.Slice G × ArrayR G f) : ‖Z u z‖ ≤ H z.2 * a' := by
    rcases z with ⟨y,z⟩; rw [Metric.mem_ball,dist_zero_right] at hu
    have hy := pays_abrupt X M hp v w.expense t.feet ht' ht.precision.1 u hu.le z
    have hz := hu.le.trans (highT X t.feet ht').2
    unfold Z metronome H cobble; rw [norm_mul,norm_prod]; dsimp only
    conv_lhs => arg 2; arg 1; rw [← s.toLeft_disjSum_toRight]
    rw [prod_disjSum,mul_assoc,mul_comm _ a']
    apply mul_le_mul hy _ (mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)) (TKpos (levySound X ht') _)
    exact mul_le_mul (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => ho i hi _ _ _ hz))
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => he' i y z u hz)) (Finset.prod_nonneg fun _ _ => norm_nonneg _) h'
  have hw : (∏ i∈s,costs S 500 (radiusB x) p C' i)=a' * ∏ i∈s.toRight,C' i := by
    conv_lhs => arg 1; rw [← s.toLeft_disjSum_toRight]
    rw [prod_disjSum]; unfold a'; congr 1
    exact Finset.prod_congr rfl (fun i hi => if_pos (he.1 i hi))
  obtain ⟨hi,hL⟩ := marked w s.toRight P Q hX.positive hY.positive (fun s i => hX.tilt i s) (fun s i => hY.tilt i s)
    fZ (levySound X ht') (levy_ge X v w.expense ht'.le) M⁻¹ hs'
  have hb : Integrable (fun i : F.Slice G × ArrayR G f => H i.2 * a') (E.prod m) :=
    ((show Integrable H m from hi).mul_const a').comp_snd E
  have hf' u : Measurable (Z u) := ((continuous_abrupt X M u).measurable.comp measurable_snd).mul (Finset.measurable_fun_prod _
    fun i _ => registers T x W R N hf L hN hR hs A F V k B i measurable_fst measurable_snd u) -- replacing
  have hv' p : Differentiable ℂ (fun u => Z u p) := by
    have h : Differentiable ℂ (fun u => abrupt X M u p.2) := by unfold abrupt; dsimp only; fun_prop
    exact Differentiable.mul h (Differentiable.fun_finsetProd (u:=s) (fun i _ => transitive T x W R N L (U p.1) p.2 i))
  obtain ⟨h1,h2,h3⟩ := chapel _ Z hb b hf' hv' hg
  refine ⟨h1,h2,fun z hz => (h3 z hz).trans ?_⟩
  change (∫ i : F.Slice G × ArrayR G f, H i.2 * a' ∂E.prod m) ≤ J*_
  have hq : ∫ i : F.Slice G×ArrayR G f,H i.2 * a' ∂ E.prod m = (∫ i,H i∂m)*a' := by
    rw [integral_mul_const (_), integral_fun_snd]; simp
  rw [hq]; change _ ≤ J*(∏ i∈s, costs S 500 (radiusB x) p C' i); rw [hw]
  apply (mul_le_mul_of_nonneg_right hL h').trans
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (logLevy X w v) (Finset.prod_nonneg fun i _ => hc i)) h').trans_eq
    (by unfold C' J; ring)

-- Cauchy; normalization full evidence cumulative. Marks selected alphabet costs at this b.





end earn
end YM.AnalyticNext.ConnectedActivity.Plotter
