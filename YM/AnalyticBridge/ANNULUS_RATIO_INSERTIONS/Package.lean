import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Voucher

/-!
# Fixed V transformed packet integrals

Measurability with all physical reads and cutoffs, even when replacing
`Z`s and `Y`s by an array sampled from a conditional law, and actual
fog law. No claims of V derivatives across even the profile doors at
unprotected real U-points. Give consumption in integral estimates
without resampling parts of the integrand. Measurability via direct
formula; in particular not relying on fderiv on ineligible configs
because D is fixed from V. We really need this on `dyed` vessels AFTER
changing the variables and stopping some defaults, though it is not
required for just the primal pmult pointwise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open SectorNext.Remainder.Affine Harvest Dress
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (O A : Stores S) (T : Tube G S) (x W : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (J : ChartRatio G) (p : Rep G f) (F : Forest S.ratio)

variable (L : Bond f → ℝ) (m : Mean (G:=G) A x F)

def wrapper (uniform : Bool) (b : Finset ℕ) (D R R' : ℕ) (y : GaussArgs (G:=G) A x F) :=
  packet O A T x W V k q d J p F y.1 y.2 L m uniform b D R R'

-- As in Canonical/check, fixed V; here prove also on remaining windows
-- without assuming all V inputs fit. The V-meas and all-V derivative
-- questions are separate.
set_option maxHeartbeats 600000 in
lemma window_env {P : Teller G} (ht : P.Funds S T) (Q : Window S) :
    Envelope (fun U => Q.work T x U k V) := by
  obtain ⟨a,b,ha,hb⟩ := ht.feeds
  rw [← ht.high] at ha
  let t := fiery G x S.patch.L; let R := till x
  let H : Config G f → Config G c := fun u => S.prediction u k
  have hh : Measurable H := S.prediction_meas (funds_branch ht) k
  have hF (i : Cell f) : Envelope (fun U : Config G f => T.workF R U V t (temp x) i) := by
    unfold workF
    exact (env_crown ha _ _ _ _).add (Envelope.sum _ _ fun j => Env.compact (continuous_const.sub (continuous_const.inner (plotted_cont ha ..))))
  have hI (i : Bond c) : Envelope (fun U : Config G f => T.workI R (H U) V (temp x) i) :=
    Env.along (Env.compact (show Continuous (fun v : Config G c => T.workI R v V (temp x) i) by unfold workI monetary wire Z; fun_prop)) hh
  have hL (i : Cell c) : Envelope (fun U : Config G f => T.workL R U (H U) V (temp x) i) := by
    let u (v : Config G f × Config G c) := T.workL R v.1 v.2 V (temp x) i
    have he : Continuous u := by
      unfold u workL unzip Z
      have h (a : Twin f) := plotted_cont ha R 1 a
      unfold Xf; fun_prop
    have hm : Measurable (fun u : Config G f => (u,H u)) := measurable_id.prodMk hh
    exact (Env.along (F:=u) (g:=fun u : Config G f => (u,H u)) (Env.compact he) hm)
  unfold Window.work SectorNext.Remainder.onWindow
  refine (((Envelope.sum _ _ hF).add (Envelope.sum _ _ hI)).add
    (Envelope.sum _ _ (fun i => (Envelope.const _).add ((hL i).add (Envelope.const _))))).add (Envelope.const _)

lemma cont_extraction (s : Signed) (Q : Window S) (H : Stencils S) (hd : 0<d) (ht : 2*d<firstRadius G) {P : Teller G} (hT : P.Funds S T) :
    Continuous (fun y : GaussArgs (G:=G) A x F => extraction T x V k H A F q d y.1 Q y.2 s) := by
  obtain ⟨a,b,ha,hb⟩ := hT.feeds
  let U := fun y : GaussArgs (G:=G) A x F => Rows.lands T x V k H A F q d y.1 y.2
  have hX : Continuous U := by
    let Z : LogArray G (Frozen A x F) →L[ℝ] Directions G f :=
      LinearMap.toContinuousLinearMap -- maybe inferred
        ( { toFun := Rows.input x A F
            map_add' := by intro u v; funext i; rw [Pi.add_apply]; unfold Rows.input; first | split <;> first | split <;> simp | simp
            map_smul' := by intro u v; funext i; rw [Pi.smul_apply]; unfold Rows.input; first | split <;> first | split <;> simp | simp } :
          LogArray G (Frozen A x F) →ₗ[ℝ] Directions G f)
    let C : LogArray G (Active A x F) →ₗ[ℝ] Directions G f :=
        ⟨⟨fresh x H A F,fresh_add x H A F⟩,fun w v => fresh_smul x H A F v w⟩
    let X : Directions G f →ₗ[ℝ] LogArray G (Slots S) :=
        ⟨⟨bump T x V k, bump_add _ _ _ _ ha⟩, fun w v => bump_smul _ _ _ _ ha v w⟩
    have hy : Continuous (fun y : LinkArray G (Frozen A x F) => autoShell q d V y) :=
      (autoShell_continuous q hd ht).comp (continuous_const.prodMk continuous_id)
    have hi : Continuous (tape (G:=G) (ι:=Active A x F)) := gaugeCount.continuous
    unfold U Rows.lands
    exact continuous_const.add (X.continuous_of_finiteDimensional.comp
      ((Z.continuous.comp (hy.comp continuous_fst)).add (C.continuous_of_finiteDimensional.comp (hi.comp continuous_snd))))
  have he i : Continuous (fun y : GaussArgs (G:=G) A x F => ‖U y i‖^2/2) :=
    (((continuous_apply _).comp hX).norm.pow 2).div_const 2
  unfold extraction
  refine (continuous_finsetSum _ (fun i hi => continuous_finsetSum _ fun j _ => ?_)).add
    (continuous_finsetSum _ fun i _ => ?_)
  · unfold chargedUp; split; exact he _; exact continuous_const
  unfold chargedSide; split; exact he _; exact continuous_const

lemma packet_meas (uniform : Bool) (b : Finset ℕ) (D R R' : ℕ) {P : Teller G} (ht : P.Funds S T) (hJ : LocalRatio J)
    (h₀ : 0<d) (hd : 2*d < firstRadius G) (he : 4*d < J.radius) (hm : Measurable m) :
    Measurable (wrapper O A T x W V k q d J p F L m uniform b D R R') := by
  let B := GaussArgs (G:=G) A x F
  let X := fun y : B => mixed A x p F y.1 y.2 m
  let U := fun y : B => volumeRead A x V p F y.1 y.2 m
  let Q s := hot (turnStore s O) D (radiusB x)
  have hx : Measurable X := (hm.comp measurable_fst).add ((measurable_const (a:=coupling p.beta)).smul (g:=fun y : B => y.2) measurable_snd)
  have hu : Measurable U := (physical_meas A F V (x:=x)).comp (f:=fun y : B => (y.1,tape (X y))) (measurable_fst.prodMk (tape.measurable.comp hx))
  have ha (s : Signed) (a : B → Prices G (Active A x F)) (hh : Measurable a) :
      Measurable (fun y : B => extraction T x V k (shots S x) A F q d y.1 (Q s) (a y) s) :=
    (cont_extraction A T x V k q d F s (Q s) (shots S x) h₀ hd ht).measurable.comp (f:=fun y : B => (y.1,a y)) (measurable_fst.prodMk hh)
  have hw s : Measurable (fun y : B => (Q s).work T x (pull s 0 (U y)) (choice s k) (pull s 0 V)) :=
    (window_env T x (pull s 0 V) (choice s k) ht (Q s)).meas.comp (pulling_meas s hu)
  have av (j : B → Signed → ℝ) (h : ∀ i, Measurable (fun y => j y i)) : Measurable (fun y => averaged (j y)) :=
    measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => h i)
  have hq : Measurable (fun y : B => feeRow O A T x V k q d p F y.1 y.2 m D) :=
    (measurable_const.mul (av (fun y s => debt T x V k (shots S x) A F q d y.1 O D (U y) (X y) s)
      (fun s => (hw s).sub (ha s X hx)))).sub ((av (fun y s => extraction T x V k (shots S x) A F q d y.1 (Q s) (m y.1) s)
        (fun s => ha s _ (hm.comp measurable_fst))).div_const _)
  exact ((((Dress.due_meas O A x W V k p q uniform R b (funds_branch ht)).comp hu).mul
    (((rental_meas O A F x q d J R').2 hJ h₀ he).comp hx)).mul measurable_const).mul ((hq.add measurable_const).exp)

end YM.AnalyticBridge.AnnulusRatioInsertions
