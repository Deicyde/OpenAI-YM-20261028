import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Sails

/-!
# Joint legality of comparison container as function of all its operands. p local.

β external to calendar. Can vary W to sample log extension, yet no
claim of probability-control (reading flags same according to masks versus output).
 Real obligations from Means specialized in downstream funding. E6 connector
 scales from primal already; don't use R γ casts. No smallness guard in λ here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c} [Fintype I] [DecidableEq I]
variable (i : ℕ) (R : Rep G f) (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
variable {d A w C t : ℝ} (h : Canary G d A)

section Gaussian_law
variable [Fintype ι] [DecidableEq ι] {B : E→ Matrix ι ι ℝ} {Y' : E → Gaussian.Vec ι}
lemma force_joint (hp : ∀ i j, ContDiffAt ℝ (n:WithTop ℕ∞) (fun y=> B y i j) p) (hB : (B p).PosDef) (hY : ContDiffAt ℝ n Y' p) :
    ContDiffAt ℝ n (fun y=> force (B y) (Y' y)) p := by
  unfold force dotProduct Matrix.mulVec dotProduct; refine ContDiffAt.sum fun i _=> (contDiffAt_pi.mp hY i).mul (ContDiffAt.sum (fun k _=> (Blaze.jetBack hp (isUnit_iff_ne_zero.mpr hB.det_pos.ne') i k).mul (contDiffAt_pi.mp hY k)))
lemma exchangeJoint (hp : ∀ i j,ContDiffAt ℝ (↑n) (fun y=> B y i j) p) (hB : (B p).PosDef) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {F : E→ Gaussian.Vec ι} (hF : ContDiffAt ℝ (↑n) F p) (hY : ContDiffAt ℝ n Y' p) :
    ContDiffAt ℝ (↑n) (fun y=> Density.replace (B y) C (F y) (Y' y)) p := by
  unfold Density.replace Density.chip Density.spice
  have hs := (determinant hp).sqrt hB.det_pos.ne'
  have h₁ := force_joint (B:=fun _=> C) (fun _ _=>contDiffAt_const) hC hY
  have h₂ := force_joint hp hB (Y':=fun x=> Y' x + F x) (hY.add hF)
  exact (contDiffAt_const.div hs (Real.sqrt_pos.mpr hB.det_pos).ne').mul (((h₁.div_const (2:ℝ)).sub (h₂.div_const (2:ℝ))).exp)
end Gaussian_law

section payments
-- Enough teeth EVEN if φ mark attempts fail. Ranks input α at all scales.
variable {ζ : ℝ} (hz : Z p=X.V)
variable (he : Intake P T X.x R)
include he h hz
lemma lighthouse (ζ : ℝ) (hf : (vary X (Z p)).relating.PosDef) (hb : (lamp9 X a (Z p)).PosDef)
    (hv : ∀ i j, ContDiffAt ℝ n (fun z=> Malachite.lamp6 X a (Z z) i j) p)
    (hB : ∀ i j, ContDiffAt ℝ n (fun z=> lamp9 X a (Z z) i j) p)
    (hh : ∀ i, ContDiffAt ℝ n (fun z=> volume6 X a i (Z z)) p)
    (hT : ∀ i, ContDiffAt ℝ n (offsetRun X a i q b 1 ∘ Z) p)
    (hE : ∀ i, ContDiffAt ℝ n (fun z=> G.mat (Silica.action X (Z z) (a.address i))) p) : Ranks X i R a q κ b D Z d ζ p n := by
  have h i : ‖G.mat (Silica.action X (Z p) (a.address i))-1‖ ≤ A := by simp only [hz,Silica.action, mul_inv_cancel,G.mat_one,sub_self,norm_zero]; exact h.side.le
  let g:=gStep R.beta; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr he.positive)
  let Y (v : E × Prices G I) k := G.mat (Silica.action X (Z v.1) (a.address k))
  let U (v : E × Prices G I) := anchor X a v.2 R.beta
  have he' k (b : E × Prices G I) : ContDiffAt ℝ n (fun v=> U v k) b := contDiffAt_const.add ((((contDiff_apply _ _ k).contDiffAt.comp _ (f:=fun v:E × Prices G I=> tape v.2) ((colors (G:=G) (ι:=I)).toContinuousLinearEquiv.contDiff.contDiffAt.comp _ contDiffAt_snd))).const_smul g)
  let B (x:E× Prices G I) := fast X (Z x.1) a d R.beta x.2
  let b' (x:E× Prices G I) := fawn X (Z x.1) a x.2 d R.beta
  have hx k s: ContDiffAt ℝ n (fun v:E × Prices G I=> (Y v k,U v k)) (p,s):= ((hE k).comp (f:=Prod.fst (β:=Prices G I)) (p,s) contDiffAt_fst).prodMk (he' k _)
  have hl k (s:Prices G I) : ContDiffAt ℝ n (fun x : E× Prices G I=> b' x k) (p,s) := by
    have hh : Canary G d A:= by assumption
    exact (he' k _).add (((Eider.sheen hh X.χ (U (p,s) k) (Y (p,s) k) (h k)).of_le (m:=n) (WithTop.coe_le_coe.mpr le_top)).comp (f:=fun v:E × Prices G I=> (Y v k,U v k)) _ (hx k s))
  have hK s : ContDiffAt ℝ n (fun x : E × Prices G I=> pulse X (Z x.1) a x.2 d R.beta) (p,s) :=
    contDiffAt_prod fun k _=> (Eider.lift (show Canary G d A by assumption) X.χ (Y (p,s) k) (U (p,s) k) (h k)).comp (f:=fun v=> (Y v k,U v k)) _ (hx k s)
  have hc i j:ContDiffAt ℝ n (fun x:E× Prices G I=> tape (B x) i) (p,j) := by
    simp_rw [show ∀ x:E× Prices G I,tape (B x) i=g⁻¹ • (b' x i-volume6 X a i (Z x.1)) from fun x=> by unfold B; rw [fast,tape.apply_symm_apply]; rfl]
    exact ((hl i j).sub (ContDiffAt.comp (g:=fun z=> volume6 X a i (Z z)) _ (hh i) contDiffAt_fst)).const_smul _
  have hX s: ContDiffAt ℝ n B (p,s) := (colors (ι:=I) (G:=G)).toContinuousLinearEquiv.symm.contDiff.contDiffAt.comp (f:=fun x=>tape (B x)) _
    (contDiffAt_pi.mpr fun i=> hc i s)
  let v (x:E × Prices G I):=distance9 X (Z x.1) a q b R.beta; let y x:=B x+v x
  have hs s : ContDiffAt ℝ n y (p,s) := (hX s).add (((colors (ι:=I) (G:=G)).toContinuousLinearEquiv.symm.contDiff.contDiffAt.comp (f:=fun (v:E× Prices G I)=> (fun j=> -(offsetRun X a j q b (1:Config G f) (Z v.1)))) (p,s) (contDiffAt_pi.mpr fun i=>(((hT i).comp (f:=Prod.fst) (p,s) contDiffAt_fst).neg))).const_smul _)
  have hJ : (lamp6 X a (Z p)).PosDef:= hf.submatrix (scoop X a).injective
  refine ⟨fun s=> (hK s).mul (exchangeJoint (B:=lamp6 X a ∘ Z ∘ Prod.fst) (fun i j=> (hv i j).comp (f:=Prod.fst) (p,s) contDiffAt_fst) hJ (show (lamp6 X a X.V).PosDef from hz ▸ hJ) (((hX s).add contDiffAt_const).sub contDiffAt_snd) contDiffAt_snd),
    fun s=> (hK s).mul (exchangeJoint (B:=lamp9 X a ∘ Z ∘ Prod.fst) (fun i j=> (hB i j).comp (f:=Prod.fst) (p,s) contDiffAt_fst) hb (show (lamp6 X a X.V).PosDef from hz ▸ hJ) ((hs s).sub contDiffAt_snd) contDiffAt_snd),
    fun s=> (guard_silent κ hg (mul_pos D.guards R.p.threshold_pos) (n:=n) (I:=I)).real.contDiffAt.comp _ (hs s),fun s=>contDiffAt_prod fun k _=> ?_⟩
  · unfold Chi.innerShare; simp_rw [div_pow]; exact (X.χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp _
      (((contDiff_norm_sq ℝ).contDiffAt.comp _ (hl k s)).div_const _)
end payments
end YM.PhysicalNext.Repeat.Baffle
