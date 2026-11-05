import YM.Push.LOOP_COEFFICIENT.PeriodStep

/-!
# The common coefficient at a step (vertex comparison version)

Projection is on the *whole* polarized precision per coarse site, not
half of it and not a determinant computed with the map drift deleted.
Signature forces a single physical color and kinetic normalization (assuming
the output free `K'` convention and convergence at cofinal periods of the
same data). The price bound may use a different reference comparison width
from the weighted annular tests, but requires pre-L bounds there. No
construction of stationary branches here. Passing to exponential-norm paths
still requires a two-leg lift of the residual; this node by itself concerns
only the precision and number.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Set Filter Matrix Complex Lattice Laurent Precision Wilson Tree RG Exterior Bloch
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {L : Side} (a : G.ColorIndex) {V W : Momentum → Matrix (Axes G) (Axes G) ℂ} (hv : ContDiffAt ℂ ω V 0) (hw : ContDiffAt ℂ ω W 0)
include hv hw
lemma probe_add : probe₂ (V+W) a = probe₂ V a + probe₂ W a := (congr_arg (· / 2) (line_add (analyticComponent hv (1,a) (1,a)) (analyticComponent hw (1,a) (1,a)) (unitAxis 0) 2)).trans (add_div ..)

omit hv hw in
lemma probe_smul (c : ℂ) : probe₂ (c • V) a = c * probe₂ V a := (congr_arg (· / 2) (line_const_mul (f:=fun z => V z (1,a) (1,a)) c (unitAxis 0) 2)).trans (mul_div_assoc ..)
lemma probe_congr (h : ∀ p,star p=p → V p = W p) : probe₂ V a = probe₂ W a := congr_arg (· / 2) <|
    line_congr (germ_real (analyticComponent hv (1,a) (1,a)).analyticAt (analyticComponent hw (1,a) (1,a)).analyticAt (Eventually.of_forall fun p hp => congr_fun (congr_fun (h p hp) (1,a)) (1,a))) (unitAxis 0) 2
omit hv hw in
lemma collect_probe {P : Profiles L (Axes G) (Axes G)} (hp : ∀ k : Site L, ContDiffAt ℂ ω (fun z => P z k) 0)
    (hU : ∀ k : Site L, ContDiffAt ℂ ω V (aliasAt 0 k)) (h : AliasJet P) (h' : Signature.Short V 2) : probe₂ (collectPair P V) a = probe₂ V a :=
  congr_arg (·/2) (congr_fun (congr_fun (collect_mark hp hU h h' (unitAxis 0)) (1,a)) (1,a))
omit hv hw
lemma drift_diff {J Y C : Momentum → Matrix (Axes G) (Axes G) ℂ} (hj : ContDiffAt ℂ ω J 0) (hy : ContDiffAt ℂ ω Y 0) (hc : ContDiffAt ℂ ω C 0) :
    ContDiffAt ℂ ω (driftKernel J Y C) 0 := by
  have hJ := analyticTranspose ((show ContDiffAt ℂ ω J (-0) by simpa using hj).comp (f:=(-·)) 0 (by fun_prop)); have hY := analyticTranspose ((show ContDiffAt ℂ ω Y (-0) by simpa using hy).comp (f:=(-·)) 0 (by fun_prop))
  exact ((analyticMul hJ hy).add (analyticMul hY hj)).sub (analyticMul (analyticMul hJ hc) hj)



namespace LoopData
variable {s f : ℕ → Side} {S : ∀ i,StepData (s i) (f i)} {F : ∀ i, Forest (S i).ratio} {ρ : ∀ i, fieldDir G (s i) 1 → AxisChart G (F i)} {P : ChartRatio G}
    {hg : ∀ i, (f i).val = (s i).val * L.val} {p : Clip} {W : PathData G} {H : Precision.Bed} {R : LoopData G L} {η C σ D Λ : ℝ}
variable (hs : Expands s) (hr : R.Regular η C) (hh : H.metric.strip η C) (hpath : W.Bounds p σ D Λ) (hfit : η/L.val ≤ σ)
    (hu : ∀ i, R.Uses (g:=ratioStep hg i) (S i) p W) (ha : ∀ i, Admission (F i) (ρ i) p W (R.lift (g:=ratioStep hg i)) P)
    (hA : ∀ i, mean (S i) * R.lift (g:=ratioStep hg i) = 1 - (S i).kernel.penalty⁻¹ • Precision.K (H.metric.acts (s i)))

def alpha (R : LoopData G L) (W : PathData G) (a : G.ColorIndex) := (probe₂ (R.target W) a).re

def residual (R : LoopData G L) (W : PathData G) (H : Precision.Bed) (a : G.ColorIndex) := R.target W - (R.alpha W a:ℂ) • kineticSymbol G H.metric

include hs hr hpath hfit hu ha
lemma alpha_value : (R.alpha W a:ℂ) = probe₂ (R.target W) a := (signature hs hr hu ha hpath hfit).probe_real (hr.target_diff hpath hfit (Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero (R:=Momentum)))) a
include hh
lemma residual_four (hH : ∀ i,(H.metric.acts (s i)).IsSymm) (hS : ∀ i, Bid.Sworn H (s i) G) (h1 : H.metric.read 0 = 1) : Signature.Short (R.residual W H a) 4 := by
  have hK := kinetic_signature hs hh hr.joint.width hH hS
  have h0 := Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero (R:=Momentum))
  rw [residual,alpha_value a hs hr hpath hfit hu ha]; exact (signature hs hr hu ha hpath hfit).relative_four (hr.target_diff hpath hfit h0) (ha 0).simple hK (kinetic_diff hh hr.joint.width h0) (kinetic_probe (row_analytic hh hr.joint.width h0) h1 a)
include hA
omit hfit in
private lemma split_drift : probe₂ (logKernel R.joint) a = probe₂ (logKernel R.base) a := by
  obtain ⟨e,A,hY⟩ := hr.charge
  let t (i) : (S i).Choices := Classical.arbitrary _
  have h0 := Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero (R:=Momentum))
  let T := driftKernel (-kineticSymbol G H.metric) (kernelOf (respTrace R.charge)) (kernelOf (reverseTrace R.charge))
  have he : ContDiffAt ℂ ω T 0 := drift_diff ((kinetic_diff hh hr.joint.width h0).neg)
    (Integrand.smooth_mean hY.resp (Work.F07.realStrip _ hY.width (star_zero (R:=Momentum))))
    (Integrand.smooth_mean hY.rev (Work.F07.realStrip _ (half_pos hY.width) (star_zero (R:=Momentum))))
  have hT : probe₂ T a = 0 := drift_probe t hs ha (fun i => (hu i).charge (t i)) hY (row_analytic hh hr.joint.width h0) a
  rw [probe_congr a (logKernel_analytic hr.joint h0) (W:= logKernel R.base+T) ((logKernel_analytic hr.base h0).add he) (fun _ hz => drift_ref hs hr hu ha hpath hh hA hz),probe_add a (logKernel_analytic hr.base h0) he,hT,add_zero]

omit hh hA hfit in
private lemma split_fine : probe₂ (collectPair R.rays (fineKernel R.vector R.ghost)) a = probe₂ (fineKernel R.vector R.ghost) a := by
  have h0 := Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero (R:=Momentum))
  have hv z (hz : star z=z) : ContDiffAt ℂ ω (fineKernel R.vector R.ghost) z := ((logKernel_analytic hr.vector (Work.F07.realStrip _ (half_pos hr.vector.width) hz)).const_smul (1/2:ℂ)).sub (logKernel_analytic hr.ghost (Work.F07.realStrip _ (half_pos hr.ghost.width) hz))
  exact hr.start.probe a (hr.rays_diff h0) (fun k => hv _ (by rw [← alias_conj,star_zero])) ((fine_signature hs hr hu hpath (ha 0).simple).twoWard) ((fine_signature hs hr hu hpath (ha 0).simple).short_two (hv 0 (star_zero _)))

omit hs hh hA hu ha in
private lemma split_loop : probe₂ (collectPair R.rays (loopSymbol W)) a = 0 := by
  have h0 := Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero (R:=Momentum))
  have he := hr.start.probe a (hr.rays_diff h0) (fun k => loop_diffAt hpath.width (loopRow_budget hpath.width hpath.two) (fits hfit h0 k)) (loop_twoWard W) (fun p => (loop_four hpath p).mono (by decide))
  rw [he]; exact div_eq_zero_iff.mpr (Or.inl (loop_four hpath (unitAxis 0) (1,a) (1,a) 2 (by decide)))




end LoopData
end YM.Push.Loops
