import YM.Analysis.Polydisc
import YM.Bid.Station
import YM.PREC.Derivative

/-! With the actual center branch rules, choices all give the same predictor
on germs, hence the same unmasked functions on germs. -/

set_option autoImplicit false
noncomputable section

open Filter Function
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace YM.Work.F04

open Lattice RG Wilson Precision Exterior Bid Tree

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Compare on actual fine chart before restricting to the tree. -/
lemma prediction_germ_chart (h : S.patch.Branches S.kernel G) (t r : S.Choices)
    (e : Edge (Site c)) :
    (fun x : Dir G f => S.prediction (represent x) t e) =ᶠ[𝓝 0]
      (fun x => S.prediction (represent x) r e) := by
  filter_upwards [Push.lips S h e t, Push.lips S h e r,
    Push.threshold S e.1 (G := G), Push.threshold S (e.1 + step e.2) (G := G)] with i hi hj hk hm
  have hf (y : Site c) (hy : S.patch.usesMin S.kernel (Push.product S y i)) :
      S.frames (represent i) t.1 y = S.frames (represent i) r.1 y := by
    unfold Push.product at hy
    simp only [StepData.frames, Patch.frame, if_pos hy]
  have hb : Push.deck S e t.1 i = Push.deck S e r.1 i := by
    unfold Push.deck StepData.connector
    rw [hf _ hk, hf _ hm]
  rw [hi, hj, Push.bonds, Push.bonds, hb]

lemma prediction_germ (h : S.patch.Branches S.kernel G) (t r : S.Choices) :
    (fun U : Config G f => S.prediction U t) =ᶠ[𝓝 1] (fun U => S.prediction U r) := by
  let Λ : Config G f → Dir G f := fun U i => G.plog (G.mat (U (i.1, axisEquiv.symm i.2)))
  have hl : Tendsto Λ (𝓝 1) (𝓝 0) := by
    have hc : ContinuousAt Λ 1 := by
      apply continuousAt_pi.mpr
      intro i
      let g := fun U : Config G f => G.mat (U (i.1, axisEquiv.symm i.2))
      have hh : Continuous g := by unfold g; fun_prop
      have he : ContinuousAt G.plog (g 1) := by
        rw [show g 1 = 1 from G.mat_one]; exact G.plog_diff.continuousAt
      exact he.comp hh.continuousAt
    simpa only [show Λ 1 = 0 by ext1 i; simp [Λ]] using hc.tendsto
  have he (b : Edge (Site f)) : ∀ᶠ U : Config G f in 𝓝 1,
      G.lieExp (G.plog (G.mat (U b))) = U b :=
    ((continuous_apply b).tendsto (1:Config G f)).eventually G.plog_right
  have hq : ∀ᶠ U : Config G f in 𝓝 1, represent (Λ U) = U := by
    filter_upwards [eventually_all.mpr he] with U hu
    funext b
    simpa only [Λ, represent, increment, collect,
      show axisEquiv.symm (coord b.2) = b.2 from axisEquiv.symm_apply_apply b.2,
      Pi.one_apply, mul_one] using! hu b
  filter_upwards [hq, hl.eventually (eventually_all.mpr fun e => prediction_germ_chart h t r e)] with U hu hh
  funext e
  have hf : S.prediction (represent (Λ U)) t e = S.prediction (represent (Λ U)) r e := hh e
  rwa [hu] at hf

lemma lifting_cont (H : Forest S.ratio) :
    Continuous fun z : Dir G c × AxisChart G H => lifting H (represent z.1) z.2 := by
  unfold lifting
  apply H.continuous_drape.comp
    (f := fun z : Dir G c × AxisChart G H =>
      fun i : H.Free => G.lieExp (z.2 i) * replica S.ratio (represent z.1) i)
  apply continuous_pi
  intro i
  apply Continuous.mul (by fun_prop)
  unfold replica
  split
  · exact continuous_const
  unfold represent increment collect
  fun_prop

lemma tested_germ (h : S.patch.Branches S.kernel G) (H : Forest S.ratio)
    (p : Clip) (W : PathData G) (t r : S.Choices) :
    uncurry (tested H t p W) =ᶠ[𝓝 0] uncurry (tested H r p W) := by
  have ht := (lifting_cont (S := S) H).tendsto (0 : Dir G c × _)
  simp only [Prod.fst_zero, Prod.snd_zero, link_one, lifted, replica_one] at ht
  filter_upwards [ht.eventually (prediction_germ h t r)] with z hz
  change S.prediction _ _ = S.prediction _ _ at hz
  simp only [uncurry, tested, noiseTaylor]
  rw [hz]

end YM.Work.F04
