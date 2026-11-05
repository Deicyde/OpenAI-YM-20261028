import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Vault
import YM.Progress.STATIONARY_SCENES.Classical
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# Borel energetic measurements (sectorwide, including V)

Core may rely on the hard selectors, not analytic germs across any
flag/mask. Publish for the integrals; use all common T. Consumes
Gauge's physical proof-bearing families. No fibration choice after
projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Canvas
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint  
open Centered Centered.Till  Footprint    Mixed 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type*} [MeasurableSpace α] {U : α→Config G f} {V : α→Config G c}

lemma ip {a b : α→G.Color} (h : Measurable a) (he : Measurable b) : Measurable (fun p => inner ℝ (a p) (b p)) := by
  exact continuous_inner.measurable.comp (h.prodMk he)

-- Kernel apps via continuous operations on full assembled vector (incl dGap).
section gap
variable (x : ℝ) (hT : P.Funds S T) (h : Measurable U) (hv : Measurable V)
include hT hv
lemma zips {v : α→ Twin c → G.Color} (he : Measurable v) (R : ℕ) :
    let W (A) := zip (T.Φ R (V A)) (v A)
    let X (A) := zip (T.Φ' R (V A)) (v A)
    let Y (A) := zip (T.N R (V A)) (v A)
    Measurable W ∧ Measurable X ∧ Measurable Y := by
  intro W X Y
  obtain ⟨h1,h2,h3,h4⟩ := hT.crosses
  let X := Config G c × (Twin c→G.Color)
  have hh {v' : Type} [Fintype v'] (q : Config G c→ v' → Twin c→Pay G) (hh : ∀ i j,Continuous (fun a => q a i j)) :
      Measurable (fun i => zip (q (V i)) (v i)) := by
    apply measurable_pi_lambda; intro j
    exact (show Continuous (fun p : X => zip (q p.1) p.2 j) from cont_zip (fun i j => (hh i j).comp continuous_fst)
      (fun i => by fun_prop) _).measurable.comp (hv.prodMk he)
  exact ⟨hh (T.Φ R) (fun i j => leap_cont (Row.rights _ _ h3 P.width.le) ..),
    hh (T.Φ' R) (fun i j => lane_cont (Row.rights _ _ h1 P.width.le) ..),
    hh (T.N R) (fun i j => lane_cont (Row.rights _ _ h2 P.width.le) ..)⟩
omit hT in
lemma zips' (I : Type) [Fintype I] (v : α→ I → G.Color) (he : Measurable v) (q : Config G c → I → Twin c→ Pay G)
    (hh : ∀ i j,Continuous (fun V => q V i j)) : Measurable (fun i => Pressure.unzip (q (V i)) (v i)) := by
  refine measurable_pi_lambda _ fun j => ?_
  let F (y : Config G c × (I→G.Color)) := Pressure.unzip (q y.1) y.2 j
  have h : Continuous F := cont_unzip (α:=Config G c × (I→G.Color)) (g:=fun a : Config G c × (I→G.Color) => q a.1) (z:=fun y => y.2) (fun i j => (hh i j).comp continuous_fst) (fun i => by fun_prop) _
  change Measurable (F ∘ fun a => (V a,v a)); exact h.measurable.comp (hv.prodMk he)
-- omit hT not needed zips'

lemma vision_me (x : ℝ) (R : ℕ) :
    Measurable (fun a => T.vision R (temp x) (V a)) ∧
      Measurable (fun a => T.Mv R (temp x) (V a)) ∧ Measurable (fun a => T.Mw R (temp x) (V a)) := by
  obtain ⟨e,r,hW,he⟩ := hT.feeds
  rw [← hT.low] at he
  have hx (j) := env_thinned (n:=c) he R S.patch.L.val (temp x) (temp_nonneg _) j
  have hp : Measurable (fun a => T.vision R (temp x) (V a)) := measurable_pi_lambda _ fun i =>
    (hx i).meas.comp hv
  obtain ⟨h1,h2,h3⟩ := zips hT hv hp R
  exact ⟨hp,h1,h2⟩
include h
lemma observes (x : ℝ) (k : S.Choices) :
    let U' i := S.prediction (U i) k; let R := till x
    let v i := Tube.Z S (U' i) (V i)
    Measurable v ∧ Measurable (fun i => T.Xf R (U i)) := by
  intro Q R v
  have hm : Measurable Q := (S.prediction_meas (funds_branch hT) k).comp h
  obtain ⟨r,r',hW,hD⟩ := hT.feeds; rw [← hT.low] at hD; rw [← hT.high] at hW
  have hr : Measurable v := by
    refine measurable_pi_lambda _ fun j => ?_
    let a (p : Config G c × Config G c) := Tube.Z S p.1 p.2 j
    change Measurable (a ∘ fun i => (Q i,V i)); exact (show Continuous a by unfold a Tube.Z; fun_prop).measurable.comp (hm.prodMk hv)
  have hF : Measurable fun a => T.Xf R (U a) := measurable_pi_lambda _ fun j => (plotted_cont hW R 1 j).measurable.comp h
  exact ⟨hr,hF⟩
lemma stripe (x : ℝ) (k : S.Choices) :
    let Q i := S.prediction (U i) k; let R := till x; let t := temp x
    (∀ j, Measurable (fun a => T.workF R (U a) (V a) (fiery G x S.patch.L) t j)) ∧
    ∀ j, Measurable (fun a => T.workI R (Q a) (V a) t j) := by
  intro Q R t
  obtain ⟨hr,hF⟩ := observes hT h hv x k
  have hm : Measurable Q := (S.prediction_meas (funds_branch hT) k).comp h
  obtain ⟨hP,hv',hy⟩ := vision_me hT hv x R
  obtain ⟨hf,hc⟩ := env_cuts hT x h hv
  refine ⟨fun j => ?_,fun j => ?_⟩
  · unfold Tube.workF; refine (hf j).meas.add ?_; apply Finset.measurable_fun_sum; intro i _
    have he := (measurable_pi_apply (j,i)).comp hv'
    exact ((he.norm.pow_const 2).div_const _).sub (ip he ((measurable_pi_apply _).comp hF))
  · have he := (measurable_pi_apply j).comp hy
    have hh := (show Continuous (fun a : Config G c × Config G c => Tube.monetary S a.1 a.2 j) from by
      unfold Tube.monetary wire; fun_prop).measurable.comp (hm.prodMk hv)
    exact hh.add (((he.norm.pow_const 2).div_const _).sub (ip he ((measurable_pi_apply _).comp hr)))
lemma syncs (x : ℝ) (k : S.Choices) :
    let U' i := S.prediction (U i) k; let R := till x; let t := temp x
    (∀ j, Measurable (fun a => T.workC R (V a) t j+(T.workL R (U a) (U' a) (V a) t j+T.workD R (V a) t j))) ∧
    (∀ j, Measurable (fun a => T.workN R (V a) t j)) := by
  intro Q R t
  obtain ⟨hr,hF⟩ := observes hT h hv x k
  obtain ⟨r,r',hW,hD⟩ := hT.feeds; rw [← hT.low] at hD; rw [← hT.high] at hW
  have hX : Measurable fun a => T.Xn R (V a) := measurable_pi_lambda _ fun j => (plotted_cont hD R S.patch.L.val j).measurable.comp hv
  obtain ⟨hP,hv',hy⟩ := vision_me hT hv x R
  have hZ := (zips hT hv hP R).2.2
  obtain ⟨hf,hc⟩ := env_cuts hT x h hv
  refine ⟨fun j => ?_,fun j => ?_⟩
  · obtain ⟨hz,hyN,hzF,_⟩ := hT.crosses
    have hm (i : Bool) := (measurable_pi_apply (j,i)).comp hP
    have hC : Measurable (fun a => T.workC R (V a) t j) := by
      unfold Tube.workC; refine Measurable.sub ?_ (hc j).meas; apply Finset.measurable_fun_sum; intro i _
      exact (ip (hm i) ((measurable_pi_apply (j,i)).comp hX)).sub ((((hm i).norm.pow_const 2).div_const _))
    refine hC.add (Measurable.add ?_ ?_)
    · have hh := zips' hv _ _ hF (T.Φ R) (fun i j => leap_cont (Row.rights _ _ hzF P.width.le) ..)
      have hd := zips' hv _ _ hr (T.Φ' R) (fun i j => lane_cont (Row.rights _ _ hz P.width.le) ..)
      unfold Tube.workL; refine Finset.measurable_fun_sum _ (fun i _ => ?_)
      let y : Twin c := (j,i)
      exact ip (hm i) ((((measurable_pi_apply y).comp hh).add ((measurable_pi_apply y).comp hd)).sub ((measurable_pi_apply y).comp hX))
    have HH := zips' hv _ _ hv' (T.Φ R) (fun i j => leap_cont (Row.rights _ _ hzF P.width.le) ..)
    have HD := zips' hv _ _ hy (T.Φ' R) (fun i j => lane_cont (Row.rights _ _ hz P.width.le) ..)
    have HN := zips' hv _ _ hZ (T.N R) (fun i j => lane_cont (Row.rights _ _ hyN P.width.le) ..)
    unfold Tube.workD; refine Finset.measurable_fun_sum _ (fun i _ => ?_)
    let y : Twin c := (j,i)
    exact (ip (hm i) ((hm i).sub ((((measurable_pi_apply y).comp HH).add ((measurable_pi_apply y).comp HD)).add
      ((measurable_pi_apply y).comp HN)))).div_const _
  exact ((((measurable_pi_apply j).comp hZ).norm.pow_const 2).div_const _)
lemma operates (x : ℝ) (k : S.Choices) :
    let U' i := S.prediction (U i) k; let R := till x; let t := temp x
    let v i := Tube.Z S (U' i) (V i)
    Measurable v ∧ Measurable (fun i => T.Xf R (U i)) ∧
    (∀ j, Measurable (fun a => T.workF R (U a) (V a) (fiery G x S.patch.L) t j)) ∧
    (∀ j, Measurable (fun a => T.workI R (U' a) (V a) t j)) ∧
    (∀ j, Measurable (fun a => T.workC R (V a) t j+(T.workL R (U a) (U' a) (V a) t j+T.workD R (V a) t j))) ∧
    (∀ j, Measurable (fun a => T.workN R (V a) t j)) := by
  intro Q R t v
  obtain ⟨h1,h2⟩ := observes hT h hv x k
  obtain ⟨h3,h4⟩ := stripe hT h hv x k
  exact ⟨h1,h2,h3,h4,syncs hT h hv x k⟩

lemma target_me (x : ℝ) (q : S.Choices) (p : Pos S) : Measurable (fun a => target T (till x) (temp x) p q (V a) (U a)) := by
  rcases p with ⟨s,i⟩
  let hX := pulling_meas s h; let hV := pulling_meas s hv
  obtain ⟨hY,hU,_⟩ := operates hT hX hV x (choice s q)
  obtain ⟨_,ht,hr⟩ := vision_me hT hV x (till x)
  rcases i with i|i
  · exact ((measurable_pi_apply i).comp hU).sub ((measurable_pi_apply i).comp ht)
  exact ((measurable_pi_apply i).comp hY).sub ((measurable_pi_apply i).comp hr)
lemma booth_meter (x : ℝ) (q : S.Choices) (i : Rack S) : Measurable (fun a => booth T (U a) q (V a) x i) := by
  rcases i with ⟨s,i⟩
  have hV := operates hT (pulling_meas s h) (pulling_meas s hv) x (choice s q)
  rcases i with i|i|i|i
  · exact measurable_const.mul (hV.2.2.1 i)
  · exact measurable_const.mul (hV.2.2.2.1 i)
  · exact measurable_const.mul (hV.2.2.2.2.1 i)
  exact measurable_const.mul (hV.2.2.2.2.2 i)
end gap
end YM.AnalyticNext.ConnectedActivity.Canvas
