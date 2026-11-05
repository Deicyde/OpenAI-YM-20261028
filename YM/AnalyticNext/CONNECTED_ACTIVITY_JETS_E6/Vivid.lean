import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.CoverageB

/-!
# All raw Mayer-address measures

Uniform on per-sector product. F,T,V fixed; branches with an indicator
zero out factor. Does not assert that pair integrability suffices for later
density-ratio differentiation. Here log letters still pre-integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {W γ x : ℝ} (X : Coat T F)
variable {α : Type*} [MeasurableSpace α] {Y : α→F.Slice G} (hY : Measurable Y)
variable (hc : ShellAccess S G X.x W X.width γ)

include hc hY in
private lemma pulse_meas (θ : P.Funds S T) (a β : ℝ) {v : α→ Air f G} (hv : Measurable v)
    (p : ChainIndex f) : Measurable (fun u => (X.wrapY (Y u)).fuel a β (v u) p) := by
  have ht := X.airwards (v:=v) hc θ hY
  let E u := X.wrapY (Y u)
  let w u := (E u).μ
  let b u := (E u).driftM
  have hx : Measurable b := by
    have he : Measurable (stand (G:=G) (ι:=Bond f)) := by
      refine measurable_pi_lambda _ fun i => ?_; exact (show Measurable (fun u : G.Color => u i.2) from (EuclideanSpace.proj (𝕜:=ℝ) i.2).measurable).comp (show Measurable (fun u : Directions G f => u i.1) from measurable_pi_apply i.1)
    exact he.comp ht.2.1
  have hw : Measurable (fun u=> (E u).hatted β) := by
    have h' := (show Continuous (fun t : Tubular f G→ℝ => X.plate *ᵥ t) by fun_prop).measurable.comp hx
    change Measurable (fun u => -_ • (X.plate *ᵥ b u + (E u).linearBill))
    exact Measurable.smul (measurable_const (a:= -(gStep β)⁻¹)) (h'.add ht.1)
  have hF i : Measurable (fun u => (E u).aperture β (v u) a i) := by
    change Measurable (fun u => if X.Hot i then X.cone (2*a) ((E u).liftA β (v u)) i else 1); split_ifs
    · exact (X.cone_b ..).comp (ht.2.2 β hv)
    exact measurable_const
  have hc (i : Tubular f G) : Measurable (fun u=> WithLp.ofLp (v u) i) := (EuclideanSpace.proj (𝕜:=ℝ) i).measurable.comp hv
  rcases p with p|p|p|p|p
  · exact (show Measurable (fun _ : α => -(Itinerary.ArmA X.shutter X.plate p)/2) from measurable_const) 
  · exact (measurable_const (a:=Itinerary.ArmA X.shutter X.blank.plate p/2))
  · exact (measurable_const (a:=Itinerary.ArmS X.shutter X.plate p/2))
  · have hs : Measurable (fun u => (E u).qlinear β (v u) p) := Finset.measurable_fun_sum _ fun i _ =>
      (hc (p,i)).mul ((measurable_pi_apply _).comp hw)
    exact (hF _).mul hs
  have he : Continuous (fun v=>X.qunique v p) := by unfold qunique circle; fun_prop
  exact ((hF p.2.1).mul (hF (Itinerary.arrive p.2.1 p.2.2))).mul (he.measurable.comp hv)

include hc hY in
lemma log_b (a : ℝ) {R : Rep G f} {Ñ : ChartRatio G} (hR : Intake P T X.x R) (he : LocalRatio Ñ)
    {v : α → Air f G} (hv : Measurable v) (i : LogIndex c f) : Measurable (fun u => (X.wrapY (Y u)).farLog R a Ñ (v u) i) := by
  have hh := X.airwards (v:=v) hc hR.ready hY
  let D u := X.wrapY (Y u); let f' u := (D u).liftA R.beta (v u)
  have ht : Measurable f' := hh.2.2 _ hv
  have hu := X.summon hY ht
  rcases i with i|i|p
  · exact ((rawlog_b hR X.V i).comp hu).mul ((X.enforce_b (2*a) (X.plaza (Raw.space T 0 X.B R i))).comp ht)
  · rcases i with i|i|i
    · let o := rowSite S i
      have hm : Measurable (fun u => X.enforce (2*a) (f' u) (X.booth o) *
          (D u).light (f' u) i.1 i.2 + (D u).extracted ((D u).μ) i.1 i.2) :=
        ((((X.enforce_b ..).comp ht).mul (X.principals_b hY hc ht hR.ready i.1 i.2).2).add
          (X.extracts_b hY hc _ _ hR.ready hh.2.1))
      change Measurable (fun u => if Inside o X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation *
        (X.enforce (2*a) (f' u) (X.booth o)*(D u).light (f' u) i.1 i.2+(D u).extracted ((D u).μ) i.1 i.2))
      split_ifs
      · exact measurable_const
      exact measurable_const.mul hm
    · exact (measurable_const (a:= X.undercurrent i))
    change Measurable (fun u => X.solo (f' u) Ñ a i); unfold solo; split_ifs
    · exact (X.gentry_b _ _ he _).comp ht
    exact measurable_const
  exact X.pulse_meas hY hc hR.ready a R.beta hv p
end YM.ConnectedActivityE6.Coat
