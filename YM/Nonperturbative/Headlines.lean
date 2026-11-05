import YM.Nonperturbative.HeadlineSpec
import YM.Nonperturbative.Continuum

set_option autoImplicit false
noncomputable section
namespace YM.Nonperturbative

universe u v

private theorem wightman {G : Gauge} {C : Family G} {S : Table C.book} {A : Boundary.Wightman S}
    {W : Boundary.Surface S} {V : S.Rotation} {h : S.RealSpin}
    (H : A.Realizes (W := W) V h) : Headline.WightmanAxioms A W :=
  ⟨H.total.norm, H.total.everywhere, H.total.cyclic, H.total.temperate, H.adj, H.meets,
    A.operators.sees W H.meets A.J H.adj, H.localPairs, H.covariance, A.action.strong,
    H.spectral, H.forward, H.unique⟩

/-- One Wilson family has, at each requested extraction order, a continuum
table satisfying the entire public specification. -/
theorem existence (G : Gauge) (hG : G.Simple) (b : ℝ) (hb : 0 < b) :
    Headline.WilsonExistence.{u,v} G hG b := by
  let R := Independent.fundedRun hG hb
  obtain ⟨penalty, allOrders⟩ := continuum_with_position_tests.{u,v} hG hb
  refine ⟨R.family, penalty, R.makes, fun p => ?_⟩
  obtain ⟨q,S,F,L,Q,M,ordered,uv,core,nested,same,contacts,basis,thresholds,X,first,four⟩ :=
    allOrders p
  refine ⟨q,S,F,L,Q,M,X,ordered,uv,F.calibration,core,?_,?_,?_,?_,same,contacts,basis,thresholds,first,four⟩
  · exact ⟨F.realization.allWorld, F.realization.chosen, wightman F.realization.qt,
      fun i => wightman (core.reconstruction.isTheory i), core.reconstruction.at_boundary⟩
  · refine ⟨core.ope.coefficients, ?_, core.joint⟩
    intro I J _ _ d e a b M η c ε hM hη hc hε D
    exact core.point a b hM hη hc hε D
  · exact ⟨nested.direct, nested.tested, nested.joint, nested.jointLaw⟩
  · exact ⟨core.trace.centered, core.trace.identified, core.trace.shortDistance,
      core.trace.positive, core.trace.wick,
      fun n U physical unit translations => core.trace.maxwell n U ⟨physical,unit,translations⟩,
      core.trace.invariant⟩

end YM.Nonperturbative
