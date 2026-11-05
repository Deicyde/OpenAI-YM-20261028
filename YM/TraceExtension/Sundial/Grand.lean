import YM.TraceExtension.Sundial.ScalePos
import YM.Fields.System

/- Clarifying `rtflux` convention of pin label and identifications. Not doing
 that proposition (no local commutator claimed). -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Filter Set Extraction OS Spec Mink Boundary MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S)
def zeta (a:Axis):ℂ:= if a=timeAxis then -Complex.I else 1
def metric (a:Axis):ℝ := if a=timeAxis then 1 else -1
def energyM(a b:Axis): S.Union:= S.pin 4 (-(zeta a*zeta b) • F.sector.energy a b)
lemma pin_fromM : S.pin 4 (stressTrace F.sector.energy)=∑ i:Axis,(metric i:ℂ) • energyM F i i:=by
   unfold stressTrace; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold energyM metric; by_cases ht:i=timeAxis
   · simp [ht,zeta,Complex.I_mul_I]
   simp [ht,zeta]
lemma pinCentered : pinned F= ∑ i:Axis,(metric i:ℂ) • energyM F i i - euclideanVEV S (selected F) (stressTrace F.sector.energy) • S.pin 4 (S.unit 4):=by
   rw [← pin_fromM]; unfold pinned center theta centerIn;rw [map_sub,map_smul]
lemma opM (x:Test4): F.action.operators.field (S.pin 4 (stressTrace F.sector.energy)) x=∑ i:Axis,(metric i:ℂ) • F.action.operators.field (energyM F i i) x:=by rw[pin_fromM, map_sum]; simp only[LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
-- unit under `pin` is label definition, light boundary UH. Center already genuine by V boundary.
lemma nonzero_strength {A:ℝ} (ha:0<A)(he:EuclideanAsymptotic F A) : pinned F≠0:=by
   intro hv; have hx : center F=0:= S.pin_inj _ (hv.trans (map_zero _).symm)
   have hp(t):euclidean F t=0:=by unfold euclidean;rw[hx];exact MultilinearMap.map_coord_zero _ (0:Fin 2) rfl
   unfold EuclideanAsymptotic at he; simp only [hp,smul_zero] at he
   have h:= tendsto_nhds_unique he tendsto_const_nhds; exact Complex.ofReal_ne_zero.mpr ha.ne' h
end YM.TraceExtension
