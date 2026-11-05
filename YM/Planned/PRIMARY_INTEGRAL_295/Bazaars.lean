import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Planned.PRIMARY_INTEGRAL_295.Porous
import YM.Planned.PRIMARY_INTEGRAL_295.Streets
import YM.Planned.PRIMARY_INTEGRAL_295.Units


/-!
# One real tree at a path with E μ0,

Sending named numerical stamps. Torus not swapped with cover in nonlinear
field. Uses `Stand` instantiated with shared Gaussian multiplier and
real Stand assertions (later below), `μ0` realized on actual `AxisChart`
(evaluation only at projected contact T). *Contacts* require true b/budget
and certifying dealer's centered intent on that chart. The b field is patch
log extension in sector's conditions (not a new probability kernel).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Bazaars
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place Emits Ripple
open Precision Exterior Tree Streets Porous Carrier Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {T : Finset Cover} {k l d : ℕ} {t ξ s M δ : ℝ} {F : Labels.Frame G d} {c f : Side}
variable {S : StepData c f}

section Observant
-- restrict fields to T centered footprint (0 o). Don't enlarge, as
-- $n(μ)$ not simultaneous for every origin. `Foot B.opts` separately.
def wall (c : Side) (S : Finset Cover) (G:Gauge) : (Site c → G.Color) →L[ℝ] (S→G.Color) :=
    ContinuousLinearMap.pi fun i:S=>ContinuousLinearMap.proj (wrap c i.val)
def terrace (c : Side) (S : Finset Cover) (G:Gauge) : Directions G c →L[ℝ] Dev S G :=
    ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (wrap c (first i).val,beam i)
lemma wall_cost (c : Side) (S : Finset Cover) (G:Gauge) : ‖wall c S G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun x=> (norm_le_pi_norm v _).trans hv.le)
lemma terr_cost (c : Side) (S : Finset Cover) (G:Gauge) : ‖terrace c S G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun x=> (norm_le_pi_norm v _).trans hv.le)

variable (T)

def earth (S : StepData c f) (W : Lines S.ratio.count) : Dir G c →L[ℝ] Dev T G :=
    (terrace f T G).comp (tapes S W)
def meets (S : StepData c f) (F : Forest S.ratio) : AxisChart G F →L[ℝ] Dev T G :=
    (terrace f T G).comp (streamFill S F)
lemma on_torus (S : StepData c f) {W : Lines S.ratio.count} (h : Whole W) (v : Dir G c) :
    earth T S W v = Units.inView T (applyLine W (aboard G c v)) := by
  rw [← street S.ratio W h v]; rfl
end Observant

/-- b is already normalized by t, ν0 normalized by t. Tree coordinates
absolute increments. Full fine support query later may rely on cutoffs.
`ν` all z indexes but only visits actual T. Nothing here implies their
Gaussian source identity or positivity.
-/
structure Launch (I E : Type) [Fintype I] (G : Gauge) {c f : Side} (S : StepData c f) where
  tree : Forest S.ratio
  b : E → Dir G c
  mean : E → AxisChart G tree
  probe : Sky I →L[ℝ] AxisChart G tree
  variation : E → Sky I →L[ℝ] Sky I
  gamma : Sky I→ℝ

namespace Launch
variable (h : Launch I E G S) (T) (W : Lines S.ratio.count)
-- sending Vair pre (β band true). normalized-then-scaled.

def muCut (y:E) := meets T S h.tree (h.mean y)
def muLin (y:E) := meets T S h.tree (crick S h.tree W (h.b y))

def pose (y:E) : Dressed T G := (wall f T G (axisPhi S h.tree W (h.b y)), h.muCut T y, terrace f T G (cellc S.ratio (h.b y)))

def stage : Stand I E T G where
    det := h.pose T W
    breeze := (0:Sky I →L[ℝ] (T→G.Color)).prod (((meets T S _).comp h.probe).prod (0:Sky I →L[ℝ] Dev T G))
    square := h.variation
    gamma := h.gamma

/-- Physical U at already varying marginal x-profile coords v. Only pay
actual entries at F.Free, explicit torus gauges used for `Pore`.
To use Probe kernel V consumers need true coordinate localization elsewhere. -/
def reading (t ξ : ℝ) (y : E) (v : Sky I) : Config G f :=
    lifting h.tree (represent (t • h.b y)) (t • (h.mean y + ξ • h.probe v))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma forecast (x:E) : archL T G (h.pose T W x) = earth T S W (h.b x) + (h.muCut T x-h.muLin T W x) := by
  classical
  ext1 i
  let b:= h.b x; let y:= (wrap f (first i).val,beam i)
  have hg : wrap f (last i).val=y.1+step y.2 := by unfold last y; rw [map_add, wrap_step]
  let A:=axisPhi S h.tree W b; let c:=cellc S.ratio b; let Q:=streamFill S h.tree (G:=G);
  change A y.1 + Q (h.mean x) y + c y - A (wrap f (last i).val) = tapes S W b y + (Q (h.mean x) y - Q (crick S h.tree W b) y)
  rw [hg,show Q (crick S h.tree W b) y= _ from fill_linear S h.tree W b y,step_straight]
  unfold A c; abel


end Launch
end YM.Planned.PrimaryIntegral295.Bazaars
