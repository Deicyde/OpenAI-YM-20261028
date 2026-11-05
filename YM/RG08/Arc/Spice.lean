import YM.RG08.Arc.Meadow
/-! # Price integral coefficients of the shifted germ with true Gaussian heat,
pack moment and pivot share tangent measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial YM.PertExtension.Chart YM.PertExtension.GaussianScore
open Function Analysis Tree Lattice RG
open scoped BigOperators Topology Real ContDiff Classical
variable {c f : Side} {S : StepData c f} (G : Gauge) (T : Forest S.ratio)

local notation "A" => FreeResolvent.Active G T →ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
local notation "⌂" => tangent G T.Free
local notation "Θ" => hold G T.Free

def maplit : (A) ≃L[ℝ] (L) := LinearEquiv.toContinuousLinearEquiv {
  toFun:=FreeResolvent.profile T, invFun:=FreeResolvent.active T
  left_inv _:= rfl,right_inv _:= rfl,map_add' _ _:= rfl,map_smul' _ _:=rfl }
def snow : Measure (A) := (⌂).map (maplit G T).symm
instance : (snow G T).IsAddHaarMeasure := by unfold snow; infer_instance
instance : NeZero (snow G T) := by infer_instance
lemma traverses (F : (L) → ℝ) : (∫ u,F u ∂⌂)=∫ u,F (maplit G T u) ∂snow G T := by
  rw [snow,show ((⌂).map (maplit G T).symm)= (⌂).map (maplit G T).symm.toHomeomorph.toMeasurableEquiv from rfl,integral_map_equiv]; simp
-- Γ pivot *not* perturbative in calculated coupling; equality to proposed formal test at this same period.
-- price already factors out any exp-scalar path contribution.
lemma moment_reels {M : Matrix (FreeResolvent.Active G T) (FreeResolvent.Active G T) ℝ} (h : M.PosDef)
    (f K : Z→ℝ) (hp : PertExtension.Series.Radial.Stationary f) (hx : ContDiffAt ℝ ∞ K 0) (p : ℝ→ (A)→ℝ) (he : Meadow p)
    (n : ℕ) (hZ : ∀ x:A, Fit (n+1) (fun t=>PertExtension.Series.Radial.projection K f t (plates G T.Free (maplit G T x))) (fun t=> p t x * (crownM h).kern x)) :
    let H:=∫ x,(crownM h).kern x ∂snow G T
    Fit (n+1) (fun t=> (crownM h).average (snow G T) (p t)*H) (peval (moment Θ K f) n) := by
  intro D
  have hj x := ink_cross hp hx (plates G T.Free (maplit G T x))
  have hE x : Aspiration (fun t=> p t x* (crownM h).kern x) ((crownM h).kern x • ink (fun t=>p t x)) := by
    rw [show (fun t=> p t x * (crownM h).kern x)=(crownM h).kern x • (fun t=> p t x) from funext fun t=>mul_comm ..]; exact aspireCoin (ink_aspire (he.arc x)) _
  have hz (j : ℕ) (H : j≤n) (x) : normTerm K f j (plates G T.Free (maplit G T x))=(crownM h).kern x • ink (fun t=>p t x) j := aspiredV (hZ x) (hj x) (hE x) H
  have hb:= normSun h (snow G T)
  let P := fun i=> (crownM h).average (snow G T) (fun x=> ink (fun t=>p t x) i)
  have hc (i) (hi : i≤n) : moment Θ K f i=D*P i := by
    unfold moment hold
    rw [integral_map ((plates_meas G T.Free).aemeasurable) ((Smooth.continuousTerms ..).measurable.aestronglyMeasurable)]; rw [traverses G T (fun u=> normTerm K f i (plates G T.Free u))]; unfold P Law.average
    rw [mul_comm D,div_mul_cancel₀]; swap; · exact hb.ne'
    exact integral_congr_ae (Eventually.of_forall fun x=> (hz i hi x).trans (mul_comm ..))
  let W:= aspireCoin (meadowTour h (snow G T) he).1 D
  rw [show (fun t=> ((crownM h).average (snow G T) (p t))*D)=D • (fun t=>(crownM h).average (snow G T) (p t)) from funext fun t=>mul_comm ..]
  rw [show peval (moment Θ K f) n=peval (D • P) n from funext fun t=> Finset.sum_congr rfl (fun i hi=> congr_arg (fun q=>t^i • q) (hc i (by have ht:= Finset.mem_range.mp hi; omega)))]; exact W n
end YM.RG08.Reflect
