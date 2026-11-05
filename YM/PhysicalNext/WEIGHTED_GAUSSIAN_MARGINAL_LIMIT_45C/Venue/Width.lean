import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Space

/-!
# Oriented axial cover for custom venue width and prices of stands

One gauge expression on all reads which may be many radiusB's away
(κ fixed pre-stage). Do NOT seek Hart status on a different threshold.
Actual logs still fit a constant times clearanceFare at all these
eligible reports (both columns and frames). All x-delays after P,Pt
and requested tier, not loaned at old size. Multiple centers used for
comparing endpoint data locally do NOT change V' reads. Original cleared
mask must thus be appropriately far away everywhere. See there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Venue
open AnalyticBridge.LocalGaussianLaws
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff



section orbit
variable {G : Gauge} {c f : Side} (S : StepData c f) (r : ℕ) (x : ℝ)

def orbit (r : ℕ) := ((r:ℝ)+1)^5

 -- sequencing ambiguous

end orbit



-- renew the *original-cost* neighborhood prerequisites at the one column
-- of interest. For the nonextended tier may have to use origin even then.
theorem relocate (r : ℕ) {G : Gauge} {x t : ℝ} {c f : Side} {S : StepData c f} (A : Stores S) (o : Site c)
    (hA : Clears A x o (vista r x)) (V : Config G c) (v : Dir G c) (hv : AgreeNear id o (vista r x) V (represent v))
    (hp : paid S (replica S.ratio V) o (vista r x) t) (p : Site c) (h : separation o p ≤ vista r x/4) :
    ∃ y : Site c, separation y p≤ radiusB x/4 ∧ Clears A x y (radiusB x) ∧
      AgreeNear id y (radiusB x) V (represent v) ∧ paid S (replica S.ratio V) y (radiusB x) t := by
  suffices q : ∃ y, separation y p ≤ radiusB x/4 ∧ separation o y+radiusB x≤vista r x by
    obtain ⟨y,he,hr⟩ := q
    have hh (s : Site c) (h : separation y s ≤ radiusB x) : separation o s ≤ vista r x :=
      (separation_triangle o y s).trans ((Nat.add_le_add_left h _).trans hr)
    refine ⟨y,he,?_,fun i hi => hv i (hh _ hi),fun i hi=>hp i (hh _ hi)⟩
    intro hz
    obtain ⟨z,hz' ,hx⟩ := halo_spec.mp hz
    apply hA; apply halo_spec.mpr; refine ⟨z,hz',?_⟩
    have hf:= separation_triangle z y o; rw [separation_comm y o] at hf; omega
  cases r with
  | zero => exact ⟨o,h,by simp [vista_zero]⟩
  | succ n =>
    have hc : 2*radiusB x ≤ vista (n+1) x := by
      rw [vista_eq]; gcongr; omega
    exact ⟨p,by simp, by omega⟩
end YM.PhysicalNext.WeightedGaussianMarginal45C.Venue
