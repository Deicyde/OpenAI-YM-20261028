import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Monitors
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ParcelBill
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Vault
import YM.Next.PHASE.Assembly
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# Completing centered square vs. exponent telescope

Keep M and complete identity covariance at unintegrated positions; Z even there. To allow
local charges never vary that baseline during `pane` applications. `hugePower` required
on actual center square.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Aff Aff.Mint Laps Wages
open Centered Centered.Till  Footprint Paths   Mixed  
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x W : ℝ} {A : Stores S}
    {F : Forest S.ratio}

section sums

variable (B : Pos S → ℝ)
def line (i : Rack S) := i.2.elim (fun p => ∑ s : Bool,B (i.1,Sum.inl (p,s)))
    (Sum.elim (fun p => B (i.1,Sum.inr p)) (fun _ => 0))
lemma costLine : ∑ i : Rack S, line B i=∑ i,B i := by simp only [Fintype.sum_prod_type,line,Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr,sum_const_zero,add_zero]
end sums

-- foreclosed rows even when radius connection
section rows
variable (Y : Mint T F A x) {P : Teller G} (hT : P.Funds S T)

lemma shuts (g : ArrayR G f) (p : Pos S) (he : p ∉ choosing A (radiusB x)) : descend (Y.actions g) p = 0 := by
  ext j
  change Y.actions g (p,j)=0
  simp [actions,Matrix.mulVec,dotProduct,D,Dmat,origin,zeroed,he]

include hT in
lemma assembled (g : ArrayR G f) : (∑ i,backs Y g i) = dotProduct (Y.actions g) (Y.actions g)/2 := by
  let B p := squareOf (descend (Y.actions g) p)
  have ht (p : Pos S) (hp : p∈choosing A (radiusB x)) : B p = Aff.weight*sqref T x Y.k p Y.V (Y.road g) := by
    unfold sqref B squareOf; rw [roads Y g p hp hT, norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt weight_pos.le]; ring
  have hV (p : Pos S) (hp : p∉choosing A (radiusB x)) : B p=0 := by unfold B squareOf; rw [shuts Y g p hp]; simp
  have he i : backs Y g i=line B i := by
    rcases i with ⟨s,i|i|i|i⟩
    · unfold backs bank line; simp only [Sum.elim_inl]; split
      next h => unfold crownF; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (ht (s,Sum.inl (_,i))
        (mem_filter.mpr ⟨mem_univ _,h⟩)).symm
      next h => exact (Finset.sum_eq_zero fun m _ => hV (s,Sum.inl (i,m)) (fun hp => h ((mem_filter.mp hp).2))).symm
    · unfold backs bank line; simp only [Sum.elim_inr,Sum.elim_inl]; split
      next h => exact (ht (s,Sum.inr i) (mem_filter.mpr ⟨mem_univ _,h⟩)).symm
      next h => exact (hV (s,Sum.inr i) (fun hp => h (mem_filter.mp hp).2)).symm
    · unfold backs bank line; simp
    unfold backs bank line; simp
  simp_rw [he,costLine]; unfold B squareOf; rw [← Finset.sum_div,descend_sq]





def march (T : Tube G S) (x : ℝ) (F : Forest S.ratio) := Real.log (flatReference T x F).det




lemma βhunt (β : ℝ) (h : 0<β) : power β > 0 ∧ β * power β^2=1 := by
  unfold power
  have hh := Real.sqrt_pos.mpr h
  constructor; positivity
  field_simp; rw [Real.sq_sqrt h.le]

include hT



end rows
end YM.AnalyticNext.ConnectedActivity.Cab
