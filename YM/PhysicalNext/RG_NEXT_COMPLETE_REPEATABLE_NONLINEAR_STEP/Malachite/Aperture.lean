import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Mineral
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization

/-!
# The column discrepancy between OUR two dry forecasts

They use DIFFERENT conventions of pads. Even here, no license to identify.
Test at b=0; sum true in-sector compression of full inverse, permissible
only with E6's direct sum at SLEEP coords. Do not pay (A_UU)⁻¹ as the
inverse of a covariance on U without this type of lemma! Keep exact prices.
Covariances even here are priced **by the error**, not by agreement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

section storm
variable (X : Coat T F) (h : P.Funds S T) {η r Q d v s l M : ℝ} {m n : ℕ}
variable (hX : Allow X.blank.plate (along S) m η r Q)
  (hB : KernelJets n d v s l M (bareStores S) F T X.x 1 X.k 0)

-- true extension
include h hX
lemma ringD : X.blank.plate⁻¹.submatrix (tube X) (tube X)=(X.blank.plate.submatrix (tube X) (tube X))⁻¹ := by
  let A := X.blank.plate; let b:= tube X; let U:= A.submatrix b b; let V:= A⁻¹.submatrix b b
  have hz : U*V=1:= by
    rw [show (1:Matrix (Eye X) _ ℝ) = (A*A⁻¹).submatrix b b from by
      rw [show A*A⁻¹=1 from hX.initial.1]; exact (Matrix.submatrix_one _ b.injective).symm]
    ext i j; rw [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    change ∑ k:Eye X, A (b i) (b k) * A⁻¹ (b k) (b j)=_
    rw [← Finset.sum_map (f:=fun k=> A (b i) k * A⁻¹ k (b j))]
    refine Finset.sum_subset (Finset.subset_univ _) ?_; intro k _ hk
    have hv : ¬X.blank.Hot k.1:= fun he=> hk (Finset.mem_map.mpr (by obtain ⟨a,h⟩:= spotlight X k he; exact ⟨a,Finset.mem_univ _,h⟩))
    obtain ⟨a,v,H,-⟩:= h.feeds
    have he : A (b i) k=A k (b i):= congr_fun (congr_fun X.blank.toned _) _
    rw [he, show A k (b i)=(1:Matrix ..) k (b i) from X.blank.asleep k hv H _,Matrix.one_apply_ne (fun he:k=b i=> hv (he.symm ▸ (focusing X i))),zero_mul]
  have hp : U⁻¹*U=1 := (hX.sub b).initial.2.1
  change V=U⁻¹
  calc
    _ = U⁻¹*(U*V) := by rw [← Matrix.mul_assoc,hp,Matrix.one_mul]
    _ = _ := by rw [hz,Matrix.mul_one]

def notice := Wisps.front (bareStores S) F (G:=G) (x:=X.x)

def missPay (η r Q v M : ℝ) (m B : ℕ) := payE η r Q m * scraps η r Q m B+ M*Real.exp (-v*B)
include hB
lemma darkness (hd : 0<d) :
    Control.Price (notice X) (notice X) ((drills X 0).submatrix (tube X) (tube X)-looks X 0) 0 (missPay η r Q v M m X.B) := by
  have hk := hB.closenessJets 0 le_rfl
  open FreeResolvent.TestD in simp only [shift_zero,show FreeResolvent.TestD.drain 0=1 by simp [FreeResolvent.TestD.drain],one_pow,mul_one] at hk
  let a:= notice X; let b := M * Real.exp (-v*X.B); let H := X.blank.plate.submatrix (tube X) (tube X); let U := looks X 0
  have hx : U=pickedPi (bareStores S) F T X.x 1 X.k 0 0 := by unfold U looks; rw [map_zero]
  have he' : Price a a (U-H⁻¹) d b:= by
    unfold H; rw [same_probe X h,hx]
    have hs := polar_schur hk; exact ⟨hs.rows.bound,hs.cols.bound⟩
  let L:= (drills X 0).submatrix (tube X) (tube X)
  have hz : Price a a (L-H⁻¹) (retain η r Q) (payE η r Q m * scraps η r Q m X.B) := by
    unfold H; rw [← ringD X h hX]; unfold L drills gem dry; rw [Work.G07.at_zero_increment]; let t:=tube X
    have he := hX.breach X.blank.shutter
    change Price a a (X.blank.kernelA.submatrix t t-X.blank.plate⁻¹.submatrix t t) _ _
    exact ⟨he.1.restrict t t, he.2.restrict t t⟩
  change Price a a (L-U) _ _; rw [show L-U=(L-H⁻¹)+-(U-H⁻¹) from by abel]
  exact paid_add (increase hz hX.weather.1.le le_rfl) (increase (spent_neg he') hd.le le_rfl)

-- no license for covariance being transported yet; cost the dry probe
omit h hB hX in
def optics (u : Directions G c) := pickedCov (bareStores S) F T X.x 1 X.k (reader G c u)
lemma night (hd : 0<d) : Price (notice X) (notice X) ((stoneC X 0).submatrix (tube X) (tube X)-optics X 0) 0
      (missPay η r Q v M m X.B) := by
  let q := missPay η r Q v M m X.B
  have he := darkness X h hX hB hd
  let L:= (drills X 0).submatrix (tube X) (tube X); let U := looks X 0
  have hp := weighted_by (paid_add he (flipped he)) (1/2:ℝ)
  rw [abs_of_nonneg (show (0:ℝ)≤ 1/2 by norm_num), show (1/2:ℝ)*(q+q)=q from by ring] at hp
  have hL : (stoneC X 0).submatrix (tube X) (tube X)= (1/2:ℝ) • (L+ Lᵀ) := by ext i j; rfl
  have hz : optics X 0= (1/2:ℝ) • (U+Uᵀ) := picked_sym ..
  rw [hL,hz,← smul_sub, show L+Lᵀ-(U+Uᵀ)=(L-U)+(L-U)ᵀ from by rw [transpose_sub]; abel]; exact hp
end storm
end YM.PhysicalNext.Repeat.Malachite
