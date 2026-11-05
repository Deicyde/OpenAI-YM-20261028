import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Idyll

/-! # Script compatible with Heir (authored on T, R from full step)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle 
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R) (D : Record) (q' κ χ : Chi) (ε : ℝ)

lemma billboard (h : Q.halo+5 ≤ n) (i : ℕ) : Walled S (R.activities.reg i).support (plate H i).support x n :=
    (Footprint.inspected_price S.ratio Q.halo _ _ (paidB H)).trans (Corona.halo_mono (Nat.mul_le_mul_right _ h) (Finset.Subset.refl _))

def scroll (h : Q.halo+5≤n) (i : ℕ) : Script G S (R.activities.reg i).support (plate H i).support n x where
  Tag := Greenbelt.Reserve S × S.Choices
  Keys p:= Key (R.activities.reg i).support x (Greenbelt.allot p.1)
  chart _ := bareStores _
  forest p:=Greenbelt.allot p.1
  θ p := p.2
  fits p:= mapcase H i (Greenbelt.allot p.1)
  profile _:= Baffle.magic D R.p R.beta κ
  moves _:= guard_natural _ _
  coefficient _:= (Fintype.card (Greenbelt.Reserve S × S.Choices):ℝ)⁻¹
  admissible:= by
    letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    let t:ℝ:= Fintype.card (Greenbelt.Reserve S × S.Choices)
    have ht:0<t:= Nat.cast_pos.mpr Fintype.card_pos
    rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; change t*|t⁻¹|≤ _; rw [abs_of_pos (inv_pos.mpr ht),mul_inv_cancel₀ ht.ne']
  fields := billboard H h i

lemma arithmetic (h : Q.halo+5≤n) (i : ℕ) : announced H D q' κ ε i= (scroll H D κ h i).tuning (gStep R.beta) q' ε (R.activities.E i) T := by
  funext x; rw [Script.tuning,Finset.sum_apply]; unfold announced likely
  let A:= Greenbelt.Reserve S; let X := A×S.Choices
  letI : Fintype A:= by unfold A; infer_instance
  let t : ℝ:= Fintype.card X; let p:ℝ:= Fintype.card A; let y:ℝ := Fintype.card S.Choices
  let f (j:A)(h:S.Choices):=aria H D q' κ ε i (Greenbelt.allot j) h x
  change p⁻¹ * (∑ j:A, y⁻¹*∑ h,f j h)=∑ k:A× S.Choices,t⁻¹*f k.1 k.2
  rw [← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_prod_type]; rw [show t=p*y from by unfold t p y X; rw [Fintype.card_prod,Nat.cast_mul], mul_inv,mul_assoc]


end YM.PhysicalNext.Repeat.Brim
