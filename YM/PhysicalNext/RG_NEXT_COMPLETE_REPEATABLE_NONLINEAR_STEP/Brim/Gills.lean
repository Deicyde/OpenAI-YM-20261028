import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Searchlight
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Bass

/-!
# Per-site rank N from E6 allowance (true seed footprint)

Calculate with potential accesses not just active queries. θ completions,
 uses rank effects from layout, even with sparse Y. Heat position in authentic
 arms. Don't convert Cover hypotheses under Fake kernel without adequacy; here
 moving poles disjoint from actual X seeds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell  Poll Pond   Metric Set Gaussian Tablet Quill  
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {Y : Support c} {E : Support f} {B B' : BudgetPoint} {n p j : ℕ} {v b r q η z : ℝ} {X : Coat T F} {L : Side}
variable {I:Type} [Fintype I] [DecidableEq I] (a : Museum F X.x (bareStores S) E Y I) {o : Site c} (hz : o∈Y) (hy : coverNumber X.B Y ≤ X.B)
variable {C : Libretto G n} {D : Record}
include hy a hz
omit [Fintype I] [DecidableEq I] in
lemma far (i : I) : separation (pole X a i) o ≤ radiusD X.x:= (Corona.extent Y X.B
    (a.stores i (halo_subset _ _ (Finset.mem_singleton_self _))) hz).trans (by change coverNumber X.B Y * _ + _ ≤ X.B*(4*X.B+2)+2*X.B; gcongr)

omit [DecidableEq I] in
lemma thrives : Fintype.card (I×G.ColorIndex) ≤ (Animals.ballCost (radiusD X.x))*tubularPrice G S.patch.L := by
  let S' := withinH (along (G:=G) S) o (radiusD X.x); let b:=scoop X a; have he (i) : b i∈S':= (joins ..).mpr ((separation_comm ..).trans_le (far a hz hy i.1))
  calc
    _ = (Finset.univ.map b).card := by simp
    _ ≤ S'.card := Finset.card_le_card fun i h=> by obtain ⟨k,hh,rfl⟩:= Finset.mem_map.mp h; exact he _
    _ ≤ _ := count_near (Census.entering S) ..

lemma illum (hr : Healthy B.threshold Y X.V) (h : Plays C D B B' P T X.x) : Carillon (lamp9 X a) X.V n B o D.K D.Z B'.threshold (radiusD X.x) := by
  have he := h.rehearsed.temp_eq; unfold lamp9; rw [a.twilight_price (k:=X.k) h.bulletin (he ▸ hr)]
  refine h.budget _ _ _ _ _ _ _ (fun i=> far a hz hy i.1) ?_
  rw [he]; rfl
omit hy hz a [Fintype I] [DecidableEq I]
def grade (G : Gauge) (L : Side) (x : ℝ) := ((Animals.ballCost (radiusD x)):ℝ)*tubularPrice G L
lemma spanDO (G : Gauge) (L : Side) : Rate G L 0 (fun x=> (radiusD x:ℝ)):= by
  have hp := Rate.radius_price (G:=G) (L:=L); unfold radiusD; push_cast
  exact Rate.add (by simpa only [zero_add] using! hp.mul (((hp.mul_left 4).add (Rate.const 2)))) (hp.mul_left 2)
lemma graded (G : Gauge) (L : Side) : Rate G L 0 (grade G L) := by
  have h:= spanDO G L
  have he x : grade G L x=((radiusD x:ℝ)+(radiusD x:ℝ)+1)^4*tubularPrice G L:= by unfold grade Animals.ballCost; push_cast; rfl
  rw [funext he]
  apply Rate.mul_right
  simpa only [zero_mul] using! ((((h.add h).add (Rate.const 1))).pow 4)
lemma can_pay (G : Gauge) (L : Side) (n p : ℕ) (D : Record) : Rate G L 0 (fun x=> Heir.canopy D.Z (radiusD x) p n) := by
  simpa only [zero_mul] using! (((((Rate.const 1).add (spanDO G L)).pow p).pow n).mul_left D.Z)
end YM.PhysicalNext.Repeat.Brim
