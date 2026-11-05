import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.MultiNext.VACUUM_STABILITY.Earning.Stage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Searchlight
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Line
import YM.Planned.ATOM_REGULAR_ESTIMATE.LargeL

/-!
# Extent ownership for testing returning-E through all W gauges of ROOT

`oarsD` bought independently of $Φ$ composition. Every incoming-k (
not to be confused with precision); every output site x in footprint. Use
Phase family V.Stroke prior to query. No controls needed if trajectories too
strong until cropping by *full* sites. Apply only after mask-aware `Regular`
 releases, not cutting Γ masks. Open shrink chart by timeScale if another
income header has a smaller C.v.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell  Poll Pond Silica Eider Metric Set Gaussian Tablet Quill  
open WardBin.Lies
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B : BudgetPoint} {Y : Support c} {n p j : ℕ} {v r z : ℝ}
section power
-- normalization cap on WHOLE stencil, rank height clock.
def canopyW (G : Gauge) (L : Side) (p : ℕ) (x : ℝ) := 2*fiery G x L * (1+(radiusD x:ℝ))^p
lemma roof_rate (G : Gauge) (L : Side) (p : ℕ) : Rate G L (-(1/2)) (canopyW G L p) := by
  have hp:= Rate.radius_price (G:=G) (L:=L)
  have hh:Rate G L 0 (fun x=> (radiusD x:ℝ)):= by
    unfold radiusD; push_cast
    exact Rate.add (by simpa only [zero_add] using! hp.mul (((hp.mul_left 4).add (Rate.const 2)))) (hp.mul_left 2)
  simpa only [zero_mul,add_zero] using! (((Rate.flame (G:=G) (L:=L)).mul_left 2).mul (((Rate.const 1).add hh).pow p))
lemma pacing (U : Directions G c) (D : Support c) (rem : ∀ i, i.1∉D → U i=0) (K : BudgetPoint) {o} (ho : o∈D)
    (he : K.power=p) (h : K.dirBound o U) (x : ℝ) (L : Side) (hg : coverNumber (radiusB x) D ≤ radiusB x) (hb : K.threshold ≤ 2 * fiery G x L) : ‖U‖ ≤ canopyW G L p x := by
  have hZ : 0≤2*fiery G x L:= (K.threshold_pos.trans_le hb).le
  refine (pi_norm_le_iff_of_nonneg (show 0≤ canopyW G L p x by unfold canopyW; positivity)).mpr fun i=> ?_
  by_cases hi : i.1∈D
  · have hY : separation i.1 o ≤ radiusD x := (Corona.extent D (radiusB x) hi ho).trans (by unfold radiusD; gcongr)
    apply (h i).trans; unfold canopyW; rw [← he]
    gcongr
  rw [rem i hi,norm_zero]; unfold canopyW; positivity
end power

section journeys
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma impulse {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (L : E →L[ℝ] T) (hp : ‖L‖≤1) (f : T→ Config G c) (h : Mode f (L 0) p z) :
    Mode (f ∘ L) 0 p z := by
  refine ⟨h.pos,fun i=> ?_⟩; have he:= Brush.reading L (h.atLink i) hp; rw [mul_one] at he; exact he
lemma oarsD (h : March.Sailor G v z p) (A : Slab G c j) (hp : ∀ i, ‖A i‖≤v) (B : Fin j → E→L[ℝ] ℝ) (hb : ∀ i,‖B i‖ ≤ 1)
    (f : E → Config G c) (hf : Mode f 0 p r) : Mode (fun u=> chug j (f u) (fun i=> (B i u) • A i)) 0 p (r+j*z) := by
  induction j generalizing f r with
  | zero=> simp only [chug,Nat.cast_zero,zero_mul,add_zero]; exact hf
  | succ j ih=>
    let L : E →L[ℝ] (E × ℝ) := (ContinuousLinearMap.id ℝ E).prod (B 0)
    have hL: ‖L‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by
      rw [one_mul]; exact max_le (le_refl _) ((ContinuousLinearMap.le_opNorm (B 0) i).trans (mul_le_of_le_one_left (norm_nonneg _) (hb 0)))
    let f' x:= increment (f x) (B 0 x • A 0)
    have he:Mode f' 0 p (z+r) := by
      apply impulse L hL (fun v:E×ℝ => increment (f v.1) (v.2 • A 0)) -- edit
      rw [map_zero]; exact h.stroke c _ (hp 0) E f 0 _ hf
    have hv:= ih (Fin.tail A) (fun i=>hp i.succ) (fun i=>B i.succ) (fun i=> hb i.succ) f' he
    rw [show r+(↑(j+1:ℕ):ℝ)*z=(z+r)+j*z by push_cast; ring]; exact hv
lemma oars_j (h : March.Sailor G v z p) (U : Config G c) (A : Slab G c j) (hp : ∀ i, ‖A i‖≤v) :
    Mode (journey U j A) 0 p (j*z) := by
  let L i : Panels j →L[ℝ] ℝ:= ContinuousLinearMap.proj i
  have he:= oarsD h A hp L (fun i=> ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (norm_le_pi_norm x i).trans_eq (one_mul _).symm)
    (fun _=>U) ⟨(le_refl (0:ℝ)),fun i=> a_oneB G _ le_rfl⟩
  rw [zero_add] at he; exact he
end journeys

lemma aura (G : Gauge) (P : Teller G) (L : Side) (p n:ℕ): ∃ V:ℝ→ℝ, Rate G L (-(1/2)) V ∧ (∀ x,0≤V x) ∧
    ∀ (x:ℝ) (c f:Side) (S : StepData c f) (T : Tube G S), Room P S T x→ S.patch.L=L → ∀ B: BudgetPoint, B.power=p → B.threshold=temp x →
      ∀ (U : Config G c) (j:ℕ) (A: Slab G c j), (∀ i, ‖A i‖≤ canopyW G L p x) → j≤n → Mode (journey U j A) 0 n (V x) := by
  obtain ⟨Y,hY,H⟩:= March.oar G n
  let u:= canopyW G L p
  have hv x : 0≤ Y*u x:= mul_nonneg hY.le (mul_nonneg (mul_nonneg zero_le_two (temp_nonneg _)) (pow_nonneg (by positivity) _))
  refine ⟨fun x=> n*(Y*u x),((roof_rate G L p).mul_left Y).mul_left _,fun x=> mul_nonneg (Nat.cast_nonneg _) (hv x),fun x c f S T hr h B hp hb U j A hA hJ=> ?_⟩
  have hZ': 0≤ u x:= nonneg_of_mul_nonneg_right (hv x) hY
  have hh:= oars_j (c:=c) (show March.Sailor G (u x) (Y*u x) n from ⟨fun c=> H c (u x) hZ'⟩) U A hA
  exact ⟨mul_nonneg (Nat.cast_nonneg n) (hv x),fun i=> (hh.atLink i).climb le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hJ) (hv x))⟩
end YM.PhysicalNext.Repeat.Brim
