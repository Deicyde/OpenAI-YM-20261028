import YM.Further.CURVED_GAUSSIAN_JETS.Fares

/-!
# Two-step chart in a patch gauge for the true predictor
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {S : StepData c f} {F : Forest S.ratio} {V : Config G c} {U : Config G f} {j k p : ℕ} {K : ℝ} (r : Ratio c f) (h : Site f → G.El)

def spin (v : Directions G f) : Directions G f := fun b=> G.adjoint (h b.1) (v b)
lemma incr_gauged (u : Config G f) (v : Directions G f) : gauge h (increment u v) = increment (gauge h u) (spin h v) := by
  funext b; unfold Lattice.gauge spin increment; rw [ProjectorNext.Equivariance.exp_adjoint]; group
lemma incr_copied (u : Config G c) (v : Directions G c) : replica r (increment u v) = increment (replica r u) (linearCopy r v) := by
  funext b; unfold replica linearCopy increment; dsimp only; split_ifs <;> simp
lemma slab_shift (x : Slab G c j) : gauge h (replica r (chug j V x)) = chug j (gauge h (replica r V)) (fun i=>spin h (linearCopy r (x i))) := by
  induction j generalizing V with | zero => rfl | succ j ih => rw [chug,chug,ih,incr_copied,incr_gauged]; rfl
lemma slab_agreement (u v : Config G f) (x : Slab G f j) (i : Bond f) (he : u i=v i) : chug j u x i=chug j v x i := by
  induction j generalizing u v with | zero => exact he | succ j ih => apply ih; rw [increment,increment,he]

abbrev Extended (G : Gauge) (c f : Side) (j : ℕ) := joint G c f j × Dir G f

def cruise (j : ℕ) (x : Extended G c f j) := increment (chug j (represent x.2) (fun i=>spin h (linearCopy r (x.1.1 i)))) (spin h x.1.2)
lemma cruise_agrees (V : Config G c) {z : Dir G f} (y : Site c) (a : ℕ) (he : AgreeNear r.parent y a (gauge h (replica r V)) (represent z)) (x : joint G c f j) : AgreeNear r.parent y a (gauge h (twoStep r V j x)) (cruise r h j (x,z)) := by
  rw [twoStep,incr_gauged,slab_shift]; unfold cruise; exact fun i hi=> congr_arg (G.lieExp (spin h x.2 i) * ·) (slab_agreement _ _ _ _ (he i hi))
lemma cruise_back (V : Config G c) {z : Dir G f} (y : Bond c) (l : S.Choices) (hS : S.patch.Branches S.kernel G) (he : AgreeNear S.ratio.parent y.1 (predReach S.patch) (gauge h (replica S.ratio V)) (represent z)) (x : joint G c f j) :
    S.prediction (twoStep S.ratio V j x) l y = (h (S.ratio.embed y.1))⁻¹ * S.prediction (cruise S.ratio h j (x,z)) l y * h (S.ratio.embed (y.1+Lattice.step y.2)) := by
  rw [← prediction_near_eq hS (gauge h _) _ l y (cruise_agrees S.ratio h V _ _ he x),predicted hS, Lattice.gauge]; dsimp only [Function.comp_apply]; group

private lemma segment (j : ℕ) {x : Extended G c f j} (hx : ‖x‖ ≤ 1) : Views (fun y : Extended G c f j=>collect G y.2) k x := by
  intro i
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 1 f=>G.Color) (i.1,coord i.2) ∘L ContinuousLinearMap.snd ℝ (joint G c f j) (Dir G f)
  exact linear_fare L (fun y=> (norm_le_pi_norm y.2 _).trans (le_max_right ..)) hx
lemma Views.spun {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X} {L : X→ Directions G f} (he : Views L k x) : Views (fun y=>spin h (L y)) k x := by
  intro i; rw [← one_mul (1:ℝ)]
  exact Allows.linear ((G.adjoint (h i.1)).toContinuousLinearMap) (he i) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=> (G.norm_adjoint ..).trans_le (one_mul _).symm.le))
lemma cruise_input (hk : ExpReceipt G k K) (hj : j ≤ k) : Push.Uniform.Inputs (cruise r h j) k (fullCost G k K) := by
  have hz : cruise r h j 0=1 := by
    unfold cruise
    rw [Prod.snd_zero,link_one,show (fun i=>spin h (linearCopy r ((0:Extended G c f j).1.1 i))) = 0 by ext; simp [spin,linearCopy],chug_zero,
      show spin h ((0:Extended G c f j).1.2)=0 by ext; simp [spin]]; exact G07.at_zero_increment 1
  refine ⟨hz,full_nonneg _ _ (Exp_nonneg hk),fun i x hx=>?_⟩
  let a := ContinuousLinearMap.snd ℝ (Slab G c j) (Directions G f) ∘L ContinuousLinearMap.fst ℝ (joint G c f j) (Dir G f)
  let b := ContinuousLinearMap.fst ℝ (Slab G c j) (Directions G f) ∘L ContinuousLinearMap.fst ℝ (joint G c f j) (Dir G f)
  have ha := (fields (L:=a) (fun y=> le_trans (le_max_right ..) (le_max_left ..)) hx).spun (k:=k) h
  have hb i := ((slabs (L:=b) (fun y=> le_trans (le_max_left ..) (le_max_left ..)) hx i).copy (k:=k) r).spun h
  have he := (((seen_const (1:Config G f)).advance hk (segment _ hx)).jogs hk hb).advance hk ha
  apply (he i).mono
  rw [fullCost, show k+2=1+k+1 by omega,pow_succ,pow_add,pow_one,mul_assoc,mul_assoc]; have he := gas_one (Exp_nonneg hk) k; have := zero_le_one.trans he; gcongr; exact mul_nonneg this (norm_nonneg _)
end YM.Further.CurvedGaussianJets.ChangeV
