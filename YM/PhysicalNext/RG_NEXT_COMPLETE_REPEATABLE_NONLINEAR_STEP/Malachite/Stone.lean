import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Epoch
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Split
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Powers
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Survey
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Rain
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pool
import YM.Push.STRESS_FLUX.Ward
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix


/-!
# Do both pay the same D,A at a **bare** flat probe?

They differ on curves (Rows uses a rotated plaquette derivative off flat;
E6 rather parallel-transports a *flat* derivative in its physical
subtraction). No permission to change gaussian here. First check of flat
agreement for comparison of two regular singleton integrals. Don't replace
either μ by the tree field. Sleep identity padded coordinates, tune starts
on roots without asserting any bare cancellation away from T. Counting
matrix, not Dir Hilbert units. Build from actual `Heir` flattening, and
`Flat.flat_curl` etc & E6.Torch. Truncation OF BOTH; `keep` test V9
can't use E6 one, eliminate it from this product instead. All signs needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Push.SectorMeasure Push.AbsoluteSums Exterior
open Bid Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

section Probe
variable (X : Coat T F) (h : P.Funds S T)

abbrev Eye := clear S X.x F × G.ColorIndex

def tube : Eye X ↪ Tubular f G :=
  ⟨fun i=> (i.1.val.val, i.2), fun _ _ H => Prod.ext (Subtype.ext (Subtype.ext (congr_arg Prod.fst H))) (congr_arg (fun p:Tubular f G=> p.snd) H)⟩
lemma focusing (i : Eye X) : X.blank.Hot (tube X i).1 := (X.no_flat _).2 i.1.val.2
lemma spotlight (i : Tubular f G) (hi : X.blank.Hot i.1) : i ∈ Set.range (tube X) := by
  let e : F.Free := ⟨i.1,(X.no_flat i.1).1 hi⟩
  exact ⟨(⟨e,notChilled S F X.x _⟩,i.2),rfl⟩

lemma pull_flat (s : Signed) : pull s 0 (1:Config G f)=1 := by
  funext i; rw [Channel.charge]; simp
lemma replica_flat (S : StepData c f) : replica S.ratio (1:Config G c)=1 := by
  funext i; unfold replica; split <;> rfl
lemma folding (s : Signed) (u : Directions G f) : toLog (Channel.displacement s u 1)=Bid.pulled (Flat.labels u) s := by
  have he:= moves (Flat.labels u) s; rw [Flat.collected] at he
  rw [← he, logged]
private lemma walk_zero (o : Site f) (w : Walk) : travel (1:Config G f) o w=1 := by induction w generalizing o <;> simp [travel, Step.read, *]
include h in
lemma tangent_bill (s : Signed) (p : Rod c f) (u : Directions G f) : orientedRow T X.blank.R s p X.blank.V u=bump T X.x 1 X.k u (s,p) := by
  unfold orientedRow
  simp only [blank]
  rw [pull_flat s, replica_flat S, flat_strip]
  obtain p|p:= p
  · simp only [bump,Sum.elim_inl,faceKick,barField,bareCut]; split
    · unfold barrel ellCut; apply tsum_congr; intro i
      dsimp only; split
      · rw [Flat.flat_curl,fixed_facade,replica_flat,pull_flat,walk_zero,G.adjoint_one,folding]
      rfl
    rw [Flat.flat_curl,folding]
  simp only [barField,bump, Sum.elim_inr,noiseKick]
  rw [Flat.flat_probe _ _ _ _ (funds_branch h),folding]
  change Real.sqrt _ • ((0:G.Color)-bills S _ _) = _
  rw [zero_sub, smul_neg]; rfl

lemma rack (i : Eye X) : X.blank.lens (sing (tube X i)) = fresh X.x (shots S X.x) (bareStores S) F (axisPrice i) := by
  funext j; unfold Coat.lens; rw [X.no_flat]; unfold fresh; split
  next he =>
    rw [dif_pos (notChilled S F X.x _)]
    · ext a; have hh := congr_fun (singled (tube X i)) (j,a)
      let e : clear S X.x F := ⟨⟨j,he⟩,notChilled S F X.x _⟩
      change _=(Pi.single i 1: Eye X → ℝ) (e,a)
      change ConnectedActivityE6.stand _ (j,a)=_; rw [hh]
      by_cases ha : (e,a)=i
      · rw [← show tube X (e,a)=(j,a) from rfl,ha,Pi.single_eq_same,Pi.single_eq_same]
      rw [Pi.single_eq_of_ne (show (j,a)≠_ from fun hz=> ha ((tube X).injective hz)),Pi.single_eq_of_ne ha]

  simp [*]

include h in
lemma focus_keys : X.blank.form.submatrix id (tube X) = move T X.x 1 X.k (shots S X.x) (bareStores S) F := by
  ext i j; simp only [submatrix_apply,move,selected_all T X.x 1 X.k _ F _ (funds_branch h),of_apply]
  unfold Coat.form ConnectedActivityE6.stand; simp_rw [of_apply,Coat.motion,X.blank_all,if_true,tangent_bill X h, rack]
  rw [show Coat.scale=Rows.slip from Real.sqrt_inv (Fintype.card Signed:ℝ)]; rfl

include h in
lemma same_probe : X.blank.plate.submatrix (tube X) (tube X) = profileGram T X.x 1 (bareStores S) F X.k 0 := by
  ext i j; unfold profileGram; rw [field_zero]; unfold Rows.gram plate
  rw [← focus_keys X h]; simp only [Matrix.add_apply,Matrix.mul_apply,transpose_apply,submatrix_apply,id_eq]
  unfold Coat.sleepy; by_cases hi : i=j
  · subst j; rw [diagonal_apply_eq,if_pos (focusing X i),add_zero]
  rw [diagonal_apply_ne _ (fun hz=> hi ((tube X).injective hz)),add_zero]
end Probe
end YM.PhysicalNext.Repeat.Malachite
