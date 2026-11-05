import YM.Pert.Parity.Branch
import YM.Pert.Parity.Readings
/-!
Symmetrize a finite determining list by pairing each Section with its column-reflected test. Since columns enter multilinearly **before** the test projection, use transformed inputs, not just a sign projection on frame parameters.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Pert.Parity
open Position Labels Full Filter Function Set Topology Maxwell Lattice
open scoped Topology Classical
variable {G : Gauge} (F : Frames G) (d : ℕ) {k : ℕ} (s : Fin k→Section F d)
local notation "S" => Section F d

def pick (v : Fin 2) : (Fin (k*2)→ℝ)→ₗ[ℝ] (Fin k→ℝ) := LinearMap.pi (fun i=>LinearMap.proj (finProdFinEquiv (i,v)))
variable {n : ℕ} (g : (Fin k→ℝ)→ₗ[ℝ] (Fin n→ℝ)) (J : Module.End ℝ (Fin n→ℝ))
def cutter := (2:ℝ)⁻¹ • ((g ∘ₗ pick 0) + (J ∘ₗ g ∘ₗ pick 1))
def paired := assemble F d (duo F d s) n (cutter g J)
variable {F d}
def report {m} (Q : Conditions F d m) (L a p t b) := chart Q (curve (finite Q L a) p t,b)
variable (F d)
local notation "raw" => assemble F d s n g
local notation "pairs" => paired F d s g J
lemma even_split (L m p t b) : report pairs L m p t b = (2:ℝ)⁻¹ • (report raw L m p t b + J (report raw L m p (-t) (twice F d b))) := by
  rw [report,report,report,paired,shift_meter,shift_meter,shift_meter]
  unfold cutter; rw [LinearMap.smul_apply,LinearMap.add_apply]; apply congrArg _; apply congr_arg₂ (·+·) <;> simp only [LinearMap.comp_apply,pick,LinearMap.pi_apply,LinearMap.proj_apply]
  · apply congrArg g; funext i
    change sample F d b L m p t (duo F d s (finProdFinEquiv (i,0))) = sample F d b L m p t (s i)
    rw [unshifted]
  apply congrArg J; apply congrArg g; funext i
  change sample F d b L m p t (duo F d s (finProdFinEquiv (i,1))) = sample F d _ _ m p _ (s i)
  have he := sample_switch F d s (twice F d b) L m p (-t) i
  simpa only [unshifted, twice_twice, neg_neg] using he.symm

def sanitary : Side := ⟨4,by decide⟩
theorem source_tends {m : ℕ} (g₁ : (Fin k→ℝ)→ₗ[ℝ] (Fin m→ℝ)) (b : Buffer F d) (p) :
    let Q := assemble F d s m g₁
    Tendsto (fun i=>report Q sanitary i p 0 b) atTop (𝓝 (chart Q (white Q,b))) := by
    intro Q; have h0 : Tendsto (fun i=>finite Q sanitary i 0) atTop (𝓝 (white Q)) := tendsto_pi_nhds.2 fun u=> by
      refine tendsto_pi_nhds.2 fun v=>?_
      exact Rig.zerothProfile _ _ _ (by decide) _ (s u).f ((s u).f).continuous ((s u).f).hasCompactSupport (s u).f.tsupport_subset
    simp only [report, curve_zero]; exact ((chart_diff Q).continuous.tendsto _).comp (h0.prodMk_nhds tendsto_const_nhds)
lemma white_split (b : Buffer F d) : chart pairs (white pairs,b) = (2:ℝ)⁻¹ • (chart raw (white raw,b) + J (chart raw (white raw,twice F d b))) := by
  have h : Tendsto (fun i=>report pairs sanitary i 0 0 b) atTop (𝓝 (chart pairs (white pairs,b))) := source_tends F d (duo F d s) (cutter g J) b 0
  refine tendsto_nhds_unique h ?_
  simp only [even_split, neg_zero]
  exact ((source_tends F d s g b 0).add (J.continuous_of_finiteDimensional.continuousAt.tendsto.comp (source_tends F d s g (twice F d b) 0))).const_smul ((2:ℝ)⁻¹)
lemma pairing_fair (hJ : ∀ u, J (J u) = u) : Fair pairs J where
  center := by
    rw [white_split,LinearMap.map_smul, map_add,hJ,map_zero, add_comm]
  mirrors L m p t b := (show report pairs L m p (-t) (twice F d b) = J (report pairs L m p t b) by rw [even_split,even_split,map_smul,map_add,hJ,neg_neg,twice_twice,add_comm])

variable {F d}
def thermometer (Q : Conditions F d n) : Buffer F d→L[ℝ] (Fin n→ℝ) := (fderiv ℝ (chart Q) (white Q,0)) ∘L ContinuousLinearMap.inr _ _ _
lemma thermometer_eval (Q : Conditions F d n) (b : Buffer F d) :
   HasDerivAt (fun t:ℝ=>chart Q (white Q,t•b)) (thermometer Q b) 0 := by
  let f (t : ℝ) := (white Q,t•b)
  have h : HasDerivAt f (0,b) 0 := by
    convert! ((hasDerivAt_const (0:ℝ) (white Q)).prodMk ((hasDerivAt_id (0:ℝ)).smul_const b)) using 1
    simp
  have z : f 0=(white Q,0) := by simp [f]
  have ht := (((chart_diff Q).differentiable (by simp)) (white Q,0)).hasFDerivAt
  unfold thermometer
  exact (show HasFDerivAt (chart Q) (fderiv ℝ (chart Q) (white Q,0)) (f 0) by change HasFDerivAt _ (fderiv ℝ (chart Q) (white Q,0)) (f 0); rw [z]; exact ht).comp_hasDerivAt (l:=chart Q) (f:=f) (0:ℝ) h
lemma slope_pairs (b) : thermometer pairs b = (2:ℝ)⁻¹ • (thermometer raw b + J (thermometer raw (twice F d b))) := by
  have hc := thermometer_eval raw b
  have hJ := (LinearMap.toContinuousLinearMap J).hasFDerivAt.comp_hasDerivAt 0 (thermometer_eval raw (twice F d b))
  apply (thermometer_eval pairs b).unique
  simp only [white_split, map_smul]; exact (hc.add hJ).const_smul ((2:ℝ)⁻¹)
def mirrorsOf (A : Buffer F d ≃L[ℝ] (Fin n→ℝ)) := A.toLinearMap ∘ₗ twice F d ∘ₗ A.symm.toLinearMap
lemma mirror_eval (A : Buffer F d ≃L[ℝ] (Fin n→ℝ)) (v) : mirrorsOf A v = A (twice F d (A.symm v)) := rfl
variable (F d)
lemma make_pairing (h : square raw) : ∃ J : Module.End ℝ (Fin n→ℝ), let R := paired F d s g J; square R ∧ Fair R J := by
  obtain ⟨A,h⟩ := (show (thermometer raw).IsInvertible from h)
  let J := mirrorsOf A
  have he (b : Buffer F d) : thermometer (paired F d s g J) b = A b := by
    rw [slope_pairs, ←h]
    change (2:ℝ)⁻¹ • (A b + J (A (twice F d b)))=A b
    have h₂ : ∀ v : Fin n→ℝ, (2:ℝ)⁻¹ • (v+v)=v := by intro v; rw [←two_smul ℝ,smul_smul]; norm_num
    unfold J; rw [mirror_eval,A.symm_apply_apply,twice_twice]; exact h₂ _
  refine ⟨J, ⟨A,ContinuousLinearMap.ext (fun b=>(he b).symm)⟩, pairing_fair F d s g _ (fun v=>by unfold J; rw [mirror_eval,mirror_eval,A.symm_apply_apply,twice_twice,A.apply_symm_apply])⟩

end YM.Pert.Parity
