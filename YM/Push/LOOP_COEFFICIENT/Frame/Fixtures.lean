import YM.Push.LOOP_COEFFICIENT.Frame.Capital
import YM.Push.LOOP_COEFFICIENT.Frame.Sites

/-!
# Centered and raw local Haar-increment formulas
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Matrix Filter Set Lattice Laurent RG Bloch Precision Exterior Pressure Wilson Gauge YM.Branch Block
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {P : Patch} {G : Gauge} {C : KernelChoices}
abbrev World (P : Patch) (G : Gauge) := (Outlook P G → ℝ) × (LocalField P G → ℝ)
def laid (j : Satellite) (z : World P G) : CoverConfig G := fun i => let x := (i.1+cloudSite P j,i.2); G.lieExp (logs (z.2 ∘ Sum.inl) x) * G.lieExp (logs (z.1 ∘ Sum.inl) x)
def fromHome (j : Satellite) (z : World P G) := G.lieExp (wind j (z.1 ∘ Sum.inl))
def goBack (j : Satellite) (z : World P G) := fromHome j z * (crownMap P (laid j (z.1,0)))⁻¹
def leverPoint (j : Satellite) (z : World P G) := goBack j z * crownMap P (laid j z)
@[simp] lemma lever_zero (j : Satellite) (z : Outlook P G → ℝ) : leverPoint (P:=P) j (z,0)=fromHome (P:=P) j (z,0) := inv_mul_cancel_right ..















@[simp] lemma jumps_zero (j : Satellite) : jumps (0:LocalField P G → ℝ) j = 0 := rfl
@[simp] lemma bondVar_zero (i : Axis) : bondVar (0:Outlook P G → ℝ) i = 0 := rfl
lemma forceLink_zero (j : Satellite) (i : P.Points) : forceLink j (0:Interior P G → ℝ) i=0 := by
  have he (u : Cover) (l : Walk) : linkSum (fun _ : Edge Cover => (0:ℝ)) u l = 0 := by induction l generalizing u <;> simp_all [linkSum]
  ext s; change -(avg fun _ => avg fun _ => linkSum _ _ _)=(0:ℝ); simp only [logs_zero,PiLp.zero_apply, he,avg_const,neg_zero]
@[simp] lemma wind_zero (j : Satellite) : wind j (0:Interior P G → ℝ)=0 := by ext s; simp [wind,forceLink_zero]
@[simp] lemma fromHome_zero (j : Satellite) : fromHome j (0:World P G)=1 := by change G.lieExp (wind j (0:Interior P G → ℝ)) = _; simp
@[simp] lemma laid_zero (j : Satellite) : laid j (0:World P G)=1 := by ext1 i; change G.lieExp (logs (0:Interior P G → ℝ) _) * G.lieExp (logs (0:Interior P G → ℝ) _) = 1; simp








variable (h : P.Branches C G)
include h


omit h in lemma jumps_diff (j : Satellite) : ContDiff ℝ ω (fun v : LocalField P G → ℝ => jumps v j) := (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toContinuousLinearEquiv.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_apply ..))
omit h in lemma bondVar_diff (i : Axis) : ContDiff ℝ ω (fun v : Outlook P G → ℝ => bondVar v i) := (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toContinuousLinearEquiv.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_apply ..))






end YM.Push.Loops.Frames
