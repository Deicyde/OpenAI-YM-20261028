import YM.Extra.FREE_DETECTOR_ALGEBRA.CurlDetect
import YM.Extra.FREE_DETECTOR_ALGEBRA.Radials

set_option warningAsError false

/-!
# Angular harmonics of probes and mixed leg pairings
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.SphereTest
open Function Filter Set Tensor Analysis Maxwell Wick
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {j k : ℕ}

lemma angGreen : KelvinAng 0 Green := by
  refine (ang_const normal).near fun x _ => ?_; unfold Green; exact mul_comm ..

theorem angBare (a b i m : Axis) : KelvinAng 2 (bareCurl a b i m) := by
  have he (b i m : Axis) : KelvinAng 1 (if i=b then grad m Green else 0) := by split_ifs; exact angGreen.gradient _; exact ang_zero _
  have ht (b i m) : KelvinAng 1 (curlOpp b i m) := (he b i m).sub (he b m i)
  exact ((ht b i m).gradient a).sub ((ht a i m).gradient b)

lemma ang_reply (P : Sol G.Color j) (i m : Axis) : KelvinAng (j+2) (reply (G:=G) P i m) := by
  let f : Axis → Axis → E4 → G.Color := fun a b => applyDiff (P.val a b) (bareCurl a b i m)
  have he a b : KelvinAng (j+2) (f a b) := by
    unfold f applyDiff
    apply ang_sum
    intro v _
    rw [Nat.add_comm]
    exact ((angBare a b i m).jet j v).linear ((ContinuousLinearMap.id ℝ ℝ).smulRight _)
  refine (ang_sum (Finset.univ:Finset Axis) (fun a x => ∑ b : Axis, f a b x) (fun a _ => ang_sum _ _ (fun b _ => he a b))).near ?_
  exact fun x hx => (replyFrob P hx i m).symm

lemma ang_tensor (P : Sol G.Color j) (Q : Sol G.Color k) : KelvinAng (j+k+2)
    (legKernel (G:=G) (dualSol G.Color j P) (dualSol _ _ Q)) := by
  let f (x) := dotF Q.val (WaveOn.nth (reply (G:=G) P) k x)
  have he : KelvinAng (j+k+2) f := by
    let H (a b : Axis) (v : Dirs k) (x : E4) := ⟪Q.val a b (dir v),coeff (reply (G:=G) P a b) k x (dir v)⟫
    change KelvinAng (j+k+2) (fun x => ∑ a : Axis, ∑ b : Axis, ∑ v : Dirs k,H a b v x)
    refine ang_sum _ _ (fun a _ => ang_sum _ _ (fun b _ => ang_sum _ _ (fun v _ => ?_)))
    rw [show j+k+2=j+2+k by omega]
    exact ((ang_reply P a b).jet k v).linear (innerSL ℝ _)
  exact (he.scalar ((-1)^k)).near fun x hx => (replyTest P Q hx).symm

theorem ang_leg (P : Probe G j) (Q : Probe G k) : KelvinAng (j+k+2) (legKernel P Q) := by
  obtain ⟨P,rfl⟩ := (dualSol G.Color j).surjective P; obtain ⟨Q,rfl⟩ := (dualSol G.Color k).surjective Q; exact ang_tensor P Q


end YM.Extra.FD.SphereTest
