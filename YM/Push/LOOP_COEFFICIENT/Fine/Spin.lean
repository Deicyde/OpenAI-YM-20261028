import YM.Push.LOOP_COEFFICIENT.Pullback
import YM.Push.LOOP_COEFFICIENT.Vector

/-!
# Actual jet of minus the left color adjoint and the shifted position gradient
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Function Set Filter Matrix Lattice Laurent Bloch RG Precision Wilson Work.F02 Complex  
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side}

def magnet (G : Gauge) (x : G.ColorIndex → ℝ) : Matrix G.ColorIndex G.ColorIndex ℝ :=
  let P := WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)
  LinearMap.toMatrix' (P.toLinearMap.comp ((-G.adjoint (G.lieExp (P.symm x))).comp P.symm.toLinearMap))
lemma magnet_apply (v w) : magnet G v *ᵥ w = WithLp.ofLp (-G.adjoint (G.lieExp (WithLp.toLp 2 v)) (WithLp.toLp 2 w)) := by rw [magnet,LinearMap.toMatrix'_mulVec]; rfl
lemma magnet_diff (G : Gauge) : ContDiffAt ℝ ω (magnet G) 0 := by
  refine matrix_diff fun i j => ?_
  let P := (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  rw [show (fun x => magnet G x i j) = fun x => WithLp.ofLp (-G.adjoint (G.lieExp (P x)) (P (Pi.single j 1))) i from funext (show ∀ x, magnet G x i j = WithLp.ofLp (-G.adjoint (G.lieExp (P x)) (P (Pi.single j 1))) i from fun x => by simpa using! congr_fun (magnet_apply (G:=G) x (Pi.single j 1)) i)]
  exact (PiLp.proj _ _ i).contDiff.contDiffAt.comp (f:=fun x => - G.adjoint (G.lieExp (P x)) (P (Pi.single j 1))) 0 (adjoint_diff (a:=fun _ => P (Pi.single j 1)) ((G.exp_jet.comp P.contDiff).contDiffAt (x:=0)) contDiffAt_const).neg

def coupling (G : Gauge) := actualMatrix (magnet G)


lemma gradient_entry (x : Loops.Links G n) (i : Edge (Site n)) (j : Site n) (a b : G.ColorIndex) : R_g (vary 1 x) (i,a) (j,b) = (if (i.1,a)=(j,b) then 1 else 0) + if i.1+step i.2=j then magnet G (fun c => x (i,c)) a b else 0 := by
  have he := paint_brace (vary 1 x) (Pi.single (j,b) 1) i
  change paint G _ (brace _ _ ) i a = _; rw [he,vary_one]; change paint G _ _ _ _ - _ = _
  rw [paint_apply,Pi.single_apply]; by_cases ht : i.1+step i.2=j
  · have hw : (paint G _) (Pi.single (j,b) 1) j = WithLp.toLp 2 (Pi.single b 1) := by ext; simp [paint_apply,Pi.single_apply]
    rw [if_pos ht,ht,hw]; have hm := congr_fun (magnet_apply (G:=G) (fun c => x (i,c)) (Pi.single b 1)) a
    rw [mulVec_single_one,col_apply] at hm; rw [hm]; rfl
  have hw : (paint G _) (Pi.single (j,b) 1) (i.1+step i.2) = 0 := by ext; simp [paint_apply,ht]
  rw [if_neg ht,hw,map_zero]; change _ - (0:ℝ) = _; rw [sub_zero,add_zero]

def onGradient (G : Gauge) (n : Side) := fun b : Loops.Links G n => R_g (vary 1 b)
lemma onGradient_diff (G : Gauge) : ContDiffAt ℝ ω (onGradient G n) 0 := smooth_R vary_diff

def readSite {a b : Type} (J : a) : CSpace (a × b) →ₗ[ℂ] CSpace b := LinearMap.pi fun i => LinearMap.proj (J,i)
lemma gradient_jet_entry (i : Edge (Site n)) (j : Site n) (a b : G.ColorIndex) : ((actualMatrix (onGradient G n)).push (entryLinearMap ℂ ℂ (i,a) (j,b))) =
    (Jet.const ((if (i.1,a)=(j,b) then 1 else 0):ℂ)).add
    (if i.1+step i.2=j then (((coupling G).pre (readSite i)).push (entryLinearMap ℂ ℂ a b)) else Jet.const 0) := by
  let P := (LinearMap.pi (R:=ℝ) (φ:=fun _ : G.ColorIndex => ℝ) (fun c => LinearMap.proj (φ:=fun _ : BondKey G n => ℝ) (i,c))).toContinuousLinearMap
  have he := actual_push cmat ofRealCLM.toLinearMap (Matrix.entryLinearMap ℝ ℝ (i,a) (j,b)).toContinuousLinearMap (entryLinearMap ℂ ℂ (i,a) (j,b)) (onGradient_diff G) (fun _ => rfl)
  change actual _ (fun x => R_g (vary _ x) _ _) = _ at he; rw [actualMatrix,← he]
  simp_rw [gradient_entry]; split_ifs
  all_goals rename_i h₁ h₂
  all_goals first
    | rw [actual_const]; ext <;> simp [Jet.add,Jet.const]
    | skip
  all_goals
    have hf := (show ContDiffAt ℝ ω (magnet G) (P 0) by rw [P.map_zero]; exact magnet_diff G).comp 0 P.contDiff.contDiffAt
    have hk := actual_push cmat ofRealCLM.toLinearMap (entryLinearMap ℝ ℝ a b).toContinuousLinearMap (entryLinearMap ℂ ℂ a b) hf (fun _ => rfl)
    rw [actual_pre cmat (magnet_diff G) P (readSite i) (fun _ => rfl)] at hk
    convert! (actual_add ofRealCLM.toLinearMap (f:=fun _ => if (i.1,a)=(j,b) then (1:ℝ) else 0) contDiffAt_const ((entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=magnet G ∘ P) 0 hf)).trans (congr_arg₂ Jet.add (actual_const ..) hk) using 2 <;> simp [*]
    all_goals first | rfl | (ext1; exact (zero_add ..).symm)
end YM.Push.Loops.Fine
