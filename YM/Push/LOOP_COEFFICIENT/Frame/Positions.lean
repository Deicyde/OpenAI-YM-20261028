import YM.Push.LOOP_COEFFICIENT.Block.Optimize

/-!
# Routed vertex for a replicated local rectangular matrix at translated loads
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter Matrix Lattice Laurent RG Bloch Complex Block
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {a b c d J E F : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [Fintype J] [DecidableEq J] [Fintype E] [Fintype F]
  {n : Side} {T : Grid n J d}

def Loads (T : Grid n J d) (D : Site n → Matrix c J ℝ) (M : Momentum → Matrix c d ℂ) := ∀ x {q k},Matches q k → ∀ v,cmat (D x) *ᵥ plane T k *ᵥ v = cell k x • (M q *ᵥ v)

def atom (M : Momentum → Matrix c d ℂ) (X : Jet c (Matrix a b ℂ)) : Vertex d a b := ⟨fun _ => X.base,fun _ p => X.lin.comp (M p).mulVecLin,fun _ p s => X.quad.compl₁₂ (M p).mulVecLin (M s).mulVecLin⟩

abbrev atVertex (M : Momentum → Matrix c d ℂ) (f : (c → ℝ) → Matrix a b ℝ) := atom M (actualMatrix f)
variable (B : Grid n E a) (C : Grid n F b)
def stack (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix a b ℝ) (z : J → ℝ) : Matrix E F ℝ := of fun i j => if (B i).1 = (C j).1 then f (D (B i).1 *ᵥ z) (B i).2 (C j).2 else 0
omit [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq J] [Fintype E] in
lemma stack_vector (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix a b ℝ) (v z i) : (stack B C D f z *ᵥ v) i = (f (D (B i).1 *ᵥ z) *ᵥ (fun j => v (C.symm ((B i).1,j)))) (B i).2 := by simp [stack,mulVec,dotProduct,← Equiv.sum_comp C.symm,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]
variable {D : Site n → Matrix c J ℝ} {f : (c → ℝ) → Matrix a b ℝ} (hf : ContDiffAt ℝ ω f 0)
include hf
omit [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq J] in
lemma composed (A : Matrix c J ℝ) : ContDiffAt ℝ ω (fun z => f (A *ᵥ z)) 0 := (show ContDiffAt ℝ ω f (clm A 0) by rw [map_zero]; exact hf).comp 0 (clm A).contDiff.contDiffAt
omit [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq J] in
lemma stack_smooth : ContDiffAt ℝ ω (stack B C D f) 0 := matrix_diff fun i j => by simp only [stack,of_apply]; split; exact matrix_component (composed hf _) _ _; exact contDiffAt_const
omit [DecidableEq a] [DecidableEq b] in
lemma probe_eq (i j) : ((actualMatrix (stack B C D f)).push (entryLinearMap ℂ ℂ i j)) = if (B i).1 = (C j).1 then (((actualMatrix f).pre (cmat (D (B i).1)).mulVecLin).push (entryLinearMap ℂ ℂ (B i).2 (C j).2)) else Jet.const 0 := by
  have he (g : (J → ℝ) → Matrix a b ℝ) (hg : ContDiffAt ℝ ω g 0) := actual_push cmat ofRealCLM.toLinearMap (entryLinearMap ℝ ℝ (B i).2 (C j).2).toContinuousLinearMap (entryLinearMap ℂ ℂ (B i).2 (C j).2) hg (fun _ => rfl)
  have h := actual_push cmat ofRealCLM.toLinearMap (entryLinearMap ℝ ℝ i j).toContinuousLinearMap (entryLinearMap ℂ ℂ i j) (stack_smooth (D:=D) B C hf) (fun _ => rfl)
  rw [actualMatrix,← h]; split
  next hh =>
    rw [← actualMatrix_pre hf]; convert! he _ (composed hf _) using 2; ext z; change stack _ _ _ _ z i j = _; rw [stack,of_apply, if_pos hh]; rfl
  next hh => change actual _ (fun z => stack B C D f z i j) = _; rw [show (fun z => stack B C D f z i j) = fun _ => 0 from funext fun _ => if_neg hh,actual_const]; rfl
omit hf [Fintype E] [Fintype J] [Fintype c] [DecidableEq J] [DecidableEq c] in
private lemma stack_routed {k q : Site n} (g : Matrix a b ℂ) (X : Matrix E F ℂ) (hx : ∀ i j,X i j = if (B i).1=(C j).1 then cell q (B i).1 * g (B i).2 (C j).2 else 0) : Routed B C (k+q) k X g := by
  refine Routed.of_vector fun v => funext fun i => ?_; let x := (B i).1; rw [plane_apply,cell_duality (k+q),cell_add,cell_duality _ k,cell_duality _ q]
  simp only [mulVec,dotProduct,← Equiv.sum_comp C.symm,Fintype.sum_prod_type]
  simp only [hx,plane,C.apply_symm_apply,of_apply,ite_mul,zero_mul, Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

end YM.Push.Loops.Frames
