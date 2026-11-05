import YM.Push.LOOP_COEFFICIENT.Block.Columns
import YM.Push.LOOP_COEFFICIENT.Block.Portal

/-!
# Distributed alias bases with an arbitrary real diagonal amplitude
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent RG Wilson Bloch Complex Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {L : Side}

abbrev Weight (L : Side) := Momentum → Site L → ℝ
def pane (L : Side) (a : Type) [Fintype a] [DecidableEq a] (w : Weight L) (p : Momentum) := ((L.val:ℂ)^2)⁻¹ • aliasBlock L a p * diagonal (fun i : Co L a => (w p i.1:ℂ))
lemma portal_unit (L : Side) (a : Type) [Fintype a] [DecidableEq a] (w : Weight L) (hw : ∀ q i, 0<w q i) (p : Momentum) : IsUnit (pane L a w p) := by
  have he : IsUnit (((L.val:ℂ)^2)⁻¹ • aliasBlock L a p) := IsUnit.mul_iff.mp ((show (((L.val:ℂ)^2)⁻¹ • aliasBlock L a p) * (((L.val:ℂ)^2)⁻¹ • returned (aliasBlock L a) p) = 1 by rw [Matrix.smul_mul, Matrix.mul_smul,straighten',smul_smul,smul_smul,show ∀ z : ℂ, z ≠ 0 → (z^2)⁻¹*(z^2)⁻¹*z^4 = 1 from fun z hz => by field_simp,one_smul]; exact side_ne _).symm ▸ isUnit_one) |>.1
  exact he.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (ofReal_ne_zero.mpr (hw p i.1).ne')))
def distributed (L : Side) (a : Type) [DecidableEq a] [Fintype a] (w : Weight L) (hw : ∀ q i, 0<w q i) : Portal (Co L a) := ⟨pane L a w,portal_unit L a w hw⟩

lemma select_pane (w : Weight L) (p : Momentum) (l : Site L) (x : CSpace (Co L a)) : select a p l *ᵥ (pane L a w p *ᵥ x) = (((L.val:ℂ)^2)⁻¹ * w p l) • (fun i => x (l,i)) := by
  rw [Matrix.mulVec_mulVec, pane, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]; ext1 i
  have he (r : Site L) j := congr_fun (congr_fun (basis_pair (a:=a) p l r) i) j
  change ∀ (r : Site L) (j : a), (select a p l * aliasBlock L a p) i (r,j) = _ at he
  simp [mulVec,dotProduct,Fintype.sum_prod_type,mul_diagonal,he,ite_mul, Finset.sum_ite_irrel,show ∀ r (j : a), ((if l=r then 1 else 0):Matrix a a ℂ) i j = _ from fun r j => apply_ite (fun M : Matrix a a ℂ => M i j) .. ,Matrix.one_apply,mul_assoc]

omit [Fintype a] in
lemma select_opposite (p : Momentum) (l : Site L) : (place a p l).transpose = (L.val:ℂ)^4 • select a (-p) (-l) := by
  obtain ⟨x,hx⟩ := alias_opposite l p; ext i j : 1; simp only [place,select,transpose_apply,submatrix_apply,id_eq,Matrix.smul_apply, smul_eq_mul,mul_inv_cancel_left₀ (pow_ne_zero _ (side_ne L)),returned,conjTranspose_apply,aliasBlock,of_apply,apply_ite (star : ℂ → ℂ),alias_adj, hx,mode_phase,mode_periodic,mul_one,mode_inverse,inv_inv,star_zero]
lemma pane_place (w : Weight L) (p : Momentum) (l : Site L) (x : CSpace (Co L a)) : x ᵥ* ((pane L a w (-p)).transpose * place a p l) = ((L.val:ℂ)^2*w (-p) (-l)) • (fun i => x (-l,i)) := by rw [← Matrix.mulVec_transpose, transpose_mul,transpose_transpose, select_opposite,Matrix.smul_mul,Matrix.smul_mulVec,← mulVec_mulVec,select_pane,smul_smul]; congr 1; field_simp [side_ne L]



end YM.Push.Loops.Block
