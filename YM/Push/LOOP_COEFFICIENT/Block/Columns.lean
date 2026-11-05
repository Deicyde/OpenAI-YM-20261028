import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Push.LOOP_COEFFICIENT.AliasJets

/-!
# Residue alias insertion and reading (unnormalized; ratio L exact)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Filter Set Matrix Metric Lattice Laurent RG Wilson Bloch Complex
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {a b c E : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype E] [DecidableEq a] [DecidableEq b] [DecidableEq c] {L s f : Side}

def place (a : Type) [DecidableEq a] (q : Momentum) (l : Site L) : Matrix (Co L a) a ℂ := (aliasBlock L a q).submatrix id (Prod.mk l)

def select (a : Type) [DecidableEq a] (q : Momentum) (l : Site L) : Matrix a (Co L a) ℂ := (((L.val:ℂ)^4)⁻¹ • returned (aliasBlock L a) q).submatrix (Prod.mk l) id

@[simp] lemma aliasSite_add (g : Ratio s f) (x y : Cover) (i j : Site g.count) : aliasSite g (x+y) (i+j)=aliasSite g x i + aliasSite g y j := by
  obtain ⟨z,hz⟩ := cover_of_eq _ _ (show wrap g.count (lift i+lift j) = wrap g.count (lift (i+j)) by simp)
  unfold aliasSite; rw [hz,smul_add,smul_add,← mul_smul,← g.exact_size, ← add_assoc,map_add,show wrap f (f.val • z) = 0 by ext i; change (((f.val • z : Cover) i : ℤ):Per f)=0; simp [Per], add_zero,map_add,map_add,map_add,map_add,map_add]; abel

lemma place_shift (a : Type) [DecidableEq a] (q : Momentum) (l : Site L) (x : Cover) : place a (q+reciprocal x) l = place a q (l+wrap L x) := by
  obtain ⟨y,hy⟩ := alias_shift l q x
  ext i j; simp [place,aliasBlock,hy]
lemma select_shift (a : Type) [DecidableEq a] (q : Momentum) (l : Site L) (x : Cover) : select a (q+reciprocal x) l = select a q (l+wrap L x) := by
  obtain ⟨y,hy⟩ := alias_shift l q x
  ext i j; simp only [select,submatrix_apply,id_eq,Matrix.smul_apply, returned, conjTranspose_apply,aliasBlock,of_apply, apply_ite (star : ℂ → ℂ),alias_adj,hy,mode_phase,mode_periodic,mul_one]

lemma place_diff (l : Site L) (q : Momentum) : ContDiffAt ℂ ω (fun q => place a q l) q := analyticMatrix (fun i j => by
  simp only [place,submatrix_apply,id_eq,aliasBlock,of_apply]; split
  · unfold mode aliasAt; fun_prop
  · fun_prop)
lemma select_diff (l : Site L) (q : Momentum) : ContDiffAt ℂ ω (fun q => select a q l) q := analyticMatrix (fun i j => by
  simp only [select,submatrix_apply,id_eq,Matrix.smul_apply, returned, conjTranspose_apply,aliasBlock,of_apply, apply_ite (star : ℂ → ℂ),alias_adj]; split
  · simp only [mode,← Complex.exp_neg]; unfold aliasAt; fun_prop
  · fun_prop)
lemma basis_pair (q : Momentum) (i j : Site L) : select a q i * place a q j = if i=j then 1 else 0 := by
  have he := straightens L a q
  ext x y : 1; have hh := congr_fun (congr_fun he (i,x)) (j,y)
  simp only [select,place,mul_apply,submatrix_apply,id_eq,Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]; change _ * ((returned (aliasBlock L a) q * aliasBlock L a q) _ _) = _; rw [hh,Matrix.smul_apply,smul_eq_mul,inv_mul_cancel_left₀ (pow_ne_zero _ (side_ne _))]; split <;> simp_all [Matrix.one_apply]
lemma place_select (q : Momentum) : ∑ i : Site L, place a q i * select a q i = 1 := by
  have h : aliasBlock L a q * (((L.val:ℂ)^4)⁻¹ • returned (aliasBlock L a) q) = 1 := by rw [Matrix.mul_smul, straighten',smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (side_ne L)),one_smul]
  ext i j; convert! congr_fun (congr_fun h i) j using 1; rw [Matrix.sum_apply, Matrix.mul_apply,Fintype.sum_prod_type]; rfl

omit [Fintype E] in
lemma coarsened (g : Ratio s f) (A : Grid f E a) (z : Cover) (l) : plane (A.trans (splitCo g a)) (wrap s z) * place a (quant s z) l = plane A (aliasSite g z l) := by
  ext i j : 1
  convert! congr_fun (congr_fun (alias_convert (a:=a) (g:=g) z) (A i)) (l,j) using 1

/- One versatile elimination rule for an output alias *family* (actual coarse vertex shifts may sum operators with different l-translation). -/
omit [Fintype E] in
lemma eliminate {F : Type} [Fintype F] {g : Ratio s f} {A : Grid f E a} {B : Grid f F b} {q p : Cover} {l : Site g.count} {M : Matrix E F ℂ} {W : Site g.count → Matrix a b ℂ}
    (h : ∀ i : Site g.count, Routed A B (aliasSite g p (i+l)) (aliasSite g q i) M (W i)) :
    Routed (A.trans (splitCo g a)) (B.trans (splitCo g b)) (wrap s p) (wrap s q) M (∑ i : Site g.count, place a (quant s p) (i+l) * W i * select b (quant s q) i) := by
  let D := plane (B.trans (splitCo g b)) (wrap s q)
  change M * D = _
  calc
    M*D = M*(D*(∑ i,place b (quant s q) (L:=g.count) i * select b (quant s q) i)) := by rw [place_select,Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mul_assoc D,show D * place b (quant s q) i = _ from coarsened g B q i,← Matrix.mul_assoc,h i,← coarsened g A p,← Matrix.mul_assoc,← Matrix.mul_assoc]
end YM.Push.Loops.Block
