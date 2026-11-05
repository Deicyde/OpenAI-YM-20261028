import YM.Next.RANK.Gaussian

/-! Covariances pulled even when they have zero directions and/or repeated legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Function Set Finsupp MvPolynomial
open scoped BigOperators Classical

variable {V Z W : Type*} (M : V → Z →₀ ℂ)


abbrev glyph : (V →₀ ℂ) →ₗ[ℂ] poly V := linearCombination ℂ MvPolynomial.X
def exchange := (MvPolynomial.aeval fun i => glyph (M i) : poly V →ₐ[ℂ] poly Z)
@[simp] lemma exchange_x (i : V) : exchange M (X i)=glyph (M i) := by unfold exchange; rw [aeval_X]
@[simp] lemma exchange_c (v : ℂ) : exchange M (C v)=C v := by unfold exchange; rw [aeval_C, MvPolynomial.algebraMap_eq]

def reads (m : Z → ℂ) : V → ℂ := fun i => linearCombination ℂ m (M i)
lemma reads_at (m : Z → ℂ) (i : V) : aeval m (exchange M (X i))=reads M m i := by
  rw [exchange_x]; simp [glyph, reads, linearCombination_apply, Finsupp.sum]
lemma reads_map (m : Z → ℂ) : (aeval m).comp (exchange M) = (aeval (reads M m)) := by
  ext i; rw [AlgHom.comp_apply,reads_at,aeval_X]
lemma reads_val (m : Z → ℂ) (p : poly V) : aeval m (exchange M p) = aeval (reads M m) p := DFunLike.congr_fun (reads_map ..) p

def treats (Q : Symmetric V) (x y : V →₀ ℂ) := linearCombination ℂ (linearCombination ℂ Q.cov x) y
lemma treats_comm (Q : Symmetric V) (x y : V →₀ ℂ) : treats Q x y=treats Q y x := by
  simp_rw [treats,linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [Q.symm i j]; ring

def scope (Q : Symmetric Z) : Symmetric V := ⟨fun i j => treats Q (M i) (M j),fun i j => treats_comm Q (M i) (M j)⟩
lemma scopes (M' : Z → W →₀ ℂ) (Q : Symmetric W) : scope (fun i => linearCombination ℂ M' (M i)) Q = scope M (scope M' Q) := by
  apply Symmetric.ext; funext i j
  let A := M i; let B := M j
  change treats Q (linearCombination ℂ M' A) (linearCombination ℂ M' B) = treats (scope M' Q) A B
  unfold treats
  rw [linearCombination_linearCombination]
  have ht : (linearCombination ℂ (scope M' Q).cov A) = fun z =>
      linearCombination ℂ (linearCombination ℂ Q.cov (linearCombination ℂ M' A)) (M' z) := by
    funext z
    calc
      _ = linearCombination ℂ (fun k => treats Q (M' k) (M' z)) A := by
        simp only [linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,scope]
      _ = linearCombination ℂ (fun k => treats Q (M' z) (M' k)) A := by
        rw [show (fun k => treats Q (M' k) (M' z)) = _ from funext (fun k => treats_comm Q _ _)]
      _ = treats Q (M' z) (linearCombination ℂ M' A) := (linearCombination_linearCombination ..).symm
      _ = _ := treats_comm ..
  rw [ht]

lemma exchange_slit (m : Z → ℂ) (p : poly V) : slit m (exchange M p) = exchange M (slit (reads M m) p) := by
  have hx (v : Z →₀ ℂ) : slit m (glyph v)=C (linearCombination ℂ m v) := by
    simp only [glyph,linearCombination_apply,Finsupp.sum,map_sum,(slit m).map_smul,slit_X,smul_eq_mul,map_mul,C_mul']
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp,hq,map_add, map_add]
  | mul_X p i hp =>
    rw [mul_comm p,slit_prod,map_add,map_mul (exchange M),map_mul (exchange M),map_mul (exchange M),exchange_x,exchange_c,(slit m).leibniz,hx,hp]
    simp only [smul_eq_mul]; rw [mul_comm (exchange M p)]; rfl

lemma slit_smul (m : V → ℂ) (a : ℂ) (p : poly V) : slit (a • m) p=a • slit m p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q h1 h2 => simp only [map_add,h1,h2,smul_add]
  | mul_X p i h =>
    rw [mul_comm p, slit_prod, slit_prod,h,Pi.smul_apply, smul_eq_mul,map_mul]
    simp only [← C_mul']; ring

lemma refresh (b : V →₀ ℂ) (Q : Symmetric V) (p : poly V) :
    milk Q (glyph b * p)=glyph b * milk Q p + slit (linearCombination ℂ Q.cov b) (milk Q p) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [map_zero,zero_mul, slit_zero,add_zero]
  | add i j hi hj => rw [map_add, add_mul, add_mul, map_add, map_add, hi,hj, slit_linear]; abel
  | single i a =>
    rw [glyph,linearCombination_single,linearCombination_single,slit_smul,← C_mul',mul_assoc, mul_assoc, drink, feeds, mul_add]; rw [← C_mul']

-- The pullback changes K by the full pulled form. No v charges needed.
lemma prepared (Q : Symmetric Z) (p : poly V) : milk Q (exchange M p) = exchange M (milk (scope M Q) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q h1 h2 => rw [_root_.map_add, _root_.map_add,h1,h2,map_add,map_add]
  | mul_X p i h =>
    rw [mul_comm p,map_mul (exchange M),feeds,map_add,map_mul (exchange M), exchange_x,refresh, h, exchange_slit]; rfl

lemma wets (Q : Symmetric Z) (m : Z → ℂ) (p : poly V) : blend Q m (exchange M p)=blend (scope M Q) (reads M m) p := by
  rw [blend_components,prepared,reads_val]; rfl

lemma labelled (f : V → Z) : (MvPolynomial.rename f : poly V →ₐ[ℂ] poly Z)=exchange (fun i => Finsupp.single (f i) 1) := by ext i; simp only [exchange_x,glyph,linearCombination_single,one_smul, MvPolynomial.rename_X]
lemma match_name (f : V → Z) (R : Symmetric Z) (x y : V) : (scope (fun i => Finsupp.single (f i) 1) R).cov x y= R.cov (f x) (f y) := by simp only [scope,treats,linearCombination_single,one_smul]
end YM.Next.Rank.Normal
