import YM.Next.RANK.Herald
import YM.Next.RANK.HomeSync
import YM.Next.RANK.Respire
import YM.Next.RANK.SpectrumReal

/-!
# Auxiliary expectation in an unforced step

Whole stencil joint law. Integration-by-parts receipt on the *centered* law; spectral
and guard costs in next interface. No assertion that the Wilson kernel is an
exact Gaussian probability kernel (estimate uses this receipt on one leading
family of the value step). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set Filter Lattice Wilson RG Perch Atlas Rise Normal  Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value MeasureTheory
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {Ω V Z : Type*}

structure VMeasure (Ω : Type*) [MeasurableSpace Ω] (V : Type*) (μ : Measure Ω) (X : Ω → V → ℝ) (P : Normal.Symmetric V) : Prop where
  norm : IsProbabilityMeasure μ
  prices (q : Normal.poly V) : Integrable (fun U=> text (X U) q) μ
  ibp (q : Normal.poly V) (i : V) :
    (∫ U,text (X U) (MvPolynomial.X i*q) ∂μ)=∫ U,text (X U) (Normal.slit (P.cov i) q) ∂μ

variable [MeasurableSpace Ω] {μ : Measure Ω} {x : Ω → V → ℝ} {P : Normal.Symmetric V}

def carry (x : Ω → V → ℝ) (m : V → ℝ) (q : Normal.poly V) (u : Ω) := text (m+x u) q
private def moving (m : V → ℝ) : Normal.poly V →ₐ[ℂ] Normal.poly V := aeval fun i => MvPolynomial.X i+MvPolynomial.C (m i:ℂ)
private lemma carries (u : V→ℝ) (m : V→ℝ) (q : Normal.poly V) : text u (moving m q)=text (m+u) q:= by
  apply DFunLike.congr_fun (f:=(aeval _).comp (moving m)); ext1 i
  rw [AlgHom.comp_apply,moving, aeval_X,_root_.map_add,aeval_X,aeval_C,aeval_X]; simp [add_comm]
private lemma slip (m : V → ℝ) (q : Normal.poly V) (b : V→ℂ) : Normal.slit b (moving m q)=moving m (Normal.slit b q):= by
  let R:=moving m
  have he i : R (MvPolynomial.X i)=MvPolynomial.X i+MvPolynomial.C (m i:ℂ):= aeval_X ..
  have hf i : R (MvPolynomial.C i)=MvPolynomial.C i:= aeval_C ..
  induction q using MvPolynomial.induction_on with
  | C i=> rw [hf,slit_C,_root_.map_zero]
  | add a b ha hb=> rw [_root_.map_add,_root_.map_add,ha,hb,_root_.map_add,_root_.map_add]
  | mul_X a i H=> rw [mul_comm a,slit_prod,_root_.map_add (f:=R),_root_.map_mul (f:=R),_root_.map_mul (f:=R),_root_.map_mul (f:=R),he,Derivation.leibniz,_root_.map_add,slit_X,slit_C,H,hf]; simp [smul_eq_mul,mul_comm]; exact Or.inl rfl

lemma carries_int (H : VMeasure Ω V μ x P) (m : V → ℝ) (q : Normal.poly V) : Integrable (carry x m q) μ:= by
  unfold carry;simp_rw [← carries]; exact H.prices _

variable (m : V→ ℝ)
private def cog (H : VMeasure Ω V μ x P) : Normal.poly V →ₗ[ℂ] ℂ where
  toFun q:=∫ U,carry x m q U ∂μ
  map_add' p q:=by simp_rw [carry,text,_root_.map_add]; exact integral_add (carries_int H m p) (carries_int H m q)
  map_smul' c p:=by simp_rw [carry,text,map_smul,smul_eq_mul]; exact integral_const_mul ..
private lemma fee (H : VMeasure Ω V μ x P) (i : V) (q : Normal.poly V) :
    cog m H (MvPolynomial.X i*q) = m i * cog m H q + cog m H (slit (P.cov i) q):= by
  let A:= moving m q; let g := fun p : Normal.poly V=> fun U=> text (x U) p
  unfold cog; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [carry,← carries]
  rw [_root_.map_mul (f:=moving m),show moving m (MvPolynomial.X i)=_ from (show moving m (MvPolynomial.X i)= X i + C (m i:ℂ) from aeval_X ..),add_mul]
  rw [show (fun U=> g (MvPolynomial.X i*A+ MvPolynomial.C (m i:ℂ)*A) U)= (fun U=>g (MvPolynomial.X i*A) U + g (MvPolynomial.C (m i:ℂ)*A) U) from funext fun U=> map_add _ _ _, integral_add (H.prices _) (H.prices _)]
  rw [H.ibp]; dsimp only [A]; simp_rw [slip]; rw [add_comm]
  congr 1
  unfold text; simp_rw [map_mul,aeval_C]; exact integral_const_mul ..

lemma payment (H : VMeasure Ω V μ x P) (q : Normal.poly V) : (∫ U,carry x m q U ∂μ)= Normal.blend P (fun i=>(m i:ℂ)) q := by
  let R:=Normal.blend P (fun i=>(m i:ℂ)); let Q:= cog m H
  have ht : ∀ {Z : Type _} (p : Finset Z) (v : Z→V),Q (Normal.glyphs v p)=R (Normal.glyphs v p):= by
    intro Z p v
    induction p using Finset.strongInduction with
    | _ p ih=>
      obtain rfl|⟨i,hi⟩:= p.eq_empty_or_nonempty
      · rw [glyphs,Finset.prod_empty,fresh]
        have hv:= H.norm; change (∫ U, text _ 1 ∂μ)=1; simp [text]
      let w:= p.erase i
      have he : w⊂ p:= Finset.erase_ssubset hi
      rw [show glyphs v p=MvPolynomial.X (v i)* Normal.glyphs v w from (Finset.mul_prod_erase p _ hi).symm, fee,blended, renew]
      simp_rw [map_sum,map_smul]; rw [show cog m H (glyphs v w)=_ from ih _ he]
      congr 1; apply Finset.sum_congr rfl; intro j hx
      exact congr_arg _ (ih _ (lt_of_le_of_lt (Finset.erase_subset ..) he))
  change Q q=R q; rw [q.as_sum]; simp_rw [map_sum]; apply Finset.sum_congr rfl; intro i hi
  obtain ⟨v,hv⟩:= Common.letter i
  rw [show monomial i (coeff i q)=coeff i q • monomial i 1 by rw [← map_smul,smul_eq_mul,mul_one],map_smul (f:=R),map_smul (f:=Q),hv]; exact congr_arg _ (ht _ _)
end YM.Next.Rank.Tapes
