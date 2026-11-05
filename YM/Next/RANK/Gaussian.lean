import Mathlib.Algebra.MvPolynomial.Derivation
import YM.Maxwell.Wick


/-!
# Signed algebraic Gaussian computations at endpoints

No positive probabilistic interpretation if the step data is cut or has
removed the P0 contractions. A rigorous polynomial formalism for those
operations. Operators Gamma compute Gaussian polynomials with covariances as
specified. They cumulate, also giving normaling the correct negative sign.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Finsupp Function Set
open scoped BigOperators

variable {V Z : Type*}
abbrev poly (V : Type*) := MvPolynomial V ℂ
structure Symmetric (V : Type*) where
  cov : V → V → ℂ
  symm i j : cov i j=cov j i
namespace Symmetric
instance : Add (Symmetric V) where
  add p q := ⟨p.cov+q.cov,fun i j => congr_arg₂ (·+·) (p.symm i j) (q.symm ..)⟩
instance : Zero (Symmetric V) where
  zero := ⟨0,fun _ _ => rfl⟩
instance : Neg (Symmetric V) where
  neg p := ⟨-p.cov,fun i j => congr_arg (-·) (p.symm i j)⟩
@[ext] lemma ext {p q : Symmetric V} (h : p.cov=q.cov) : p=q := by cases p;cases q;congr
lemma cancels (p : Symmetric V) : p + -p=0 := ext (add_neg_cancel _)


end Symmetric

open MvPolynomial
variable (b : V → ℂ)

def slit := MvPolynomial.mkDerivation ℂ (fun i => C (σ:=V) (b i))
@[simp] lemma slit_X (i : V) : slit b (MvPolynomial.X i)=C (b i) := by simp [slit]
@[simp] lemma slit_C (a : ℂ) : slit b (C a)=0 := (slit b).map_algebraMap _
lemma slit_prod (p : poly V) (i : V) : slit b (MvPolynomial.X i * p)= MvPolynomial.X i*slit b p+C (b i)*p := by rw [(slit b).leibniz,slit_X]; simp [smul_eq_mul,mul_comm p]
lemma slit_zero (p : poly V) : slit 0 p=0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q h H => simp only [map_add,h,H,add_zero]
  | mul_X p i h => rw [mul_comm, slit_prod,h]; simp
lemma slit_linear (a : V → ℂ) (p : poly V) : slit (a+b) p=slit a p+slit b p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q h H => simp only [map_add,h,H]; abel
  | mul_X p i h => rw [mul_comm p]; simp only [slit_prod,h,mul_add,Pi.add_apply,map_add,add_mul]; abel
lemma slit_slit (a : V → ℂ) (p : poly V) : slit a (slit b p)=slit b (slit a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q h H => simp only [map_add,h,H]
  | mul_X p i h =>
    rw [mul_comm p]; simp only [slit_prod, _root_.map_add,(slit a).leibniz (C _) p,(slit b).leibniz (C _) p, smul_eq_mul,slit_C,mul_zero,h]; ring

variable (Q : Symmetric V) (i : V)
def cream (i : V) : Module.End ℂ (poly V) := LinearMap.mulLeft ℂ (X i) + (slit (Q.cov i)).toLinearMap
lemma creams (p : poly V) : cream Q i p=X i*p+slit (Q.cov i) p := rfl
lemma cream_comm (j : V) : Commute (cream Q i) (cream Q j) := by
  apply LinearMap.ext; intro p; change cream Q i (cream Q j p)=cream Q j (cream Q i p); simp only [creams,_root_.map_add,slit_prod]; rw [Q.symm i j, slit_slit (Q.cov j)]; ring

private abbrev cheese := Algebra.adjoin ℂ (Set.range (cream Q))
open scoped IsMulCommutative in
local instance (Q : Symmetric V) : CommSemiring (cheese Q) := by
  have := Algebra.isMulCommutative_adjoin (s:=Set.range (cream Q)) ℂ (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩; exact cream_comm Q i j)
  infer_instance
def make (Q : Symmetric V) : poly V →ₐ[ℂ] Module.End ℂ (poly V) :=
    (cheese Q).val.comp (MvPolynomial.aeval (fun i => (⟨cream Q i,Algebra.subset_adjoin ⟨i,rfl⟩⟩ : cheese Q)))
lemma made : make Q (X i)=cream Q i := by simp only [make,AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl

def milk : Module.End ℂ (poly V) := ((LinearMap.applyₗ (R:=ℂ)) 1).comp (make Q).toLinearMap
lemma milk_val (p : poly V) : milk Q p = (make Q p) 1 := rfl
@[simp] lemma pure : milk Q 1=1 := by rw [milk_val, map_one (make Q)]; rfl
lemma drink (a : ℂ) (p : poly V) : milk Q (C a*p)=C a*milk Q p := by rw [C_mul', _root_.map_smul,C_mul']
@[simp] lemma fine (a : ℂ) : milk Q (C a)=C a := by simpa only [pure,mul_one] using drink Q a 1
lemma feeds (p : poly V) : milk Q (X i*p) = X i*milk Q p+slit (Q.cov i) (milk Q p) := by rw [milk_val,map_mul (make Q),made]; rfl
lemma skims (p : poly V) : slit b (milk Q p)=milk Q (slit b p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [_root_.map_add,hp,hq]
  | mul_X p i hp =>
    rw [mul_comm p,feeds]; simp only [slit_prod,_root_.map_add]; rw [drink,feeds,slit_slit (Q.cov i),hp]; abel
lemma froze (p : poly V) : milk (0:Symmetric V) p=p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact fine _ _
  | add p q hp hq => rw [_root_.map_add,hp,hq]
  | mul_X p i hp =>
    rw [mul_comm p,feeds,hp]; exact (congr_arg (_+·) (slit_zero p)).trans (add_zero _)

lemma warms (P : Symmetric V) (p : poly V) : milk P (milk Q p)=milk (P+Q) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [_root_.map_add,hp,hq]
  | mul_X p i hp =>
    rw [mul_comm p,feeds, _root_.map_add,feeds,feeds,← skims,hp]
    change _ = _ + slit (P.cov i+Q.cov i) _; rw [slit_linear]; abel



def blend (m : V → ℂ) : poly V →ₗ[ℂ] ℂ := (aeval m).toLinearMap.comp (milk Q)
lemma blend_components (m : V → ℂ) (p : poly V) : blend Q m p = aeval m (milk Q p) := rfl
lemma blended (m : V → ℂ) (p : poly V) : blend Q m (X i*p) = m i*blend Q m p + blend Q m (slit (Q.cov i) p) := by
  rw [blend_components, feeds, skims, _root_.map_add, map_mul, aeval_X]; rfl
@[simp] lemma fresh (m : V → ℂ) : blend Q m 1=1 := by rw [blend_components,pure,map_one]
end YM.Next.Rank.Normal
