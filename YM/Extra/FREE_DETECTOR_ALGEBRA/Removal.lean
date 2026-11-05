import Mathlib.Algebra.MvPolynomial.PDeriv
import YM.Extra.FREE_DETECTOR_ALGEBRA.Match


set_option warningAsError false

/-!
# Wick removal / annihilator identity

Acts on moments of the actual `WickPol`. No self-contraction, z=x-y,
no scalar conjugations even with complex coefficients. Will support both
matrix positivity and multiplication/detection tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.Pair
open Function Set Filter Tensor Maxwell Wick Wick.Occ
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {n : ℕ}

/-- Opposite positions, excluding self. -/
abbrev Others (i : Fin n) := {j : Fin n // j≠i}

def extractVar (i : Slot G) (x y : E4) : Derivation ℂ (WickPol G) (WickPol G) :=
  MvPolynomial.mkDerivation ℂ (fun a => MvPolynomial.C (entry i a x y))

private lemma extractMon (i : Slot G) (x y : E4) (p : Slot G →₀ ℕ) :
    extractVar i x y (monBasis G p) = ∑ k ∈ p.support,
      (p k : ℂ) • entry i k x y • monBasis G (p - Finsupp.single k 1) := by
  classical
  unfold extractVar
  have h (p : Slot G →₀ ℕ) : monBasis G p = MvPolynomial.monomial p 1 := by simp [monBasis]
  simp_rw [h, MvPolynomial.mkDerivation_monomial,one_smul, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [smul_eq_mul,MvPolynomial.C_apply,MvPolynomial.smul_monomial,MvPolynomial.monomial_mul,add_zero,mul_one]

/-- Replace a polynomial at site i, preserving everything else. -/
def replace (x : Points n) (W : Fin n → WickPol G) (i : Fin n) : WickPol G →ₗ[ℂ] ℂ :=
    (moment G x).toLinearMap W i

theorem replace_at (x : Points n) (W : Fin n → WickPol G) (i : Fin n) (v : WickPol G) :
    replace x W i v = moment G x (Function.update W i v) := rfl

theorem grouped (W : Powers G n) (i : Fin n) (f : Fin n → Slot G → ℂ) :
    (∑ p : {q : Occ W // q.label ≠ i}, f p.val.label p.val.probe) =
    ∑ j : Others i, ∑ a ∈ (W j).support, ((W j a):ℂ) * f j a := by
  classical
  let U := {q : Occ W // q.label ≠ i}
  let Z := (j : Others i) × (a : (W j).support) × Fin (W j a)
  let g (p : Z) : U := ⟨Occ.atSlot p.1 p.2.1 p.2.2 p.2.2.isLt, p.1.property⟩
  have ht (u : U) : u.val.probe ∈ (W u.val.label).support := by
    apply Finsupp.mem_support_iff.mpr; have he := u.val.legit; omega
  let e : Z ≃ U :=
    { toFun := g
      invFun u := ⟨⟨u.val.label,u.property⟩,⟨u.val.probe,ht u⟩,u.val.index,u.val.legit⟩
      left_inv x := rfl
      right_inv x := rfl }
  have he := Fintype.sum_equiv e (fun p => f p.1 p.2.1) (fun p => f p.val.label p.val.probe) (fun _ => rfl)
  rw [← he]; unfold Z
  simp_rw [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_coe_sort _ (fun a => ((W j a):ℂ) * f j a)

lemma remove_mon (W : Powers G n) (x : Points n) (hx : x∈conf n) (i : Fin n) (u : Slot G) :
    let V (j : Fin n) := monBasis G (W j)
    replace x V i (V i * MvPolynomial.X u) = ∑ k : Others i, replace x V k ((extractVar u (x i) (x k)) (V k)) := by
  classical
  intro V
  have he (p : Slot G →₀ ℕ) : monBasis G p = MvPolynomial.monomial p 1 := by simp [monBasis]
  have h : Function.update V i (V i * MvPolynomial.X u) = fun k => monBasis G (bump W i u k) := by
    ext1 k; rcases eq_or_ne k i with hk|hk
    · subst k
      simp only [Function.update_self, V, bump, he, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
    simp [V,bump,Function.update_of_ne hk]
  rw [replace_at,h,moment_basis,mon_bump W i u hx]
  let f j a := entry u a (x i) (x j) * monomial x (smaller W j a)
  have heq := grouped W i f
  change ∑ p : {q : Occ W // q.label≠i}, f _ _ = _
  rw [heq]; refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only [V]
  rw [extractMon,_root_.map_sum]; apply Finset.sum_congr rfl
  intro a _
  rw [_root_.map_smul,_root_.map_smul,replace_at,show Function.update (fun j => monBasis G (W j)) k.1
    (monBasis G (W k - Finsupp.single a 1)) = fun b => monBasis G (smaller W k a b) by
      funext m; by_cases hm : m=k.val <;> simp [smaller,hm], moment_basis]
  exact rfl

/-- Genuine recurrence, all Wick polynomial inputs, no cutoff or bounded
grade requirement other than the finite Wick inputs implicit in polynomial.
Uses actual ordinary entry; reflected arguments must be supplied separately. -/
theorem remove (x : Points n) (hx : x∈conf n) (i : Fin n) (u : Slot G) (W : Fin n → WickPol G) :
    replace x W i (W i * MvPolynomial.X u) = ∑ k : Others i, replace x W k (extractVar u (x i) (x k) (W k)) := by
  let E := WickPol G →ₗ[ℂ] WickPol G
  let f (i : Fin n) (p : E) := (moment G x).compLinearMap (Function.update (fun _ : Fin n => LinearMap.id) i p)
  let lhs := f i (LinearMap.mulRight ℂ (MvPolynomial.X u))
  let rhs := ∑ k : Others i, f k (extractVar u (x i) (x k)).toLinearMap
  have he i p W : f i p W = replace x W i (p (W i)) := by
    change moment G x _ = moment G x _
    congr 1
    funext v
    by_cases h : v=i <;> simp [h]
  have hl W : lhs W = replace x W i (W i*MvPolynomial.X u) := he ..
  have hr W : rhs W = ∑ k : Others i, replace x W k (extractVar u (x i) (x k) (W k)) := by
    unfold rhs; rw [sum_apply]; exact Finset.sum_congr rfl fun k _ => he ..
  have hw : lhs=rhs := by
    refine Module.Basis.ext_multilinear (fun _ => monBasis G) fun Y => ?_
    rw [hl,hr]; exact remove_mon Y _ hx i u
  exact (hl W).symm.trans ((congr_arg (fun f : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ => f W) hw).trans (hr W))
end YM.Extra.FD.Pair
