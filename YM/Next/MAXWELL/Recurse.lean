import Mathlib.Algebra.MvPolynomial.PDeriv
import YM.Next.MAXWELL.Fusion
import YM.Next.MAXWELL.Kernel



/-!
# Annihilate

The cross-only Wick recurrence, from actual polynomial labels. Canonical
coordinate tests are real, but all these equations also keep the complex
linearity (ordinary, not anti). Use C-linear derivative operators;
`symbol` a real linear probe tested on Shell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Function Set Filter Finset Tensor Analysis Wick Occ
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {j k l n : ℕ}

/-- At x, test p into a field at y; remove an entry. -/
def eat (p : Probe G j) (x y : E4) : Derivation ℂ (WickPol G) (WickPol G) :=
  MvPolynomial.mkDerivation ℂ fun i => MvPolynomial.C (K p (coordinateLeg i) x y : ℂ)

def takeAt (U : Powers G n) (i : Fin n) (s : Slot G) : Powers G n :=
  update U i (U i - Finsupp.single s 1)

/-- Occurrence sum, independent of the copy index. -/
private lemma add_index (U : Powers G n) (f : Fin n → Slot G → ℂ) :
    (∑ p : Occ U, f p.label p.probe) = ∑ i, ∑ v ∈ (U i).support, (U i v : ℂ) * f i v := by
  classical
  let X := (i : Fin n) × (v : (U i).support) × Fin (U i v.val)
  have he (p : Occ U) : p.probe ∈ (U p.label).support := by
    have ht := p.legit; rw [Finsupp.mem_support_iff]; omega
  let e : Occ U ≃ X :=
    { toFun p := ⟨p.label,⟨p.probe,he p⟩,p.index,p.legit⟩
      invFun p := atSlot p.1 p.2.1 p.2.2 p.2.2.isLt
      left_inv _ := rfl
      right_inv _ := rfl }
  have H : (∑ p : Occ U, f p.label p.probe) = ∑ x : X, f x.1 x.2.1.val :=
    Fintype.sum_equiv e _ _ fun _ => rfl
  rw [H]; unfold X; rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro i _
  rw [Fintype.sum_sigma]
  simp
  exact Finset.sum_attach (U i).support (fun x => (U i x : ℂ) * f i x)

theorem mon_eaten (p : Probe G j) (W : Slot G →₀ ℕ) (x y : E4) :
    eat p x y (monBasis G W) = ∑ i ∈ W.support, ((W i:ℂ)*(K p (coordinateLeg i) x y:ℂ)) •
      monBasis G (W - Finsupp.single i 1) := by
  unfold eat monBasis
  rw [MvPolynomial.coe_basisMonomials,MvPolynomial.mkDerivation_monomial,one_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  change MvPolynomial.monomial _ _ * MvPolynomial.C _ = _
  rw [mul_comm,MvPolynomial.C_mul_monomial,MvPolynomial.smul_monomial]; simp [mul_comm]

lemma derivation_sum_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (WickPol G) (WickPol G)) (p : WickPol G) :
    (∑ i ∈ s,D i) p = ∑ i ∈ s,D i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,Derivation.add_apply,ih]

lemma deriv_scalar (D : Derivation ℂ (WickPol G) (WickPol G)) (t : ℂ) (p : WickPol G) :
    D (t • p)= t • D p := map_smul D.toLinearMap t p

lemma probe_expansion (p : Probe G j) : p =
    ∑ i : Fin (legDim G j), p (frame G j i) • ((frame G j).coord i) := by
  apply LinearMap.ext; intro u; rw [LinearMap.sum_apply]
  conv_lhs => rw [← (frame G j).sum_repr u]
  simp only [map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..

section Recur
variable {x : Points n} (H : x ∈ conf n)

lemma moment_X (s : Slot G) (v : Fin n → WickPol G) (i : Fin n) (H : x ∈ conf n) :
    moment G x (update v i (MvPolynomial.X s * v i)) =
      ∑ b ∈ Finset.univ.erase i, moment G x (update v b (eat (coordinateLeg s) (x i) (x b) (v b))) := by
  classical
  let A (L : Module.End ℂ (WickPol G)) (i : Fin n) :
      MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
    (moment G x).compLinearMap (fun j => if j=i then L else LinearMap.id)
  have he (L : Module.End ℂ (WickPol G)) (i : Fin n) (v : Fin n → WickPol G) :
      A L i v = moment G x (update v i (L (v i))) := by
    simp only [A,MultilinearMap.compLinearMap_apply]; congr 1
    ext1 j; by_cases h : j=i <;> simp_all
  let L₀ := Algebra.lmul ℂ (WickPol G) (MvPolynomial.X s)
  let L (b : Fin n) := (eat (coordinateLeg s) (x i) (x b)).toLinearMap
  suffices h : A L₀ i = ∑ b ∈ Finset.univ.erase i, A (L b) b by
    change moment G x (update v i (L₀ _)) = _
    rw [← he, h,_root_.sum_apply]; simp_rw [he]; rfl
  apply Module.Basis.ext_multilinear (fun _ => monBasis G)
  intro W
  let V := fun i => monBasis G (W i)
  rw [_root_.sum_apply]; simp_rw [he]
  change moment G x (update V i _)= ∑ b ∈ Finset.univ.erase i, moment G x (update V b (eat _ _ _ (V b)))
  rw [show update V i _ = fun j => monBasis G (grow W i s j) from ?_, moment_basis,mon_growth x H]
  · have hq (b : Fin n) : moment G x (update V b (eat (coordinateLeg s) (x i) (x b) (V b))) =
        ∑ k ∈ (W b).support, (W b k : ℂ) * (entry s k (x i) (x b) * Wick.monomial x (takeAt W b k)) := by
      rw [show eat (coordinateLeg s) (x i) (x b) (V b) = _ from mon_eaten (coordinateLeg s) (W b) (x i) (x b)]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [MultilinearMap.map_update_smul, show update V b (monBasis G (W b - Finsupp.single k 1)) =
        fun j => monBasis G (takeAt W b k j) from funext fun j => by by_cases h : j=b <;> simp_all [takeAt,V],moment_basis]
      exact mul_assoc ..
    let f := fun b k => if b=i then 0 else entry s k (x i) (x b) * Wick.monomial x (takeAt W b k)
    simp_rw [hq]
    change (∑ p : Occ W, f p.label p.probe) = _
    rw [add_index W f,← sum_erase_add _ _ (Finset.mem_univ i)]
    rw [show (∑ k ∈ (W i).support, (W i k : ℂ) * f i k) = 0 by simp [f],add_zero]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun k hk => ?_
    rw [show f b k = _ from if_neg (Finset.mem_erase.mp hb).1]
  ext1 j; by_cases h : j=i
  · subst j; rw [update_self,grow,update_self]
    change MvPolynomial.X _ * monBasis G _ = _
    simp only [monBasis,MvPolynomial.X,MvPolynomial.coe_basisMonomials, MvPolynomial.monomial_mul,add_comm,mul_one]
  simp [grow,h,V]

/-- Algebraic symbol recursion. The coefficient hitting the other slot is
linear in p (no conjugate here). -/
lemma moment_one (p : Probe G j) (v : Fin n → WickPol G) (i : Fin n) (H : x ∈ conf n) :
    moment G x (update v i (symbol j p * v i)) =
      ∑ b ∈ Finset.univ.erase i, moment G x (update v b (eat p (x i) (x b) (v b))) := by
  classical
  let e (l : Fin (legDim G j)) : Slot G := ⟨j,l⟩
  let c (l) := p (frame G j l)
  have he : p = ∑ l : Fin (legDim G j), c l • coordinateLeg (e l) := probe_expansion p
  unfold symbol; rw [sum_mul,MultilinearMap.map_update_sum]
  simp_rw [mul_assoc, MvPolynomial.C_mul',MultilinearMap.map_update_smul,moment_X _ _ _ H]
  have ht (b : Fin n) (hb : b ≠ i) : eat p (x i) (x b) = ∑ l : Fin (legDim G j),
      (c l:ℂ) • eat (coordinateLeg (e l)) (x i) (x b) := by
    apply MvPolynomial.derivation_ext; intro k
    have hx : x i ≠ x b := (show Injective x.ofLp from H).ne hb.symm
    simp only [eat,derivation_sum_apply, Derivation.smul_apply,MvPolynomial.mkDerivation_X]
    nth_rw 1 [K_pairing p _ hx, he]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [K_pairing _ _ hx,map_mul]; exact MvPolynomial.C_mul' ..
  simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  rw [ht b (Finset.mem_erase.mp hb).1, derivation_sum_apply, MultilinearMap.map_update_sum]
  simp_rw [Derivation.smul_apply,MultilinearMap.map_update_smul]; rfl
end Recur

lemma eat_symbol (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) :
    eat p x y (symbol l q) = MvPolynomial.C (K p q x y : ℂ) := by
  classical
  let e (i : Fin (legDim G l)) : Slot G := ⟨l,i⟩
  have he : q = ∑ i : Fin (legDim G l), (q (frame G l i)) • coordinateLeg (e i) := probe_expansion q
  rw [K_pairing p q h]
  conv_rhs => rw [he]
  simp only [symbol, map_sum,map_smul,eat, Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul,map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.C_mul',deriv_scalar,MvPolynomial.mkDerivation_X, MvPolynomial.C_mul']; rfl

end YM.Maxwell.Free
