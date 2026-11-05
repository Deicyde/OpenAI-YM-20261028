import Mathlib.Analysis.Matrix.Order
import YM.Next.MAXWELL.Pulls


/-!
# Finite-probe Fock calculation

Uniform theorem for every arity, obtained algebraically on polynomial
smearings of Wick's finite insertions. Auxiliary finite spaces only for
given finite lists; later apply after proving the infinite hierarchy's
actual one-leg kernel is PSD. No claim of Hilbert-space construction of
an interacting theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free.Fock
open Function Set Filter Tensor Analysis MvPolynomial Finset
open scoped Topology ContDiff BigOperators ComplexOrder

variable {σ ι β : Type*}
abbrev Space (σ : Type*) := MvPolynomial σ ℂ

section Form
variable [Fintype σ]

def bill (s : σ →₀ ℕ) := ∏ i : σ, Nat.factorial (s i)

lemma bill_pos (s : σ →₀ ℕ) : 0 < bill s := prod_pos fun _ _ => Nat.factorial_pos _

lemma bill_next (s : σ →₀ ℕ) (i : σ) : bill (s+Finsupp.single i 1) = (s i+1)* bill s := by
  classical
  unfold bill; rw [← mul_prod_erase _ _ (Finset.mem_univ i),← mul_prod_erase _ (fun i => Nat.factorial (s i)) (Finset.mem_univ i),
    Finsupp.add_apply,Finsupp.single_eq_same,Nat.factorial_succ, ← mul_assoc];
  congr 1; exact prod_congr rfl (fun j hj => by simp [(Finset.mem_erase.mp hj).1.symm])

def form (p q : Space σ) := ∑ s ∈ p.support, (bill s:ℂ)* (star (MvPolynomial.coeff s p)*MvPolynomial.coeff s q)

lemma padded {p q : Space σ} {s : Finset (σ →₀ ℕ)} (hs : p.support ⊆ s) :
    form p q = ∑ i ∈ s, (bill i:ℂ)*(star (MvPolynomial.coeff i p)*MvPolynomial.coeff i q) :=
  sum_subset hs (fun i _ h => by rw [MvPolynomial.notMem_support_iff.mp h, star_zero, zero_mul,mul_zero])

lemma form_conj (p q : Space σ) : form q p=star (form p q) := by
  classical
  rw [padded (Finset.subset_union_right (s₁:=p.support)),padded (Finset.subset_union_left (s₂:=q.support)), star_sum];
  exact Finset.sum_congr rfl fun i _ => by rw [star_mul,star_mul,star_star,star_natCast,mul_comm (bill i:ℂ)]

lemma form_strict (p : Space σ) (hp : p≠0) : 0 < form p p := by
  classical
  apply Finset.sum_pos
  · intro i hi
    have h : MvPolynomial.coeff i p ≠ 0 := MvPolynomial.mem_support_iff.mp hi
    have he : (0:ℂ)<bill i := by exact_mod_cast bill_pos i
    exact mul_pos he (star_mul_self_pos (IsRegular.of_ne_zero h))
  exact nonempty_iff_ne_empty.mpr (fun h => hp (by ext1 i; simpa using MvPolynomial.notMem_support_iff.mp (by rw [h]; simp : i ∉ p.support)))

lemma form_zero (p : Space σ) : form p 0=0 := by simp [form]
lemma form_nonneg (p : Space σ) : 0 ≤ form p p := by
  by_cases h : p=0
  · rw [h,form_zero]
  exact (form_strict p h).le

lemma form_add (p q r : Space σ) : form p (q+r)=form p q+form p r := by
  simp [form,mul_add,Finset.sum_add_distrib]

lemma form_scale (p q : Space σ) (c : ℂ) : form p (c • q)=c * form p q := by
  simp only [form,MvPolynomial.coeff_smul,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma form_extend (p q r : Space σ) : form (p+q) r=form p r+form q r := by
  rw [form_conj r (p+q),form_conj r p,form_conj r q, form_add,star_add]

lemma form_rescale (p q : Space σ) (c : ℂ) : form (c • p) q=star c * form p q := by
  rw [form_conj q (c • p),form_conj q p,form_scale,star_mul,mul_comm]

def pairingR (p : Space σ) : Space σ →ₗ[ℂ] ℂ where
  toFun q := form p q
  map_add' := form_add p
  map_smul' c q := form_scale p q c

def pairingL (q : Space σ) : Space σ →ₛₗ[starRingEnd ℂ] ℂ where
  toFun p := form p q
  map_add' _ _ := form_extend _ _ _
  map_smul' c p := form_rescale p q c

lemma form_sum {s : Finset ι} (f : ι → Space σ) (p : Space σ) :
    form p (∑ i ∈ s, f i) = ∑ i ∈ s, form p (f i) := map_sum (pairingR p) f s
lemma form_gather {s : Finset ι} (f : ι → Space σ) (p : Space σ) :
    form (∑ i ∈ s, f i) p = ∑ i ∈ s, form (f i) p := map_sum (pairingL p) f s

lemma form_atom (s : σ →₀ ℕ) (a : ℂ) (p : Space σ) :
    form (MvPolynomial.monomial s a) p = (bill s:ℂ) * (star a * MvPolynomial.coeff s p) := by
  classical
  by_cases h : a=0
  · subst a; simp [form]
  simp [form,h,MvPolynomial.support_monomial]

lemma base_norm : form (1 : Space σ) 1=1 := by
  rw [show (1:Space σ) = monomial 0 1 from rfl,form_atom]; classical simp [bill]

lemma form_next (i : σ) (p q : Space σ) : form (X i * p) q = form p (pderiv i q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [X, MvPolynomial.monomial_mul, form_atom,form_atom, MvPolynomial.coeff_pderiv]
    rw [add_comm (Finsupp.single i 1),bill_next]; push_cast; simp only [one_mul]; ring
  | add p r hp hr => rw [mul_add,form_extend,form_extend,hp,hr]
end Form

section Tensor
variable [Fintype σ]

def synth (v : σ → ℂ) : Space σ := ∑ i : σ, C (v i)*X i

def testBy (v : σ → ℂ) : Derivation ℂ (Space σ) (Space σ) := MvPolynomial.mkDerivation ℂ (fun i => C (star (v i)))

lemma test_pays (u v : σ → ℂ) : testBy u (synth v) = C (∑ i : σ, star (u i)*v i) := by
  simp only [testBy,synth,map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_mul', Derivation.map_smul, MvPolynomial.mkDerivation_X,map_mul,mul_comm]; exact (C_mul' ..).symm

lemma form_joins (u : σ → ℂ) (p q : Space σ) : form (synth u*p) q=form p (testBy u q) := by
  classical
  have he (q : Space σ) : testBy u q = ∑ i : σ, star (u i) • pderiv i q := by
    let L := fun i : σ => (pderiv (R := ℂ) i)
    have hf (S : Finset σ) (c : σ → Derivation ℂ (Space σ) (Space σ)) (p : Space σ) :
        (∑ i ∈ S,c i) p = ∑ i ∈ S,c i p := by
      induction S using Finset.induction_on with | empty => simp | @insert i s hi ih => simp [hi,Derivation.add_apply,ih]
    have hp : testBy u = ∑ i, star (u i) • L i := derivation_ext (fun i => by
      unfold testBy; rw [MvPolynomial.mkDerivation_X]; simp [L,pderiv_X, hf, Derivation.smul_apply,Pi.single_apply, smul_ite, ← MvPolynomial.C_mul'] )
    rw [hp,hf]; simp_rw [Derivation.smul_apply]; rfl
  rw [synth,sum_mul,form_gather _ q,he,form_sum]
  apply Finset.sum_congr rfl; intro i _; rw [mul_assoc,MvPolynomial.C_mul',form_rescale,form_next,form_scale]

/-- Fock tensor of a list on one side, with internal kernel. -/
def packet (E : β → β → ℂ) (L : β → σ → ℂ) : (u : List β) → Space σ
  | [] => 1
  | a::r => synth (L a)*packet E L r + ∑ i : Fin r.length, E a (r.get i) • packet E L (r.eraseIdx i.val)
termination_by u => u.length
decreasing_by
  · simp
  exact lt_trans (pulls_short _) (by simp)

lemma packet_rule (E : β → β → ℂ) (L : β → σ → ℂ) (a : β) (r : List β) :
   packet E L (a::r) = synth (L a)*packet E L r + pulls r (fun b u => E a b • packet E L u) := by
  rw [packet]; rfl

lemma one_capture (E : β → β → ℂ) (L : β → σ → ℂ) (u : σ → ℂ) (r : List β) :
    testBy u (packet E L r) = pulls r (fun b w => (∑ i, star (u i)*L b i) • packet E L w) := by
  have scale (a : ℂ) (p : Space σ) : testBy u (a • p) = a • testBy u p := map_smul (testBy u).toLinearMap ..
  induction h : r.length using Nat.strong_induction_on generalizing r with
  | h n ih =>
    subst n; cases r with
    | nil => rw [pulls_nil,packet]; exact Derivation.map_one_eq_zero _
    | cons a t =>
      let K := packet E L
      let m (b : β) := ∑ i, star (u i) * L b i
      have he : testBy u (pulls t (fun b r => E a b • packet E L r)) =
          pulls t (fun b r => pulls r (fun c v => E a b • m c • packet E L v)) := by
        unfold pulls; rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [scale,ih _ (lt_trans (pulls_short i) (by simp)) _ rfl,pulls,Finset.smul_sum]
      have hp := pulls_twice t (fun b c v => E a b • m c • packet E L v)
      rw [packet_rule _ _ a t,map_add,he, hp, Derivation.leibniz,test_pays,ih _ (by simp) t rfl,pulls_cons]
      have hc (b : β) (v : List β) : m b • packet E L (a::v) = synth (L a) * (m b • packet E L v) + pulls v (fun c w => E a c • m b • packet E L w) := by
        rw [packet_rule,smul_add,mul_smul_comm,pulls,Finset.smul_sum]
        congr 1
        exact sum_congr rfl fun c _ => smul_comm ..
      change synth (L a) * pulls _ _ + packet E L t * C (m a) + pulls _ _ = m a • packet E L t + pulls t (fun b v => m b • packet E L (a::v))
      simp_rw [hc]
      rw [mul_comm (packet E L t),C_mul']
      unfold pulls m; simp_rw [Finset.sum_add_distrib,Finset.mul_sum]
      rw [add_comm _ ((_ : ℂ) • packet E L t),add_assoc]
lemma packet_base (E : β → β → ℂ) (L : β → σ → ℂ) (v : List β) :
    pairCost E v = form 1 (packet E L v) := by
  induction h : v.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    subst n; cases v with
    | nil => rw [pairCost,packet, base_norm]
    | cons b v =>
      have he : form 1 (synth (L b)*packet E L v) = 0 := by
        rw [form_conj _ 1,form_joins]; simp [form_zero]
      rw [pair_step,packet_rule,form_add,he,zero_add]
      unfold pulls; rw [form_sum]; apply Finset.sum_congr rfl; intro i _
      dsimp only
      rw [form_scale,ih _ (lt_trans (pulls_short i) (by simp)) _ rfl]

/-- The reflected list only needs reflected *internal* edge weights.
Combining the two lists then pairs through the cross weights (order of
list on either side arbitrary, but held fixed). -/
theorem halves (q p : β → ι) (X : ι → ι → ℂ) (E : β → β → ℂ) (L : β → σ → ℂ)
    (hq : ∀ a b, X (q a) (q b) = star (E a b)) (hp : ∀ a b, X (p a) (p b)=E a b)
    (hX : ∀ a b, X (q a) (p b) = ∑ i : σ, star (L a i) * L b i) (u v : List β) :
    pairCost X (u.map q ++ v.map p) = form (packet E L u) (packet E L v) := by
  induction h : u.length using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    subst n; cases u with
    | nil => simp_rw [List.map_nil,List.nil_append,packet, pair_transfer]
             rw [show (fun a b => X (p a) (p b)) = E from funext fun a => funext fun b => hp a b]
             exact packet_base E L _
    | cons a u =>
      rw [List.map_cons,List.cons_append,pair_step,pulls_append,pulls_map,pulls_map,packet_rule,
        form_extend,form_joins,one_capture,add_comm]
      dsimp only [pulls]; rw [form_gather,form_sum]
      -- compare internal and cross
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        rw [ih _ (by simp) _ _ rfl, form_scale,hX]
      apply Finset.sum_congr rfl; intro i _; rw [hq,form_rescale,ih _ (lt_trans (pulls_short i) (by simp)) _ _ rfl]
end Tensor
end YM.Maxwell.Free.Fock
