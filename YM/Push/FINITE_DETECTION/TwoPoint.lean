import YM.Bid.Craft
import YM.Next.FOUNDATIONS.SU2
import YM.Push.FINITE_DETECTION.Polarize

/-!
# Positive Wick norm of the local polynomial at a single reflected pair

Proof by a real position-space
triangular basis change, rather than the spatial Fourier argument there.

This concerns only the actual free kernel `Maxwell.Wick`.

Includes arity
zero monomials (empty matching).

Distinct sites at relative pole, so no
coincidence value, no distributional extensions used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Free
open Function Set Filter Maxwell Wick Wick.Occ Equiv Kelvin
open scoped Topology BigOperators ContDiff ComplexConjugate
variable {G : Gauge}

def detectors := points ![pole,(0:E4)]
lemma detectors_in : detectors ∈ conf 2 := by
  intro i j he
  fin_cases i <;> fin_cases j <;> (first | rfl | exact ((show pole ≠ 0 from pole_in) he).elim | exact ((show pole ≠ 0 from pole_in) he.symm).elim)

def wickPair : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ :=
  let M := moment G detectors
  let T i (u : Fin 2 → WickPol G) := M.toLinearMap u i
  have he a b c : T 0 ![a,b] c = M ![c,b] := by unfold T; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  have ht a b c : T 1 ![a,b] c = M ![a,c] := by unfold T; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  LinearMap.mk₂ ℂ (fun a b => M ![a,b])
    (fun a b u => by simpa only [he] using (T 0 ![a,u]).map_add a b)
    (fun c a u => by simpa only [he] using (T 0 ![a,u]).map_smul c a)
    (fun a u v => by simpa only [ht] using (T 1 ![a,u]).map_add u v)
    (fun c a u => by simpa only [ht] using (T 1 ![a,u]).map_smul c u)

variable {W : Powers G 2}
lemma front_corner (P : Matching W) {a : Occ W} : a ∈ corners P ↔ a.label = 0 := by
  have hd := different P a
  simp only [corners,Finset.mem_filter,Finset.mem_univ,true_and]
  revert hd; generalize a.label = i; generalize (partner P a).label = j
  fin_cases i <;> fin_cases j <;> decide
lemma from_corner (P : Matching W) {a : Occ W} (ha : a ∈ corners P) : (partner P a).label = 1 := by
  have hd := different P a
  rw [(front_corner P).mp ha] at hd
  revert hd; generalize (partner P a).label = j; fin_cases j <;> decide

def amplitude (P : Matching W) := ∏ a ∈ corners P, if a.probe = (partner P a).probe then lengthSq a.probe else 0
lemma amplitude_nonneg (P : Matching W) : 0 ≤ amplitude P :=
  Finset.prod_nonneg (fun _ _ => by split_ifs; exact (lengthSq_pos _).le; exact le_rfl)

lemma pair_test (W : Powers G 2) :
    wickPair (forward G (monBasis G (W 0))) (reversed G (monBasis G (W 1))) = ↑(∑ P : Matching W, amplitude P) := by
  let u (a : Occ W) := if a.label=0 then eigenVar a.probe else reflectedVar a.probe
  have hs : (fun i => ∏ a ∈ stationed W i, ordinary G (u a)) =
      ![forward G (monBasis G (W 0)),reversed G (monBasis G (W 1))] := by
    simp_rw [← stationed_powers, map_prod]; ext1 i
    fin_cases i
    · change _ = ∏ a ∈ stationed W 0, _
      refine Finset.prod_congr rfl fun a ha => ?_; simp [u,(Finset.mem_filter.mp ha).2,forward]
    change _ = ∏ a ∈ stationed W 1, _
    apply Finset.prod_congr rfl; intro a ha; simp [u,(Finset.mem_filter.mp ha).2, reversed,show (1 : Fin 2) ≠ 0 from one_ne_zero]
  have he := linear_substitution u detectors
  rw [hs] at he
  change moment G detectors _ = _
  rw [he, Complex.ofReal_sum]; refine Finset.sum_congr rfl fun P _ => ?_
  rw [amplitude, Complex.ofReal_prod]; apply Finset.prod_congr rfl; intro a ha
  rw [show (fun i j : Slot G => entry i j (detectors a.label) (detectors (partner P a).label)) =
      (fun i j => (legKernel (coordinateLeg i) (coordinateLeg j) pole : ℂ)) by
    rw [(front_corner P).mp ha,from_corner P ha]; simp [entry,detectors]]
  change Q G (u a) _ = _
  rw [show u a = eigenVar a.probe from if_pos ((front_corner P).mp ha),
    show u (partner P a) = reflectedVar _ from if_neg ((from_corner P ha).symm ▸ one_ne_zero),pairing_var]
  split_ifs <;> simp

lemma off (P : Matching W) (h : W 0 ≠ W 1) : amplitude P = 0 := by
  classical
  by_contra! hp
  have he (a) (ha : a.label = 0) : a.probe = (partner P a).probe := by
    have ht := Finset.prod_ne_zero_iff.mp (show amplitude P ≠ 0 from hp) a ((front_corner P).mpr ha)
    exact by_contra fun hn => ht (if_neg hn)
  have he0 (a : Occ W) : a ∈ stationed W 0 ↔ a ∈ corners P := by simp [stationed,front_corner]
  apply h; apply (monBasis G).injective
  simp_rw [← stationed_powers]
  refine Finset.prod_bij (fun a _ => partner P a) (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _,from_corner P ((he0 a).mp ha)⟩)
    (fun _ _ _ _ h => (partner P).injective h) (fun b hb => ⟨partner P b, (he0 _).mpr ?_,turn ..⟩) (fun a ha => congr_arg _ (he a (Finset.mem_filter.mp ha).2))
  apply (orientation P b).mpr
  rw [front_corner,(Finset.mem_filter.mp hb).2]
  exact one_ne_zero

private lemma switches (W : Powers G 2) (h : W 0 = W 1) : ∃ P : Matching W, ∀ a, (partner P a).probe = a.probe := by
  have he (i : Fin 2) : W i.rev = W i := by fin_cases i; exact h.symm; exact h
  let s (a : Occ W) := atSlot a.label.rev a.probe a.index (he _ ▸ a.legit)
  have hs (a : Occ W) : s (s a) = a := Occ.ext (Fin.rev_rev _) rfl rfl
  let e : Perm (Occ W) := ⟨s,s,hs,hs⟩
  have hv (i : Fin 2) : i.rev ≠ i := by fin_cases i <;> decide
  exact ⟨⟨e,Equiv.ext hs,fun a => hv _⟩,fun a => rfl⟩

lemma wick_pos (p : Slot G →₀ ℕ) : 0 < ∑ P : Matching ![p,p], amplitude P := by
  obtain ⟨P,hP⟩ := switches ![p,p] rfl
  refine Finset.sum_pos' (fun q _ => amplitude_nonneg q) ⟨P,Finset.mem_univ _, Finset.prod_pos (fun i _ => ?_)⟩
  simpa only [hP,if_true] using lengthSq_pos i.probe

lemma wick_orth (p q : Slot G →₀ ℕ) : wickPair (forward G (monBasis G p)) (reversed G (monBasis G q)) =
    if p=q then (↑(∑ P : Matching ![p,p], amplitude P) : ℂ) else 0 := by
  have he := pair_test ![p,q]
  change wickPair (forward G (monBasis G p)) (reversed G (monBasis G q)) = _ at he
  rcases eq_or_ne p q with h|h
  · subst q; rw [if_pos rfl]; exact he
  rw [he,if_neg h, Finset.sum_eq_zero (fun P _ => off P h),Complex.ofReal_zero]

lemma as_coeff (p : WickPol G) : p = ∑ i ∈ p.support, MvPolynomial.coeff i p • monBasis G i := p.as_sum.trans (by
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = _ • MvPolynomial.monomial i 1
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial,mul_one])

lemma barred_sum (p : WickPol G) : barred p = ∑ i ∈ p.support, star (MvPolynomial.coeff i p) • monBasis G i := by
  conv_lhs => unfold barred; arg 2; rw [as_coeff p]
  rw [map_sum]
  apply Finset.sum_congr rfl; intro i _
  change _ = _ • MvPolynomial.monomial _ _
  simp_rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.map_C]; congr 1
  change MvPolynomial.map _ (MvPolynomial.monomial i 1) = MvPolynomial.monomial i 1; simp

/-- Actual reflected free norm at a pair, via the triangular probe basis.
No RP/support assumptions on any Wilson family in this free calculation. -/
theorem positive (p : WickPol G) (hp : p ≠ 0) : 0 < (wickPair (forward G p) (reversed G (barred p))).re := by
  classical
  let c (i) := MvPolynomial.coeff i p
  let s i := ∑ P : Matching ![i,i], amplitude P (G := G)
  have he i (hi : i ∈ p.support) :
      ∑ j ∈ p.support, (c i * (star (c j) * wickPair (forward G (monBasis G i)) (reversed G (monBasis G j)))) =
      (Complex.normSq (c i) * s i : ℝ) := by
    simp_rw [wick_orth, ← mul_assoc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq p.support,if_pos hi,Complex.star_def,Complex.mul_conj, Complex.ofReal_mul]
  conv_rhs => arg 1; lhs; arg 2; rw [as_coeff p]
  rw [barred_sum]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; simp_rw [mul_left_comm (star (MvPolynomial.coeff _ p)) (MvPolynomial.coeff _ p)]
  change 0 < (∑ i ∈ p.support, ∑ j ∈ p.support, c i * (star (c j) * wickPair (forward G (monBasis G i)) (reversed G (monBasis G j)))).re
  rw [Finset.sum_congr rfl he, ← Complex.ofReal_sum,Complex.ofReal_re]
  obtain ⟨i,hi⟩ := not_forall.mp (fun h => hp (MvPolynomial.eq_zero_iff.mpr h))
  exact Finset.sum_pos (fun j hj => mul_pos (by
    apply lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm ?_); exact mt Complex.normSq_eq_zero.mp (MvPolynomial.mem_support_iff.mp hj))
    (wick_pos j)) ⟨i,MvPolynomial.mem_support_iff.mpr hi⟩

theorem two_detect {d} (v : Labels.Label G d) (hv : v ∉ equationIdeal G d) :
    0 < (moment G detectors ![observable G d v, observable G d (Labels.tensor σ (Labels.realBar v))]).re := by
  obtain ⟨p,hp⟩ := forward_full G (observable G d v)
  change 0 < (wickPair _ _).re
  rw [reversed_observable hp.symm,← hp]; exact positive p (fun hw => hv (hp.symm.trans (by rw [hw,map_zero])))
end YM.Push.FiniteDetection.Free
