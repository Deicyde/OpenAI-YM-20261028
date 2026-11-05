import YM.Extra.FREE_DETECTOR_ALGEBRA.Duplex

set_option warningAsError false

/-!
# Finite Wick determinants from factorial-weighted Gram

Here the script is *orthogonal for the reflected form*, not independently
orthogonalized for the input norm. Works also for arbitrary mixtures of
engineering weights and ordinary lengths; Wick powers, not ordinary powers
in the correlations. Length zero contributes one, incl empty color cases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Maxwell Wick Pair Analysis
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {ι : Type*}

/-- Induction per factor, not just support. -/
theorem per_factor (p : ι →₀ ℕ) (C : (ι →₀ ℕ) → Prop) (hz : C 0) (h : ∀ q i, C q → C (q + Finsupp.single i 1)) : C p := by
  induction p using Finsupp.induction₂ with
  | zero => exact hz
  | add_single i a q _ _ hq =>
    have hh (a : ℕ) : C (q + Finsupp.single i a) := by
      induction a with
      | zero => simpa using hq
      | succ a ha => simpa [Finsupp.single_add, add_assoc] using h _ i ha
    exact hh a

def monoPol (q : ι →₀ ℕ) := MvPolynomial.monomial q (1:ℂ)
theorem monoPol_mul (q : ι →₀ ℕ) (i : ι) : monoPol (q+Finsupp.single i 1)=monoPol q * MvPolynomial.X i := by
  simp [monoPol,MvPolynomial.X,MvPolynomial.monomial_mul]
theorem monoPol_C : monoPol (0:ι →₀ ℕ)=1 := rfl
lemma monoScaled (q : ι →₀ ℕ) (c : ℂ) : MvPolynomial.monomial q c=c • monoPol q := by
  simp [monoPol,MvPolynomial.smul_monomial]

variable [Fintype ι] [DecidableEq ι]

def tally (d : ι → ℝ) (q : ι →₀ ℕ) := ∏ i : ι, (↑(q i).factorial:ℝ) * d i ^ q i
omit [DecidableEq ι] in
@[simp] theorem tally_zero (d : ι → ℝ) : tally d 0 = 1 := by simp [tally]
theorem tally_step (d : ι → ℝ) (q : ι →₀ ℕ) (i : ι) : tally d (q+Finsupp.single i 1)= ((q i:ℝ)+1)*d i * tally d q := by
  let f (i : ι) := (↑(q i).factorial:ℝ) * d i ^ q i
  have he (a : ι) : (↑((q+Finsupp.single i 1 : ι →₀ ℕ) a).factorial:ℝ) * d a ^ ((q+Finsupp.single i 1 : ι →₀ ℕ) a) =
      ((if i=a then ((q i:ℝ)+1)*d i else 1) * f a) := by
    by_cases ha : i=a
    · subst a; simp [f,Nat.factorial_succ,pow_succ]; ring
    simp [ha,f]
  unfold tally
  simp_rw [he, Finset.prod_mul_distrib]; simp [f,Finset.prod_mul_distrib]

omit [DecidableEq ι] in
theorem tally_pos (d : ι → ℝ) (hd : ∀ i, 0 < d i) (p : ι →₀ ℕ) : 0 < tally d p :=
  Finset.prod_pos fun i _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (hd i) _)

variable {G : Gauge} {x y : E4} {n : ℕ}

theorem aligned_script (b : ι → ProbeTower G n) (hx : x≠y) (d : ι→ℝ)
    (he : ∀ i j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then d i else 0) (p q : ι →₀ ℕ) :
    aligned G x y (encode b (monoPol p)) (encode b (monoPol q)) = if p=q then (tally d p:ℂ) else 0 := by
  revert q
  apply per_factor p
  · intro q
    by_cases h : q=0
    · subst q; rw [monoPol_C]; simp [aligned_unit]
    have ht : ∃ i : ι, q i ≠ 0 := not_forall_not.mp (fun hh => h (Finsupp.ext fun a => not_not.mp (hh a)))
    obtain ⟨i,hi⟩ := ht
    have hb : monoPol q=monoPol (q-Finsupp.single i 1)*MvPolynomial.X i := by rw [← monoPol_mul, Finsupp.sub_add_single_one_cancel hi]
    rw [monoPol_C,hb,_root_.map_mul,encode_X,_root_.map_one,aligned_one_right _ _ hx,if_neg (Ne.symm h)]
  intro p i IH q
  rw [monoPol_mul,aligned_step b hx i (d i) (he i)]
  rw [show MvPolynomial.pderiv i (monoPol q) = (q i:ℂ) • monoPol (q-Finsupp.single i 1) by
    simp [monoPol,MvPolynomial.pderiv_monomial,MvPolynomial.smul_monomial],_root_.map_smul,_root_.map_smul,IH]
  by_cases hp : q i = 0
  · have hz : ¬ p+Finsupp.single i 1=q := by intro hw; rw [←hw] at hp; simp at hp
    rw [hp,if_neg hz]; simp
  have hv : p+Finsupp.single i 1=q ↔ p=q-Finsupp.single i 1 :=
    ⟨fun h => by rw [← h,add_tsub_cancel_right],fun h => by rw [h,Finsupp.sub_add_single_one_cancel hp]⟩
  by_cases hh : p=q-Finsupp.single i 1
  · rw [if_pos hh,if_pos (hv.mpr hh),tally_step]
    have ht : q i=p i+1 := by conv_lhs => rw [← hv.mpr hh]; simp
    rw [ht]; simp [Complex.real_smul]; ring
  rw [if_neg hh,if_neg (mt hv.mp hh)]; simp

lemma bar_scaled (p : WickPol G) (c : ℂ) : barPol (c • p) = star c • barPol p := by
  rw [← MvPolynomial.C_mul',← MvPolynomial.C_mul',_root_.map_mul]; simp [barPol]

omit [Fintype ι] [DecidableEq ι] in
lemma bar_mono (b : ι → ProbeTower G n) (q : ι →₀ ℕ) : barPol (encode b (monoPol q)) = encode b (monoPol q) := by
  apply per_factor q
  · rw [monoPol_C]; simp
  intro p i h
  rw [monoPol_mul, _root_.map_mul,_root_.map_mul,h]; rw [encode_X,bar_code]

/-- General sesquilinear identity on an orthogonal script. Quantify over
*same* basis in both slots; no assumption that the basis vectors are
normalized. -/
theorem duplex_script (b : ι → ProbeTower G n) (hx : x≠y) (d : ι→ℝ)
    (he : ∀ i j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then d i else 0) (p q : MvPolynomial ι ℂ) :
    duplex x y (encode b p) (encode b q) = ∑ i ∈ p.support, p.coeff i * star (q.coeff i) * (tally d i:ℂ) := by
  classical
  unfold duplex
  have hh (p : MvPolynomial ι ℂ) : encode b p = ∑ i ∈ p.support, p.coeff i • encode b (monoPol i) := by
    calc encode b p = encode b (∑ i ∈ p.support, p.coeff i • monoPol i) := by
          apply congr_arg; simp_rw [← monoScaled]; exact p.as_sum
         _ = _ := by simp
  rw [hh p,hh q,_root_.map_sum,_root_.map_sum] -- order may q outer
  simp_rw [bar_scaled,bar_mono,LinearMap.sum_apply,_root_.map_sum,_root_.map_smul,LinearMap.smul_apply,aligned_script b hx d he]

  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte,smul_eq_mul]; ring
  · intro b _ hb; simp [Ne.symm hb]
  intro h; simp [MvPolynomial.notMem_support_iff.mp h]
end YM.Extra.FD
