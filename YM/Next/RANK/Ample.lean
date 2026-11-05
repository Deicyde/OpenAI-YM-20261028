import YM.Next.RANK.ScaleScale


/-! Cost of ordinary polynomial Wick preprocessing. Keep even degree-
0 contractions. This is a difference even if all curved coordinates are dummy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Lattice Wilson RG Marker Poly Glyph Perch Normal MvPolynomial Function Set Rise Common
open scoped Topology BigOperators Classical

variable {V Z A : Type*}

-- use decrease of original polynomial degree by two for partners.

def opq (K : Normal.Symmetric V) (r : ℂ) : Normal.Symmetric V :=
    ⟨fun i j=> (r*r)⁻¹*K.cov i j,fun i j => congr_arg (_*·) (K.symm i j)⟩
lemma model (t : ℂ) : factors (V:=V) t=exchange (fun (i:V) => Finsupp.single i t) := by ext1 i; rw [Normal.exchange_x,glyph,Finsupp.linearCombination_single, factors_X,C_mul']
lemma blend_up (K : Normal.Symmetric V) (r : ℂ) (h : r ≠ 0) (p : poly V) : factors r (milk K p)=milk (opq K r) (factors r p) := by
  have ht : scope (fun i : V => Finsupp.single i r) (opq K r)=K := by
    apply Normal.Symmetric.ext; funext i j; simp only [scope,treats,Finsupp.linearCombination_single,Pi.smul_apply,opq,smul_eq_mul]; field_simp
  simp_rw [model, prepared]; rw [ht]
lemma blends (p : poly V) (r : ℝ) (h : 1 ≤ r) : coin p≤coin (factors (r:ℂ) p) := by
  have hs : p.support ⊆ (factors (r:ℂ) p).support := by
    intro i hi; rw [mem_support_iff] at hi ⊢; rw [factors, jets_coeff]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le h).ne')) hi
  rw [metal,metal]; apply le_trans (Finset.sum_le_sum (g:=fun i => ‖coeff i (factors (r:ℂ) p)‖) (fun i hi => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => norm_nonneg _)
  rw [factors,jets_coeff,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans h)]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ h)

lemma peak_cost (R : ℝ) (w : V → ℕ) (b : ℂ) (p : poly V) (hr : 0≤R) : cents (b • p) w R≤‖b‖*cents p w R := by rw [← C_mul']; exact (funds _ hr ..).trans_eq (by rw [pay_C])

-- estimate in rank units. B depends d, not V.
lemma puff [DecidableEq Z] (Q : Normal.Symmetric V) (D n : ℕ) (e : ℝ) (he : ∀ i j, ‖Q.cov i j‖≤ e)
    (hb : 0≤e) (h : e≤1) (s : Finset Z) (g : Z → V) (hn : s.card≤n) (hp : n ≤ D) :
    coin (milk Q (glyphs g s)-glyphs g s) ≤ e*(2*(D+2))^n ∧ totalDegree (milk Q (glyphs g s)) ≤ n := by
  classical
  let C : ℝ := 2*(D+2)
  have hz : 1 ≤ C := by unfold C; linarith
  induction n generalizing s with
  | zero =>
    obtain rfl := Finset.card_eq_zero.mp (by omega : s.card=0)
    simp only [glyphs,Finset.prod_empty,Normal.pure,totalDegree_one,sub_self,coin,pay_nothing,pow_zero,mul_one]; exact ⟨hb,le_rfl⟩
  | succ n H =>
    obtain rfl|⟨i,hi⟩ := s.eq_empty_or_nonempty
    · exact ⟨by simp only [glyphs, Finset.prod_empty,Normal.pure,sub_self,coin,pay_nothing]; positivity, by simp [glyphs]⟩
    let p := s.erase i; let v := glyphs g p
    have hk : p.card≤n := by unfold p; rw [Finset.card_erase_of_mem hi]; omega
    have hg : 0 ≤ C^n := pow_nonneg (zero_le_one.trans hz) _
    have hC t (hv : t⊆p) := H t ((Finset.card_le_card hv).trans hk) (by omega)
    have hh (t : Finset Z) (ht : t ⊆ p) : coin (milk Q (glyphs g t)) ≤ 1+C^n := by
      have hv : coin (glyphs g t)≤1 := (purchased _ zero_le_one ..).trans (by simp)
      let a := glyphs g t
      rw [show milk Q a=a+(milk Q a-a) by abel]
      apply (Rise.taller _ zero_le_one ..).trans
      exact add_le_add hv ((hC t ht).1.trans (mul_le_of_le_one_left hg h))
    have hu : milk Q (glyphs g s)=X (g i) * milk Q v + ∑ j∈p,Q.cov (g i) (g j) • milk Q (glyphs g (p.erase j)) := by
      rw [show glyphs g s=X _*v from (Finset.mul_prod_erase s (fun j => X (g j)) hi).symm,feeds,skims, show v= glyphs _ _ from rfl,renew,map_sum]; simp only [map_smul]
    have h' j (h : j∈p) : p.erase j ⊆ p := Finset.erase_subset ..
    rw [hu]; constructor
    · have ht : coin (∑ j∈p,Q.cov (g i) (g j) • milk Q (glyphs g (p.erase j))) ≤ (D:ℝ)*(e*(1+C^n)) := by
        apply (Rise.collect _ zero_le_one ..).trans
        calc
          _ ≤ ∑ _∈p,e*(1+C^n) := Finset.sum_le_sum fun j H => le_trans (peak_cost 1 _ _ _ zero_le_one)
            (mul_le_mul (he (g i) (g j)) (hh _ (h' j H)) (Rise.sign _ _ zero_le_one) hb)
          _ ≤ _ := by
            rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : p.card≤ D)) (by positivity)
      rw [show glyphs g s=X _*v from (Finset.mul_prod_erase s (fun j => X (g j)) hi).symm,add_comm,add_sub_assoc, ← mul_sub]; apply (Rise.taller _ zero_le_one ..).trans; apply (add_le_add ht (Rise.funds _ zero_le_one _ _)).trans
      simp only [pay_X,one_pow,one_mul]; have hy := (hC p le_rfl).1
      change cents (milk Q _-_) 0 1 ≤ _ at hy
      change D*(e*(1+C^n))+_ ≤ e*C^(n+1); rw [pow_succ]; unfold C at *
      nlinarith only [hy,mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=n) hz) (show 0 ≤ (D:ℝ)*e by positivity),mul_nonneg hb hg]
    refine (totalDegree_add ..).trans (max_le ((totalDegree_mul ..).trans ?_) ((totalDegree_finsetSum ..).trans (Finset.sup_le fun j hj => ?_)))
    · have ht := (hC _ (le_refl p)).2
      rw [totalDegree_X]; unfold v; omega
    exact (totalDegree_smul_le ..).trans ((hC _ (h' j hj)).2.trans (Nat.le_succ _))

lemma bounds (Q : Normal.Symmetric V) (D : ℕ) (e : ℝ) (he : ∀ i j, ‖Q.cov i j‖ ≤ e) (hb : 0≤e) (h : e≤1) (p : poly V) (hp : p.totalDegree ≤ D) :
    coin (milk Q p-p) ≤ coin p*(e*(2*(D+2))^D) ∧ totalDegree (milk Q p) ≤ D := by
  classical
  let A : ℝ := e*(2*(D+2))^D
  let Y:=p.support
  have hx i (hi : i∈Y) : let P:= monomial i (1:ℂ);
                          coin (milk Q P-P) ≤ A ∧ totalDegree (milk Q P)≤ D := by
    intro P; unfold P; obtain ⟨v,hv⟩ := Common.letter i; rw [hv]; apply puff Q D D e he hb h
    · simpa using (le_totalDegree hi).trans hp
    rfl
  have he (i : V →₀ ℕ) : monomial i (coeff i p)= coeff i p • monomial i 1 := by rw [← map_smul,smul_eq_mul,mul_one]
  constructor
  · let H:= milk Q - LinearMap.id; change coin (H p) ≤ coin p*A; nth_rw 1 [p.as_sum]; rw [map_sum]; apply (Rise.collect _ zero_le_one ..).trans
    rw [metal, Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi; rw [he,map_smul (f:=H)]
    exact (peak_cost 1 _ _ _ zero_le_one).trans (mul_le_mul_of_nonneg_left (hx i hi).1 (norm_nonneg _))
  nth_rw 1 [p.as_sum]; rw [map_sum]
  refine (totalDegree_finsetSum ..).trans (Finset.sup_le fun i hi => ?_)
  rw [he, map_smul]; exact (totalDegree_smul_le ..).trans (hx i hi).2
end YM.Next.Rank.LiftMark
