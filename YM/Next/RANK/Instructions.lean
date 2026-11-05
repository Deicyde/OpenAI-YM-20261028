import YM.Next.RANK.Ample

/-!
# Calibration cost primitives in variable-number (not weight-gradation) units
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Normal Rise Common Perch MvPolynomial Labels Configuration
open scoped Classical Topology BigOperators

variable {V Z B : Type*} {G : Gauge} {d : ℕ}

lemma scalar_bound (p : poly V) {v : ℝ} (hv : 0 ≤ v) (ht : v ≤ 1) {d : ℕ} (h : ∀ i∈p.support,d ≤ Finsupp.weight (fun _ => (1:ℕ)) i) :
    coin (factors (v:ℂ) p) ≤ v^d * coin p := by
  nth_rw 1 [p.as_sum]; rw [map_sum]; refine (Rise.collect _ zero_le_one ..).trans ?_; rw [metal, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i hi; rw [factors,jets_as]; apply (peak_cost 1 0 _ _ zero_le_one).trans
  rw [tavern,norm_pow, Complex.norm_real, Real.norm_of_nonneg hv,one_pow,one_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hv ht (h i hi)) (norm_nonneg _)
lemma factor_degree (p : poly V) (v : ℂ) : totalDegree (factors v p) ≤ totalDegree p := by rw [model]; exact ascent ..

lemma lin_tile (U : poly V →ₗ[ℂ] poly Z) (P : poly V) {C : ℝ} (h : ∀ i∈P.support,coin (U (monomial i 1))≤C) : coin (U P)≤coin P*C := by
  nth_rw 1 [P.as_sum]; rw [map_sum]; apply (Rise.collect _ zero_le_one ..).trans
  rw [metal, Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi
  have he : monomial i (coeff i P) = coeff i P • monomial i 1 := by rw [← map_smul, smul_eq_mul,mul_one]
  rw [he, map_smul]
  exact (peak_cost 1 _ _ _ zero_le_one).trans (mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg _))

lemma message (U T : poly V→ₐ[ℂ] poly Z) (A B : ℝ) (ha : 1 ≤ A) (hb : 0≤B)
    (h : ∀ i,coin (U (X i))≤A) (ht : ∀ i,coin (T (X i))≤A) (hc : ∀ i,coin (U (X i)-T (X i))≤B)
    (p : poly V) (hp : p.totalDegree≤d) :
    coin (U p - T p) ≤ coin p * (d * B * A^d) := by
  have hz := zero_lt_one.trans_le ha
  refine lin_tile (U.toLinearMap-T.toLinearMap) _ fun i hi => ?_
  have hV : i.sum (fun _ k => k)≤d := (MvPolynomial.le_totalDegree hi).trans hp
  let p := i.sum fun _ k => k; obtain ⟨v,hv⟩ := Common.letter i
  have hg (s : Finset (Fin p)) : coin (U (glyphs v s)) ≤ A^s.card := by
    rw [glyphs,map_prod]; refine (purchased _ zero_le_one ..).trans ?_; rw [← Finset.prod_const]; exact Finset.prod_le_prod (fun i _ => sign _ _ zero_le_one) fun i _ => h _
  have hs (s : Finset (Fin p)) : coin (U (glyphs v s)-T (glyphs v s)) ≤ s.card* B*A^s.card := by
    induction s using Finset.induction_on with
    | empty => simp only [glyphs,Finset.prod_empty,map_one,sub_self,coin,pay_nothing,Finset.card_empty,Nat.cast_zero,zero_mul,le_rfl]
    | @insert a s ha' H =>
      let p := glyphs v s
      let z := X (v a) (R:=ℂ)
      rw [show glyphs v (insert a s)=z*p from Finset.prod_insert ha',map_mul,map_mul,show U z*_-T z*_= (U z-T z)*U p+T z*(U p -T p) from by ring]
      apply (Rise.taller _ zero_le_one _ _).trans
      rw [Finset.card_insert_of_notMem ha']; apply (add_le_add ((funds _ zero_le_one ..).trans
        (mul_le_mul (hc (v a)) (hg s) (sign _ (U p) zero_le_one) hb)) ((funds _ zero_le_one ..).trans
        (mul_le_mul (ht _) H (sign _ _ zero_le_one) hz.le))).trans
      have hr := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (show s.card≤s.card+1 by omega)) hb
      push_cast; rw [pow_succ] at hr ⊢; linarith only [hr]
  rw [hv]; refine (hs Finset.univ).trans ?_
  simp only [Finset.card_univ,Fintype.card_fin]; gcongr

namespace Tariffs

-- thaw into polynomial keys is a real linear representative, quantitative inverse from l1.
def expose (F : Frame G d) : F.Coeff →ₗ[ℂ] poly (KeyIn G d) :=
    (boundKey G d).toLinearMap.comp ((localFields G d).subtype.comp F.coords.symm.toLinearMap)
lemma expose_at (F : Frame G d) (v) : expose F v=thawKey (F.coords.symm v) := rfl
lemma exposed (F : Frame G d) : Function.Injective (expose F) := by
  intro a b h
  apply F.coords.symm.injective; apply Subtype.ext
  rw [← returns (F.coords.symm a),← returns (F.coords.symm b),← expose_at, h]; rfl

def zonal (F : Frame G d) (c : ℝ) := 0 ≤ c ∧ ∀ v : F.Coeff, F.coeffSize v ≤ c* Rise.coin (expose F v)

lemma zone_cost (F : Frame G d) : ∃ c : ℝ, zonal F c := by
  let v := (expose F).leftInverse
  have he (u) : v (expose F u)=u := LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (exposed F)) _
  let U := (Finset.univ : Finset F.Index).biUnion fun i => MvPolynomial.support (expose F (Pi.single i 1))
  have hs (x : F.Coeff) : (expose F x).support ⊆ U := by
    have hx : x=∑ i,x i • Pi.single i 1 := by ext i; simp [Pi.single_apply]
    conv_lhs => rw [hx,map_sum]
    simp_rw [map_smul]
    suffices ∀ (s : Finset F.Index), (∑ i ∈ s,x i • expose F (Pi.single i 1)).support ⊆ U from this Finset.univ
    intro s; induction s using Finset.induction_on with
    | empty => simp
    | insert i s h IH =>
      rw [Finset.sum_insert h]; apply Finset.Subset.trans MvPolynomial.support_add
      exact Finset.union_subset (fun k ht => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _, MvPolynomial.support_smul ht⟩) IH
  let A i := ∑ a∈ U, ‖v (monomial a 1) i‖
  let a:= ∑ i, A i
  have ha i : 0 ≤ A i := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨a,Finset.sum_nonneg (fun i _ => ha i),fun x => ?_⟩
  let p := expose F x
  have hx i : ‖x i‖ ≤ A i*coin p := by
    rw [← show v p i=x i from congr_fun (he x) i]; nth_rw 1 [show p=_ from p.as_sum]; rw [map_sum, Finset.sum_apply]
    apply (norm_sum_le ..).trans; rw [metal,Finset.mul_sum]; apply Finset.sum_le_sum; intro k hk
    have he : monomial k (coeff k p)=coeff k p • monomial k 1 := by rw [← map_smul,smul_eq_mul,mul_one]
    rw [he,map_smul, Pi.smul_apply,norm_smul,mul_comm]
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun k => ‖v (monomial k 1) i‖) (fun _ _ => norm_nonneg _) (hs x hk)) (norm_nonneg _)
  unfold a; rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => hx i
end Tariffs
end YM.Next.Rank.LiftMark
