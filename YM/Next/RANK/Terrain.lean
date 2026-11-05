import YM.Next.RANK.Mountain

/-!
# From Booth price to true Θ faces

Axial transport derivative costs only polynomial in path length. Use the
order n prefix induction after separating out the two terms with derivative
order n in the matrix product at the identity: in this real Frobenius norm
the identity matrix itself need not have norm 1. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Beamer Source Labels Source.Drops
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators

section calculus
variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma artillery (v : ℕ → ℝ) (P : ℕ → ℕ) (s : ℕ) (h : ∀ i,0 ≤ v i) : ∃ C : ℝ, ∃ n : ℕ,0≤C ∧ ∀ M : ℝ,1 ≤ M →
    ∀ i ≤ s,v i * M^(P i) ≤ C*M^n := by
  let R := Finset.range (s+1)
  refine ⟨∑ i∈R,v i,R.sup P,Finset.sum_nonneg (fun i _ => h i),fun M he i hi=>?_⟩
  have hx : i∈R := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact mul_le_mul (Finset.single_le_sum (fun i _ => h i) hx) (pow_le_pow_right₀ he (Finset.le_sup hx)) (pow_nonneg (zero_le_one.trans he) _)
    (Finset.sum_nonneg fun i _ => h i)
section
variable [NormedRing V] [NormedAlgebra ℝ V] {f g : E → V} (n : ℕ) {x : E}
lemma times_slope (h : ContDiffAt ℝ n f x) (hp : ContDiffAt ℝ n g x) :
    slopeCap n (f*g) x ≤ ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*slopeCap i f x*slopeCap (n-i) g x := by
  obtain ⟨s,a,b,hX⟩ := mem_nhds_iff.mp ((h.eventually (by simp)).and (hp.eventually (by simp)))
  have h : ContDiffOn ℝ n f s := fun y hy => ((a hy).1).contDiffWithinAt
  have he : ContDiffOn ℝ n g s := fun y hy => ((a hy).2).contDiffWithinAt
  have ht := norm_iteratedFDerivWithin_mul_le h he b.uniqueDiffOn hX le_rfl
  simp_rw [iteratedFDerivWithin_of_isOpen _ b hX] at ht; exact ht
private lemma strip1 (h : ContDiffAt ℝ n f x) (he : n≠0) : slopeCap n (f-1) x= slopeCap n f x := by
  change ‖iteratedFDeriv ℝ n (f-fun _=> (1:V)) x‖=_; rw [iteratedFDeriv_sub_apply h contDiffAt_const,iteratedFDeriv_const_of_ne he]; simp [slopeCap]
lemma slope0 {Q V : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Q → V) (x) : slopeCap 0 f x=‖f x‖ := norm_iteratedFDeriv_zero

private lemma axes_score {a b A B : ℝ} (h : ContDiffAt ℝ (n+1:ℕ) f x) (hp : ContDiffAt ℝ (n+1:ℕ) g x) (hx : f x=1) (h₀ : g x=1)
    (ha : slopeCap (n+1) f x ≤ a) (hb : slopeCap (n+1) g x ≤ b) (he : 0≤A) (hu : 0≤B) (hA : ∀ i,i≤n→ slopeCap i f x ≤ A)
    (hB : ∀ i,i≤n→ slopeCap i g x ≤ B) :
    slopeCap (n+1) (f*g) x ≤ a+b + ∑ i∈Finset.range (n+2), ((n+1).choose i:ℝ)*A*B := by
  let k:= n+1
  have hC : ContDiffAt ℝ (n+1:ℕ) (1:E→V) x := contDiffAt_const
  let P:= f-1; let Q:=g-1
  have hD : ContDiffAt ℝ (n+1:ℕ) (P*Q) x := (h.sub hC).mul (hp.sub hC)
  have hh : f*g=(f+Q)+ P*Q := by unfold Q P; noncomm_ring
  rw [hh]; unfold slopeCap; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ (↑(n+1:ℕ)) (f+Q) x from h.add (hp.sub hC)) hD,iteratedFDeriv_add_apply h (show ContDiffAt ℝ (↑(n+1:ℕ)) Q x from hp.sub hC)]
  apply (norm_add_le ..).trans; apply add_le_add
  · refine (norm_add_le ..).trans (add_le_add ha ?_); exact (strip1 (n+1) hp (by omega)).trans_le hb
  apply (times_slope (n+1) (show ContDiffAt ℝ (↑(n+1:ℕ)) P x from h.sub hC) (show ContDiffAt ℝ (↑(n+1:ℕ)) Q x from hp.sub hC)).trans
  apply Finset.sum_le_sum; intro i hi
  let m : ℝ := k.choose i
  have hm : 0 ≤ m := Nat.cast_nonneg _; rw [Finset.mem_range] at hi
  change m*slopeCap i (f-1) x*slopeCap (k-i) (g-1) x≤m*A*B
  by_cases hj : i=0
  · subst i; rw [slope0, Pi.sub_apply, hx, Pi.one_apply,sub_self, norm_zero,mul_zero,zero_mul]; positivity
  by_cases hr : i=k
  · rw [hr,Nat.sub_self,slope0, Pi.sub_apply,h₀, Pi.one_apply,sub_self,norm_zero,mul_zero]; positivity
  have hv : i≤n := by omega
  have hK : k-i≤n := by omega
  rw [strip1 i (h.of_le (by exact_mod_cast (Nat.le_trans hv (Nat.le_succ n)))) hj,strip1 (k-i) (hp.of_le (by exact_mod_cast hK.trans (Nat.le_succ _))) (by omega)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i hv) hm) (hB _ hK) (norm_nonneg _) (mul_nonneg hm he)

/-- Bounds on products even where Matrix.frobenius is used. -/
theorem conquer (V E : Type*) [NormedRing V] [NormedAlgebra ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] (D : ℕ) :
    ∃ (C : ℝ) (n : ℕ), 0≤C ∧ ∀ (J : List (E → V)) (x : E) (B : ℝ), 1≤B →
      (∀ i ∈ J, ContDiffAt ℝ D i x ∧ i x=1 ∧ ∀ j,j≤D → slopeCap j i x ≤ B) →
        ContDiffAt ℝ D (J.prod) x ∧ J.prod x=1 ∧ ∀ j,j≤D → slopeCap j J.prod x≤ C*((1+J.length:ℝ)*B)^n := by
  induction D with
  | zero =>
    refine ⟨‖(1:V)‖,0,norm_nonneg _,fun J x B _ h => ?_⟩
    have he (P : List (E→V)) (h : ∀ i∈P,ContDiffAt ℝ 0 i x∧ i x=1) : ContDiffAt ℝ 0 P.prod x ∧ P.prod x=1 := by
      induction P with
      | nil => exact ⟨contDiffAt_const,rfl⟩
      | cons a P IH =>
        have ⟨hp,hg⟩ := IH (fun i ht => h i (List.mem_cons_of_mem _ ht)); obtain ⟨h,he⟩ := h a List.mem_cons_self
        rw [List.prod_cons]; exact ⟨h.mul hp,by rw [Pi.mul_apply,he,hg,mul_one]⟩
    obtain ⟨ha,hb⟩ := he J (fun i hi => ⟨(by simpa only [Nat.cast_zero] using! (h i hi).1),(h i hi).2.1⟩)
    refine ⟨Nat.cast_zero (R:=WithTop ℕ∞) ▸ ha,hb,fun i H=>?_⟩
    rw [Nat.eq_zero_of_le_zero H,slope0,hb,pow_zero,mul_one]
  | succ n IH =>
    obtain ⟨C,v,hC,H⟩:=IH
    let Y := ∑ i∈Finset.range (n+2),((n+1).choose i:ℝ)
    have hz : 0 ≤ Y := by unfold Y; positivity
    let K := 1+Y*C
    have hK : 1≤K := by dsimp only [K]; linarith only [mul_nonneg hz hC]
    refine ⟨C+K,v+2,by have hp := zero_lt_one.trans_le hK; positivity,fun P x B hx hp => ?_⟩
    let D:= (1+P.length:ℝ)*B
    have hd : 1 ≤ D := le_trans hx (by unfold D; exact le_mul_of_one_le_left (zero_le_one.trans hx) (by simp))
    have hg := zero_le_one.trans hx
    let takes (L : List (E → V)) := ∀ i∈L, ContDiffAt ℝ (n+1:ℕ) i x ∧ i x=1 ∧ ∀ j,j≤n+1→ slopeCap j i x≤ B
    have hl (L) (h : takes L) (hi : L.length ≤ P.length) : L.prod x=1 ∧ ∀ i, i≤n→ slopeCap i L.prod x≤C*D^v := by
      obtain ⟨-,hv,he⟩:= H L x B hx (fun i hi => ⟨(h i hi).1.of_le (by simp), (h i hi).2.1,fun j ht=> (h i hi).2.2 j (by omega)⟩)
      refine ⟨hv,fun i h=> (he i h).trans ?_⟩
      unfold D; gcongr
    have hi (L) (h : takes L) (he : L.length≤P.length) : ContDiffAt ℝ (↑(n+1:ℕ)) L.prod x ∧ slopeCap (n+1) L.prod x≤(L.length:ℝ)* (B*K*D^v) := by
      induction L with
      | nil =>
        rw [List.prod_nil]; refine ⟨contDiffAt_const,?_⟩
        change ‖iteratedFDeriv ℝ _ (fun _ : E=> (1:V)) _‖ ≤ _; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
      | cons a L IH =>
        have hp := h a List.mem_cons_self
        have ht : takes L := fun i hi=> h i (List.mem_cons_of_mem _ hi)
        have hv : L.length ≤ P.length := le_trans (Nat.le_of_lt (List.length_cons .. ▸ Nat.lt_succ_self L.length)) he
        have hs := hl L ht hv; obtain ⟨hi,hh⟩ := IH ht hv
        rw [List.prod_cons]; refine ⟨hp.1.mul hi,(axes_score n hp.1 hi hp.2.1 hs.1 (hp.2.2 (n+1) le_rfl) hh hg (mul_nonneg hC (pow_nonneg (zero_le_one.trans hd) _)) (fun i h => hp.2.2 i (Nat.le_trans h n.le_succ)) hs.2).trans ?_⟩
        have hY : (∑ i∈Finset.range (n+2), ((n+1).choose i:ℝ)*B*(C*D^v))=Y*B*(C*D^v) := by unfold Y; simp_rw [Finset.sum_mul]
        rw [hY]
        have H : B ≤ B*D^v := le_mul_of_one_le_right hg (one_le_pow₀ hd)
        unfold K; rw [List.length_cons]; push_cast; linarith only [H]
    obtain ⟨hs,ha⟩ := hi P hp le_rfl; have h := hl P hp le_rfl; let d:=v+2
    have he : 0≤K := zero_le_one.trans hK
    refine ⟨hs,h.1,fun i hi => ?_⟩; change slopeCap i _ _≤ (C+K)*D^d
    by_cases hv : i=n+1
    · rw [hv]; apply ha.trans
      have he' : (P.length:ℝ)* B ≤ D := by dsimp [D]; linarith only [hx];
      calc
        _ = ((P.length:ℝ)*B)*(K*D^v) := by ring
        _ ≤ D*(K*D^v) := mul_le_mul_of_nonneg_right he' (mul_nonneg he (pow_nonneg (zero_le_one.trans hd) _))
        _ = K*D^(v+1) := by ring
        _ ≤ _ := by unfold d; gcongr <;> linarith only [hC,hK]
    apply (h.2 i (by omega)).trans; unfold d; gcongr <;> linarith only [hC,hK]
end
section
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma strap (F : E → V) (H : V → W) (x : E) (n : ℕ) (he : ContDiffAt ℝ n F x) (h : ContDiffAt ℝ n H (F x)) (a b : ℝ) (hx : ∀ i,i ≤ n → slopeCap i H (F x)≤a)
    (hg : ∀ i, 1 ≤ i → i≤n → slopeCap i F x≤ b^i) : slopeCap n (H∘F) x ≤ n.factorial*a*b^n := by
  obtain ⟨s,hh,hU,hV⟩ := mem_nhds_iff.mp (h.eventually (by simp))
  have ho := he.continuousAt.preimage_mem_nhds (hU.mem_nhds hV)
  obtain ⟨S,hs,hS,hX⟩ := mem_nhds_iff.mp ((he.eventually (by simp)).and ho)
  have hm : MapsTo F S s := fun x he => (hs he).2
  have h : ContDiffOn ℝ n H s := fun i hi => (show ContDiffAt ℝ n H i from hh hi).contDiffWithinAt
  have he : ContDiffOn ℝ n F S := fun i hi => (show ContDiffAt ℝ n F i from (hs hi).1).contDiffWithinAt
  have hv : ‖iteratedFDerivWithin ℝ n (H∘F) S x‖ ≤ _ := norm_iteratedFDerivWithin_comp_le h he le_rfl hU.uniqueDiffOn hS.uniqueDiffOn hm hX (C:=a) (D:=b)
    (fun i hi=> by rw [iteratedFDerivWithin_of_isOpen _ hU hV]; exact hx i hi) (fun i hi hh=> by rw [iteratedFDerivWithin_of_isOpen _ hS hX]; exact hg i hi hh)
  rw [iteratedFDerivWithin_of_isOpen _ hS hX] at hv; exact hv
end
end calculus
end YM.Next.Rank.Spindle
