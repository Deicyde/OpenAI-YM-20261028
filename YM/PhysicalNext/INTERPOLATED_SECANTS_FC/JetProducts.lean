import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.BETA_TRANSPORT.Activity
import YM.Push.LOCAL_SPLITTING.Calculus



/-!
Full k ordered left derivatives of a product of entries and then scalar derivatives on that
same array (also normalized finite parameter differences). Using chart germs, NOT differentiating
a clipped/masked field. The factor for moving all directions is to be charged once per slot, not
once per slot per factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Lattice Wilson RG Filter Set Function Next.Foundations Push.Local
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {ι : Type*} (s : Finset ι) {G : Gauge} {n : Side} {U : Config G n}

lemma smooth_sum {j : ℕ} {t : ℝ} {f : ι → ℝ → ℝ} (h : ∀ i∈s, ContDiffAt ℝ j (f i) t) :
    ContDiffAt ℝ j (fun u => ∑ i∈s, f i u) t := by
  induction s using Finset.induction_on with
  | empty => simp [contDiffAt_const]
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma absolute_product_difference {p q h : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ i∈s, |p i| ≤ h i ∧ |q i| ≤ h i ∧ |p i-q i| ≤ δ * h i) :
    |(∏ i∈s,p i) - ∏ i∈s,q i| ≤ δ * ∏ i∈s,(2*h i) := by
  let f (g : ι → ℝ) i := if i∈s then g i else 0
  have hh i : |f p i| ≤ f h i ∧ |f q i| ≤ f h i ∧ |f p i-f q i| ≤ δ*f h i := by
    by_cases hi:i∈s <;> simp [f, hi,hb]
  have H := Push.BetaTransport.product_diff hδ (f p) (f q) (f h) (fun i => (hh i).1) (fun i => (hh i).2.1)
    (fun i => (hh i).2.2) s
  simpa +contextual [f] using H

private def differentiated (f : ι → ℝ → ℝ) (i : ι) := update f i (deriv (f i))

lemma scalar_product {f : ι → ℝ → ℝ} {k : ℕ} {t : ℝ} {c : ι → ℝ}
    (hf : ∀ i∈s, ContDiffAt ℝ k (f i) t) (he : ∀ i∈s, ∀ j ≤ k, |iteratedDeriv j (f i) t| ≤ c i) :
    |iteratedDeriv k (fun u => ∏ i∈s,f i u) t| ≤ (s.card:ℝ)^k * ∏ i∈s,c i := by
  induction k generalizing f with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul,Finset.abs_prod]; exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => he i hi 0 le_rfl)
  | succ k ih =>
    have hx i (hi : i∈s) j (hj : j∈s) : ContDiffAt ℝ k (differentiated f i j) t ∧
        ∀ v≤k, |iteratedDeriv v (differentiated f i j) t| ≤ c j := by
      by_cases hm : j=i
      · subst j; rw [differentiated,update_self]; exact ⟨(hf i hi).derivWithin (by push_cast; rfl),fun v hv => by
          rw [← iteratedDeriv_succ']; exact he i hi (v+1) (by omega)⟩
      rw [differentiated,update_of_ne hm]; exact ⟨(hf j hj).of_le (Nat.cast_le.mpr (Nat.le_succ k)),fun v hv => he j hj v (by omega)⟩
    have hr : deriv (fun u => ∏ i∈s,f i u) =ᶠ[𝓝 t] fun u => ∑ i∈s,∏ j∈s,differentiated f i j u := by
      filter_upwards [(s.eventually_all).mpr (fun i hi => (hf i hi).eventually (by simp))] with u hu
      rw [(HasDerivAt.fun_finsetProd (u:=s) fun i hi => ((hu i hi).differentiableAt (by simp)).hasDerivAt).deriv]
      exact Finset.sum_congr rfl fun i hi => by
        rw [← Finset.prod_erase_mul _ _ hi,differentiated,update_self, smul_eq_mul]; congr 1
        exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [iteratedDeriv_succ',hr.iteratedDeriv_eq, iteratedDeriv_fun_sum (fun i hi => contDiffAt_prod (fun j hj => (hx i hi j hj).1))]
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun i hi => ih (fun j hj => (hx i hi j hj).1) (fun j hj =>
      (hx i hi j hj).2))).trans_eq (by simp; ring))

abbrev Field (G : Gauge) (n : Side) := Config G n → ℝ
private def moved (f : ι → Field G n) (A : Directions G n) (i : ι) := update f i (leftDerivs (f i) [A])
omit s in
private lemma testing {f : ι → Field G n} {k m : ℕ} (hk : m<k) {i j : ι} (h : Chart k (f i) U)
    (he : Chart k (f j) U) (A : Directions G n) : Chart m (moved f A i j) U := by
  unfold moved
  by_cases hj : j=i
  · rw [hj,update_self]; exact leftDerivs_chart _ m (h.of_le (Nat.cast_le.mpr (by simp; omega)))
  rw [update_of_ne hj]; exact he.of_le (Nat.cast_le.mpr hk.le)

private lemma expansion {k : ℕ} (l : List (Directions G n)) (f : ι → Field G n) (hl : l.length<k)
    (hf : ∀ i∈s, Chart k (f i) U) (A : Directions G n) :
    leftDerivs (fun v => ∏ i∈s,f i v) (l++[A]) U = ∑ i∈s,leftDerivs (fun v => ∏ j∈s, moved f A i j v) l U := by
  let F i v := ∏ j∈s, moved f A i j v
  have h' i (hi : i∈s) : ∀ᶠ v in 𝓝 0, Chart k (f i) (increment U v) := chart_eventually (by rw [Work.G07.at_zero_increment]; exact hf i hi)
    (fun j => by simp only [increment,G.mat_mul]; exact (G.exp_jet.comp (contDiff_apply ..)).contDiffAt.mul contDiffAt_const)
  have H : leftDerivs (fun v => ∏ i∈s,f i v) [A] ∘ increment U =ᶠ[𝓝 0] (∑ i∈s,F i) ∘ increment U := by
    filter_upwards [(s.eventually_all).2 h'] with t ht
    simp only [comp_apply,leftDerivs, Finset.sum_apply]
    have he := (HasDerivAt.fun_finsetProd (u:=s) fun i hi => left_has A (l:=[]) (by simp; omega) (ht i hi)).deriv
    dsimp only [leftDerivs] at he
    rw [he]
    apply Finset.sum_congr rfl; intro i hi
    unfold F; rw [← Finset.prod_erase_mul _ _ hi,moved,update_self,zero_smul,Work.G07.at_zero_increment, smul_eq_mul]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Work.G07.left_append,left_congr _ _ H,left_sum s F U l (fun i hi => contDiffAt_prod (fun j hj => testing hl (hf i hi) (hf j hj) A)) le_rfl]

section Motion
variable {D : Directions G n → Prop} {k N : ℕ} {r : Set ℝ} {f : ℝ → ι → Field G n}

omit s in
private lemma moved_prices {A : Directions G n} {l : List (Directions G n)} {i j : ι} {H : (ℝ→ℝ) → Prop}
    (h : ∀ l : List (Directions G n), l.length ≤ k → (∀ a∈l,D a) → H (fun t => leftDerivs (f t j) l U))
    (hA : D A) (hl : l.length < k) (he : ∀ a∈l,D a) : H (fun t => leftDerivs (moved (f t) A i j) l U) := by
  by_cases hj : j=i
  · subst j; simp_rw [moved, update_self, ← Work.G07.left_append]; exact h _ (by simp; omega) fun v hv => by simpa using
      (show D v from (List.mem_append.mp hv).elim (he v) fun hh => (List.mem_singleton.mp hh) ▸ hA)
  simp_rw [moved, update_of_ne hj]; exact h _ hl.le he

lemma left_product_continuous (hf : ∀ t∈r,∀ i∈s, Chart k (f t i) U)
    (he : ∀ i∈s, ∀ l : List (Directions G n), l.length ≤ k → (∀ a∈l,D a) → ContinuousOn (fun t => leftDerivs (f t i) l U) r)
    (l : List (Directions G n)) (hl : l.length ≤ k) (hd : ∀ a∈l,D a) :
    ContinuousOn (fun t => leftDerivs (fun v => ∏ i∈s,f t i v) l U) r := by
  induction l using List.reverseRecOn generalizing f k with
  | nil => exact continuousOn_finsetProd s fun i hi => he i hi [] hl hd
  | append_singleton l A ih =>
    have hl' : l.length < k := by simp only [List.length_append,List.length_cons,List.length_nil,zero_add] at hl; omega
    exact (continuousOn_finsetSum s fun i hi => ih (fun t ht j hj => testing hl' (hf t ht i hi) (hf t ht j hj) A)
      (fun j hj l' hl' h => moved_prices (k:=k) (H:=fun F => ContinuousOn F r) (he j hj) (hd A (by simp)) (by omega) h) le_rfl (fun a ha=> hd a (by simp [ha]))).congr
        (fun t ht => expansion s l _ hl' (hf t ht) A)

/-- Mixed derivatives on a pre-mask piece; do the V derivatives FIRST, in their stipulated order. -/
lemma mixed_product {c : ι → ℝ} {t : ℝ} (hf : ∀ᶠ u in 𝓝 t, ∀ i∈s, Chart k (f u i) U)
    (he : ∀ i∈s, ∀ l : List (Directions G n), l.length ≤ k → (∀ a∈l, D a) → let F := fun t => leftDerivs (f t i) l U
      ContDiffAt ℝ N F t ∧ ∀ j ≤ N, |iteratedDeriv j F t| ≤ c i)
    (l : List (Directions G n)) (hl : l.length ≤ k) (hd : ∀ a∈l,D a) : let F := fun t => leftDerivs (fun v => ∏ i∈s,f t i v) l U
    ContDiffAt ℝ N F t ∧ ∀ j ≤ N, |iteratedDeriv j F t| ≤ (s.card:ℝ)^(l.length+j) * ∏ i∈s, c i := by
  induction l using List.reverseRecOn generalizing f k with
  | nil => exact ⟨contDiffAt_prod fun i hi => (he i hi [] hl hd).1, fun j hj => (Nat.zero_add j).symm ▸ scalar_product s
      (fun i hi => (he i hi [] hl hd).1.of_le (Nat.cast_le.mpr hj)) (fun i hi _ hy => (he i hi [] hl hd).2 _ (hy.trans hj))⟩
  | append_singleton l A ih =>
    have hl' : l.length < k := by simpa using hl
    let M (i : ι) t := leftDerivs (fun v => ∏ j∈s,moved (f t) A i j v) l U
    intro F
    have hF : F =ᶠ[𝓝 t] fun t => ∑ i∈s,M i t := hf.mono fun t ht => expansion s l _ hl' ht A
    have h i (hi : i∈s) := ih (hf.mono fun t ht j hj => testing hl' (ht i hi) (ht j hj) A) (fun j hj l' hl' h => moved_prices
      (H:=fun F => ContDiffAt ℝ N F t ∧ ∀ j' ≤ N, |iteratedDeriv j' F t| ≤ c j) (he j hj) (hd A (by simp)) (by omega) h)
      le_rfl (fun a ha=> hd a (by simp [ha]))
    refine ⟨(smooth_sum s fun i hi => (h i hi).1).congr_of_eventuallyEq hF,fun j hj => ?_⟩
    rw [hF.iteratedDeriv_eq,iteratedDeriv_fun_sum (fun i hi => (h i hi).1.of_le (Nat.cast_le.mpr hj))]
    exact (Finset.abs_sum_le_sum_abs (fun i => iteratedDeriv j (M i) t) s).trans ((Finset.sum_le_sum (fun i hi => (h i hi).2 j hj)).trans_eq (by simp; ring))
end Motion

lemma product_change {D : Directions G n → Prop} {δ : ℝ} (hδ : 0 ≤ δ) {f g : ι → Field G n} {c : ι → ℝ} {k : ℕ}
    (hf : ∀ i∈s, Chart k (f i) U ∧ Chart k (g i) U)
    (hb : ∀ i∈s, ∀ l : List (Directions G n), l.length ≤ k → (∀ a∈l,D a) → let F := leftDerivs (f i) l U; let H := leftDerivs (g i) l U
       |F| ≤ c i ∧ |H| ≤ c i ∧ |F-H| ≤ δ*c i)
    (l : List (Directions G n)) (hl : l.length ≤ k) (hd : ∀ a∈l,D a) :
    |leftDerivs (fun v => ∏ i∈s,f i v) l U-leftDerivs (fun v => ∏ i∈s,g i v) l U| ≤ δ * ((s.card:ℝ)^l.length * ∏ i∈s,(2*c i)) := by
  induction l using List.reverseRecOn generalizing f g k with
  | nil => simpa only [leftDerivs,List.length_nil,pow_zero,one_mul] using absolute_product_difference s hδ (fun i hi => hb i hi [] hl hd)
  | append_singleton l A ih =>
    have hl' : l.length < k := by simpa using hl
    have h i (hi : i∈s) := ih (f:=moved f A i) (g:=moved g A i) (k:=l.length)
      (fun j hj => ⟨testing hl' (hf i hi).1 (hf j hj).1 A,testing hl' (hf i hi).2 (hf j hj).2 A⟩) (fun j hj m hm h => ?_) le_rfl
      (fun a ha=>hd a (by simp [ha]))
    · rw [expansion s l f hl' (fun i hi => (hf i hi).1),expansion s l g hl' (fun i hi => (hf i hi).2),← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum h).trans_eq (by simp; ring))
    by_cases hz : j=i
    · subst j; simp_rw [moved, update_self, ← Work.G07.left_append]; exact hb i hi _ (by simp; omega) (fun v hv => (List.mem_append.mp hv).elim
        (h v) fun he => hd v (List.mem_append_right _ he))
    rw [moved,update_of_ne hz,moved,update_of_ne hz]; exact hb j hj _ (hm.trans hl'.le) h
end YM.PhysicalNext.InterpolatedSecantsFc
