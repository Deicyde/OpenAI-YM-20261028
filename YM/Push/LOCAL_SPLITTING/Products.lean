import YM.Push.LOCAL_SPLITTING.Calculus

/-!
# Multi-factor local bulk inputs to a singleton split

This is product formation on regular fields (e.g., starting with transported
canonical components), not a claim of closure of a many-marker RG system or of
independence. Keep every stencil. Pay for the number of differentiated factors
only at the number of derivatives tested, also when reanchoring ALL at once.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side} {ι : Type*}
private theorem chart_prod (s : Finset ι) {k : ℕ} (f : ι → Config G n → ℂ) {U : Config G n}
    (h : ∀ i∈s, Chart k (f i) U) : Chart k (∏ i∈s, f i) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact contDiffAt_const
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i (by simp)).mul (ih fun j hj => h j (by simp [hj]))

/-- The pointwise Leibniz cost even for an empty product or 0-jet. -/
theorem left_prod_bound (s : Finset ι) (f : ι → Config G n → ℂ) {U : Config G n}
    {D : Directions G n → Prop} {a : ι → ℝ} {k : ℕ} (h : ∀ i∈s, Chart k (f i) U)
    (hc : ∀ i∈s, ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → ‖leftDerivs (f i) l U‖ ≤ a i) :
    ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) →
      ‖leftDerivs (∏ i ∈ s, f i) l U‖ ≤ (s.card:ℝ)^l.length * ∏ i∈s, a i := by
  classical
  intro l hl hD
  induction l using List.reverseRecOn generalizing f k with
  | nil => simp only [leftDerivs, List.length_nil, Finset.prod_apply, norm_prod, pow_zero,one_mul]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => hc i hi [] hl hD)
  | append_singleton l A ih =>
    let f' (i j : ι) := if j = i then leftDerivs (f i) [A] else f j
    have he : l.length+1 ≤ k := by simpa using hl
    have hx (i) (hi : i∈s) (j) (hj : j∈s) : Chart l.length (f' i j) U := by
      unfold f'; split
      · exact leftDerivs_chart _ l.length ((h i hi).of_le (Nat.cast_le.mpr (Nat.add_comm .. ▸ he)))
      exact (h j hj).of_le (Nat.cast_le.mpr (Nat.le_of_succ_le he))
    have ht : leftDerivs (∏ i ∈ s, f i) [A] ∘ increment U =ᶠ[𝓝 0] (∑ i∈s, ∏ j∈s, f' i j) ∘ increment U := by
      have h' (i) (hi : i∈s) : ∀ᶠ x in 𝓝 0, Chart k (f i) (increment U x) :=
        chart_eventually (by rw [Work.G07.at_zero_increment]; exact h i hi) fun j => by simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
      filter_upwards [(s.eventually_all).2 h'] with x hx
      have hy (i) (hi : i∈s) := left_has A (l:=[]) (by simp; omega) (hx i hi)
      have hh := (HasDerivAt.fun_finsetProd hy).deriv
      simp only [zero_smul,Work.G07.at_zero_increment,leftDerivs] at hh
      simp only [comp_apply,leftDerivs, Finset.prod_apply,Finset.sum_apply,hh]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.prod_erase_mul _ _ hi]; unfold f'; rw [if_pos rfl]; simp only [leftDerivs, smul_eq_mul]; congr 1
      exact Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [Work.G07.left_append,left_congr l U ht,left_sum _ _ U l (fun i hi => chart_prod s (f' i) (hx i hi)) le_rfl]
    have hcost (i : ι) (hi : i∈s) := ih (f' i) (hx i hi) (by
      intro j hj l' hl' hD'; unfold f'; split
      · rename_i he; subst j; rw [← Work.G07.left_append]; exact hc _ hj _ (by simp; omega) (by
          intro v hv; obtain hh|hh := List.mem_append.mp hv
          · exact hD' _ hh
          exact hD _ (List.mem_append_right _ hh))
      exact hc _ hj _ (by omega) hD') le_rfl (fun v hv => hD v (by simp [hv]))
    apply (norm_sum_le ..).trans
    exact (Finset.sum_le_sum hcost).trans_eq (by rw [Finset.sum_const]; simp; ring)

section Products
variable {B : BudgetPoint} {Y : Support n}

theorem regular_prod (s : Finset ι) (f : ι → Config G n → ℂ) (h : ∀ i∈s, B.Regular Y (f i)) : B.Regular Y (∏ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact regular_const _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact regular_mul (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem price_product (s : Finset ι) (f : ι → Config G n → ℂ) (a : ι → ℝ) (o : Site n) (b : ι → Site n)
    (R : ℕ) (hb : ∀ i∈s, separation (b i) o ≤ R) (X : ι → Support n) (hx : ∀ i∈s,X i ⊆ Y)
    (h : ∀ i∈s, B.Regular (X i) (f i)) (hg : ∀ i∈s, B.supBounds (b i) (X i) (f i) (a i)) :
    B.Regular Y (∏ i∈s, f i) ∧ B.supBounds o Y (∏ i∈s, f i) (((s.card+1:ℕ)*(1+(R:ℝ))^B.power)^B.order * ∏ i∈s, a i) := by
  have hs := regular_prod s f (fun i hi => regular_larger (h i hi) (hx i hi))
  have ha : 0 ≤ ∏ i∈s, a i := Finset.prod_nonneg fun i hi => (hg i hi).1
  refine ⟨hs, by positivity, fun U hu l hl hd => ?_⟩
  let D (v : Directions G n) := ∀ i∈s, B.dirBound (b i) v
  let r : ℝ := (1+(R:ℝ))^B.power
  have hr : 1 ≤ r := one_le_pow₀ (by simp)
  let l' := l.map (r⁻¹ • ·)
  have hD : ∀ v∈l', D v := by
    simp only [l',List.forall_mem_map]; intro v hv i hi e
    have he : (1+(separation e.1 o : ℝ))^B.power ≤ r*(1+(separation e.1 (b i):ℝ))^B.power := by
      unfold r; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity)
      have ht : (separation e.1 o : ℝ) ≤ (separation e.1 (b i) : ℝ)+(R:ℝ) := by exact_mod_cast (separation_triangle e.1 (b i) o).trans (Nat.add_le_add_left (hb _ hi) _)
      nlinarith [show (0:ℝ) ≤ (R:ℝ)*(separation e.1 (b i):ℝ) from by positivity]
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    apply (mul_le_mul_of_nonneg_left ((hd _ hv e).trans (mul_le_mul_of_nonneg_left he B.threshold_pos.le)) (by positivity : 0 ≤ r⁻¹)).trans_eq
    field_simp [(zero_lt_one.trans_le hr).ne']
  have hy i hi := Finset.disjoint_of_subset_left (hx i hi) hu
  have hf := left_prod_bound s f (D:=D) (U:=U) (fun i hi => (h i hi).smooth U (hy i hi)) (fun i hi l hl he => (hg i hi).2 U (hy i hi) l hl (fun v hv => he v hv i hi)) l' (by simpa [l'] using hl) hD
  rw [show l = l'.map (r • ·) from Eq.symm (by simp [l',List.map_map,comp_def,smul_smul, (zero_lt_one.trans_le hr).ne']), left_homogeneous (f:=∏ i∈s, f i) l' (hs.smooth U hu) (by simpa [l'] using hl), norm_smul, Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ r^l'.length)).trans
  rw [← mul_assoc, ← mul_pow]; apply mul_le_mul_of_nonneg_right _ ha
  rw [mul_comm]; exact (pow_le_pow_left₀ (by positivity) (by push_cast; linarith : (s.card:ℝ)*r ≤ ((s.card+1 : ℕ) : ℝ)*r) l'.length).trans (pow_le_pow_right₀ (by push_cast; nlinarith) (by simpa [l'] using hl))

theorem product_masked (s : Finset ι) (f : ι → Config G n → ℂ) (X : ι → Support n) (t : ℝ) :
    (∏ i ∈ s, masked t (X i) (f i)) = masked t (s.biUnion X) (∏ i∈s, f i) := by
  classical
  funext U; rw [Finset.prod_apply]
  by_cases h : Healthy t (s.biUnion X) U
  · rw [masked_eq _ _ _ _ h, Finset.prod_apply]; exact Finset.prod_congr rfl fun i hi => masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem X hi) h)
  rw [masked_ne _ _ _ _ h]
  simp only [Healthy,Finset.disjoint_left,not_forall] at h
  obtain ⟨x,h⟩ := h
  by_cases hx : x∈s.biUnion X
  · obtain ⟨i,hi,hy⟩ := Finset.mem_biUnion.mp hx
    refine Finset.prod_eq_zero hi (masked_ne _ _ _ _ (fun H => ?_))
    simp [hx, Finset.disjoint_left.mp H hy] at h
  simp [hx] at h

end Products
end YM.Push.Local
