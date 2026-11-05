import YM.Push.ABSOLUTE_SUMS.Copies

set_option warningAsError false

/-!
# Absolute exponential-list identities

For actual summable real activities, at one finite torus. Multiplicities
at repeated address occurrences tracked in `Multiple.Reps` (one inverse
factorial per distinct address), or MAY choose a given optional h
parent only once (then it's an ordinary finset). Integrals separately.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity

open Lattice Wilson RG AbsoluteSums AbsoluteSums.Multiple Finset Filter Function
open scoped Classical BigOperators Topology

variable {ι κ : Type*}

/-- absolute product series (convenience). -/
lemma abs_mul_pair {g : ι → ℝ} {f : κ → ℝ}
    (h : Summable fun x => ‖g x‖) (l : Summable fun x => ‖f x‖) :
    Summable fun p : ι × κ => ‖g p.1 * f p.2‖ := by
  simp only [norm_mul]
  apply summable_mul_of_summable_norm (f:=fun a => ‖g a‖) (g:=fun a => ‖f a‖) <;> simp <;> assumption

universe u
private def Claim (α : Type u) [hF : Fintype α] : Prop := ∀ w : α → ι → ℝ, (∀ i, Summable fun j => ‖w i j‖) →
  let p z := ∏ i : α, w i (z i)
  Summable (fun z : α → ι => ‖p z‖) ∧ (∑' z : α → ι, p z) = ∏ i : α, ∑' j, w i j
private theorem pi_claim (α : Type u) [hF : Fintype α] : @Claim ι α hF := by
  refine Fintype.induction_empty_option (P:=@fun α h => @Claim ι α h) ?_ ?_ ?_ α (h_fintype:=hF)
  · intro a b hb e ih w h
    letI : Fintype a := Fintype.ofEquiv _ e.symm
    have hi := ih (fun i j => w (e i) j) (fun i => h (e i))
    let d : (a → ι) ≃ (b → ι) := Equiv.arrowCongr e (.refl _)
    intro p
    have hh (x : a → ι) : p (d x) = ∏ i, w (e i) (x i) := by
      unfold p; rw [← e.prod_comp]; simp [d]
    constructor
    · rw [← d.summable_iff]; change Summable (fun z => ‖p (d z)‖); simp_rw [hh]; exact hi.1
    rw [← d.tsum_eq _]
    simp_rw [hh]; rw [hi.2]; exact Fintype.prod_equiv e _ _ (fun i => rfl)
  · intro w h
    exact ⟨.of_finite, by simp [tsum_fintype]⟩
  · intro a ha ih w h
    have hi := ih (fun i j => w (some i) j) (fun i => h (some i))
    let d : ((Option a) → ι) ≃ (ι × (a → ι)) := Equiv.piOptionEquivProd
    intro p
    let f (z : a → ι) := ∏ i, w (some i) (z i)
    change Summable (fun z => ‖f z‖) ∧ (∑' z, f z) = _ at hi
    have hh (z : ι × (a → ι)) : p (d.symm z) = w none z.1 * f z.2 := by
      unfold p f; rw [Fintype.prod_option]; rfl
    constructor
    · rw [← d.symm.summable_iff]; change Summable (fun z => ‖p (d.symm z)‖); simp_rw [hh]
      exact abs_mul_pair (h none) hi.1
    rw [← d.symm.tsum_eq _, Fintype.prod_option]
    simp_rw [hh]; rw [← tsum_mul_tsum_of_summable_norm (h none) hi.1,hi.2]

/-- Finitely many independent address counters (Fintype over KEYS; values
can be infinite). -/
theorem pi_series (α : Type u) [hF : Fintype α] (w : α → ι → ℝ) (h : ∀ i, Summable fun j => ‖w i j‖) :
    let p z := ∏ i : α, w i (z i)
    Summable (fun z : α → ι => ‖p z‖) ∧ (∑' z : α → ι, p z) = ∏ i : α, ∑' j, w i j := pi_claim α w h

lemma mayer_abs (x : ℝ) : |Real.exp x-1| ≤ |x| *Real.exp |x| := by
  have ht : 0 ≤ |x| *Real.exp |x| := by positivity
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp h)),abs_of_nonneg h]
    have he := Real.add_one_le_exp (-x)
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)] at he
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr (by
    rw [show (1:ℝ)=Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_monotone (le_of_not_ge h)))]
  have he := Real.add_one_le_exp x
  have hh : |x| ≤ |x| * Real.exp |x| := le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (abs_nonneg _))
  linarith [neg_le_abs x]

theorem mayer_summable (w : ι → ℝ) (h : Summable fun i => ‖w i‖) :
    Summable fun i => ‖Real.exp (w i)-1‖ := by
  let C := ∑' i, ‖w i‖
  have he i : ‖w i‖ ≤ C := by
    exact h.le_tsum i (fun i _ => norm_nonneg _)
  apply (h.mul_right (Real.exp C)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i; exact (mayer_abs (w i)).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (he i)) (abs_nonneg _))

/-- The Mayer product formula, incl $∅$. -/
theorem mayer (w : ι → ℝ) (h : Summable fun i => ‖w i‖) :
    let f i := Real.exp (w i)-1
    Summable (fun s : Finset ι => ‖∏ i∈s,f i‖) ∧
    Real.exp (∑' i,w i) = ∑' s : Finset ι,∏ i∈s,f i := by
  intro f; have he : Summable (fun i => ‖f i‖) := mayer_summable w h
  have hf : Summable (fun s : Finset ι => ‖∏ i∈s,f i‖) := by
    simpa only [norm_prod] using summable_finsetProd_of_summable_nonneg (fun i => norm_nonneg (f i)) he
  refine ⟨hf,?_⟩
  rw [← tprod_one_add hf.of_norm]
  have hh : (fun i => Real.log (1+f i)) = w := by ext; simp [f]
  have hg i : 0 < 1+f i := by simpa [f,add_sub_cancel_left] using Real.exp_pos (w i)
  rw [← Real.rexp_tsum_eq_tprod hg (hh.symm ▸ h.of_norm)]; change Real.exp _ = Real.exp (tsum (fun _ => _)); rw [hh]

private lemma powers (x : ℝ) : HasSum (fun n : ℕ => x^(n+1) / (n+1).factorial) (Real.exp x - 1) := by
  have ht : HasSum (fun n : ℕ => x^n / n.factorial) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  simpa using (hasSum_nat_add_iff' 1).mpr ht

private lemma powers_norm (x : ℝ) : Summable fun n : ℕ => ‖x^(n+1) / (n+1).factorial‖ := by
  simpa [Real.norm_eq_abs] using (powers |x|).summable

private lemma fibre (w : ι → ℝ) (s : Finset ι) :
    Summable (fun p : ↥s → ℕ => ‖manyW w ⟨s,p⟩‖) ∧
    (∑' p, manyW w ⟨s,p⟩) = ∏ i∈s,(Real.exp (w i)-1) := by
  obtain ⟨hl,hg⟩ := pi_series (↥s) (fun i (n : ℕ) => w i.val^(n+1)/(n+1).factorial) (fun i => powers_norm _)
  rw [Finset.prod_subtype s (p:=(·∈s)) (fun _ => Iff.rfl)]
  refine ⟨hl,hg.trans (prod_congr rfl fun i _ => ?_)⟩
  exact (powers _).tsum_eq

lemma manyW_norm (w : ι → ℝ) (r : Reps ι) : ‖manyW w r‖ = manyW (fun i => ‖w i‖) r := by
  simp [manyW,Real.norm_eq_abs]

/-- Multiset-form exponential. No price threshold required for this
reordering. -/
theorem exponential (w : ι → ℝ) (h : Summable fun i => ‖w i‖) :
    Summable (fun r : Reps ι => ‖manyW w r‖) ∧
    Real.exp (∑' i,w i) = ∑' r : Reps ι, manyW w r := by
  let g (i : ι) := ‖w i‖
  have hf i : ‖g i‖ = g i := Real.norm_of_nonneg (norm_nonneg _)
  have hi i : 0 ≤ Real.exp (g i) - 1 := sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _))
  have he : Summable (fun r : Reps ι => ‖manyW w r‖) := by
    apply (summable_sigma_of_nonneg (f:=fun r : Reps ι => ‖manyW w r‖) (fun _ => norm_nonneg _)).mpr
    constructor
    · intro i; exact (fibre w i).1
    simp_rw [manyW_norm, fun i => (fibre (fun i => ‖w i‖) i).2]
    change Summable (fun s : Finset ι => ∏ i∈s,(Real.exp (g i)-1))
    apply summable_finsetProd_of_summable_nonneg hi
    exact (mayer_summable g (by simpa only [hf] using h)).of_norm
  refine ⟨he,?_⟩; rw [he.of_norm.tsum_sigma,(mayer w h).2]; apply tsum_congr; intro s; exact (fibre w s).2.symm
end YM.Push.LogIdentity
