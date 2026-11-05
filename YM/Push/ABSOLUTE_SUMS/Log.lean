import Mathlib.Analysis.Normed.Group.Tannery
import YM.Push.ABSOLUTE_SUMS.FiniteLog


/-!
# Exact real log identity under the absolute bounds

Downstream application of the combinatorial package. For a hard-core
gas inc. repeated-index incompatibility, FULL real amplitudes and
complete addresses. Can restrict to labels compatible with a given
forced list for applying this. All coefficient sums over occurrences,
absolutely convergent at this volume with uniform per-root control as
above. Shows exactly the identity discussed at  for unmarked
real weights with the appropriate prices; does not construct the
weights or assume applicability of these prices to any actual proposal
for the RG step. No claim here about complex/analytic branches (bounds
can be used separately).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Gas
open Function Filter Graph Ursell Coef Trees RG Finset Lattice
open scoped BigOperators Classical Topology
variable {ι : Type*} (R : ι → ι → Prop) (w : ι → ℝ)

lemma logRow_open [Fintype ι] (n : ℕ) : logRow R w n = ∑ z : Tuple ι n, term R w ⟨n,z⟩ := by
  unfold logRow Coef.linked term; rw [sum_div]

lemma finite_log [Fintype ι] (hr : Hard R) {n : Side} (X : ι → Support n) (B : ℕ)
    (ht : Tests R X) (hX : ∀ i,(X i).Nonempty) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) : Real.exp (logSum R w) = total R w := by
  have he : Summable (term R w) := (absolute R w X B ht hX ha h).2.1.of_norm
  have hz : logSum R w= ∑' i, logRow R w i := by
    unfold logSum; rw [he.tsum_sigma]; apply tsum_congr; intro i
    rw [logRow_open, tsum_fintype]
  rw [hz,total,tsum_fintype (value R w)]
  let C : ℝ := (n.val^4:ℕ)*γ
  have hh := h.1
  refine exact_polynomial R w hr (show 0≤C by unfold C; positivity) (ready_pos X B h) h.2.2.2.1 ?_
  intro i; rw [logRow_open]
  exact (norm_sum_le ..).trans (budget_sum (absolute_at R w X B ht hX ha h i) univ)

-- restricting labels
abbrev chosenRel (D : Finset ι) := fun i j : ↥D => R i.val j.val
abbrev chosenW (D : Finset ι) := fun i : ↥D => w i.val

private def liftIndex (D : Finset ι) (i : Clusters ↥D) : Clusters ι := ⟨i.1,fun j => (i.2 j).val⟩
private def boundTo (D : Finset ι) (i : Clusters ι) : ℝ := if ∀ j, i.2 j∈D then term R w i else 0

private lemma actual (D : Finset ι) : ∑' i, boundTo R w D i = logSum (chosenRel R D) (chosenW w D) := by
  unfold logSum
  have he : Injective (liftIndex D) := by
    rintro ⟨s,p⟩ ⟨t,q⟩ h
    have hs : s=t := congr_arg Sigma.fst h; subst t
    have hi : (fun i => (p i).val) = (fun i => (q i).val) := (Sigma.mk.inj h).2 |> eq_of_heq
    have hp : p=q := funext fun i => Subtype.ext (congr_fun hi i)
    subst q; rfl
  have hr : Function.support (boundTo R w D) ⊆ Set.range (liftIndex D) := by
    rintro ⟨s,p⟩ hi
    have hi : ∀ j, p j∈D := by
      by_contra hn
      exact hi (if_neg hn)
    exact ⟨⟨s,fun i => ⟨p i,hi i⟩⟩,rfl⟩
  rw [← he.tsum_eq hr]; apply tsum_congr; rintro ⟨s,p⟩
  unfold boundTo liftIndex; dsimp only; rw [if_pos (fun j => (p j).property)]; unfold term coefficient; rfl

private def pickedFrom (D : Finset ι) (s : Finset ι) : ℝ := if s ⊆ D then value R w s else 0

private lemma literal (D : Finset ι) : ∑' i, pickedFrom R w D i = total (chosenRel R D) (chosenW w D) := by
  let f (i : Finset ↥D) : Finset ι := i.image (fun j => j.val)
  have hf : Injective f := Finset.image_injective Subtype.val_injective
  have hg : Function.support (pickedFrom R w D) ⊆ Set.range f := by
    intro i hi
    have he : i ⊆ D := by by_contra hh; exact hi (if_neg hh)
    let s : Finset ↥D := univ.filter (fun j => j.val∈i)
    refine ⟨s,?_⟩; ext j; rw [show f s=_ from rfl,mem_image]; constructor
    · rintro ⟨a,ha,rfl⟩; exact (mem_filter.mp ha).2
    intro h; exact ⟨⟨j,he h⟩, mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have he (s : Finset ↥D) : pickedFrom R w D (f s) = value (chosenRel R D) (chosenW w D) s := by
    have hs : f s⊆ D := fun i hi => by obtain ⟨j,hj,rfl⟩ := mem_image.mp hi; exact j.property
    have he : separated (chosenRel R D) s ↔ separated R (f s) := by
      constructor
      · intro h i hi j hj hk
        obtain ⟨i,hi',rfl⟩ := mem_image.mp hi
        obtain ⟨j,hj',rfl⟩ := mem_image.mp hj
        exact h _ hi' _ hj' (fun hz => hk (congr_arg Subtype.val hz))
      intro h i hi j hj hk
      exact h _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj) (fun h => hk (Subtype.ext h))
    unfold pickedFrom value; rw [if_pos hs]
    by_cases hh : separated (chosenRel R D) s
    · rw [if_pos hh,if_pos (he.mp hh)]
      exact Finset.prod_image Subtype.val_injective.injOn
    rw [if_neg hh,if_neg fun h => hh (he.mpr h)]
  unfold total; rw [← hf.tsum_eq hg]; exact tsum_congr he

lemma actual_values {n : Side} (X : ι → Support n) (B : ℕ) (hX : ∀ i,(X i).Nonempty)
    {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    SumBudget (fun s => ‖value R w s‖) (Real.exp ((n.val^4:ℕ)*γ)) := by
  let f (i : ι) := ‖w i‖
  have he := Product.everyone_ne X B (show ∀ i,0 ≤ f i from fun _ => norm_nonneg _)
    (fun i _ => hX i) h.2.2.2.2.2
  have hb : SumBudget f ((n.val^4:ℕ)*γ) := budget_mono he (fun _ => norm_nonneg _) (fun i =>
    le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg (add_nonneg ha h.2.1.le) (by positivity))))
  apply budget_mono (Product.set_products hb) (fun _ => norm_nonneg _)
  intro i; unfold value; split
  next hi => rw [norm_prod]
  next hi => rw [norm_zero]; exact prod_nonneg fun i _ => norm_nonneg _

/-- Calculation of the *actual* series and sign on hard overlap graphs.
A sufficient hit threshold; no convergence assumption on either series.
R can also encode a previous tested stencil (so long as edges are still
payable by overlaps). Hard includes incompatibility of an address with
itself. -/
theorem price_log (hr : Hard R) {n : Side} (X : ι → Support n) (B : ℕ)
    (ht : Tests R X) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    SumBudget (fun s => ‖value R w s‖) (Real.exp ((n.val^4:ℕ)*γ)) ∧
    SumBudget (fun i => ‖term R w i‖) (((n.val^4:ℕ)*γ)*(1-q)⁻¹) ∧
    Real.exp (logSum R w) = total R w ∧ 0 < total R w ∧ Real.log (total R w) = logSum R w := by
  have hX i : (X i).Nonempty := by obtain ⟨x,hx,-⟩ := ht i i (hr.diag i); exact ⟨x,hx⟩
  have hb := actual_values R w X B hX ha h
  have hB := absolute R w X B ht hX ha h
  suffices he : Real.exp (logSum R w) = total R w from
    ⟨hb,hB,he,he ▸ Real.exp_pos _,by rw [← he,Real.log_exp]⟩
  have he (D : Finset ι) : Real.exp (∑' i,boundTo R w D i)=∑' i,pickedFrom R w D i := by
    let x i := X (i:↥D).val
    rw [actual,literal]; refine finite_log (γ:=γ) (δ:=δ) (q:=q) (chosenRel R D) _ ⟨fun i => hr.diag _,fun i j => hr.symm _ _⟩
      x B (fun i j => ht _ _) (fun i => hX _) ha ?_
    obtain ⟨hg,hd,hq,hn,hw,hh⟩ := h
    refine ⟨hg,hd,hq,hn,fun _ => norm_nonneg _,fun y => ?_⟩
    have hv := budget_pull (fun j : ↥D => j.val) Subtype.val_injective (hh y)
    exact hv
  have hf : Tendsto (fun D => ∑' i,boundTo R w D i) atTop (𝓝 (logSum R w)) := by
    apply tendsto_tsum_of_dominated_convergence hB.2.1
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (univ.image i.2)] with D hD
      exact (show boundTo R w D i = _ from if_pos (fun j => hD (mem_image_of_mem _ (mem_univ j)))).symm
    refine Eventually.of_forall fun D i => ?_
    unfold boundTo; split <;> first | exact le_rfl | exact norm_zero.trans_le (norm_nonneg _)
  have hg : Tendsto (fun D => ∑' i,pickedFrom R w D i) atTop (𝓝 (total R w)) := by
    apply tendsto_tsum_of_dominated_convergence hb.2.1
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with D hD
      exact (show pickedFrom R w D i = _ from if_pos hD).symm
    refine Eventually.of_forall fun D i => ?_
    unfold pickedFrom; split <;> first | exact le_rfl | exact norm_zero.trans_le (norm_nonneg _)
  exact tendsto_nhds_unique ((Real.continuous_exp.continuousAt.tendsto.comp hf).congr he) hg
end YM.Push.AbsoluteSums.Gas
