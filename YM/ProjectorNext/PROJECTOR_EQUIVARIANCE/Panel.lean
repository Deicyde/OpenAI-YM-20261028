import YM.Next.FOUNDATIONS.SU2
import YM.Push.CUTOFF_PROJECTORS.Along

/-!
# Safe Coefficient ledger assembly

For the symmetry average. Regular supports can all differ. Forced names
on the *same* R, necessarily use those very names when combining (checking
absolute budgets before applying tsum exchange).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source Analysis MeasureTheory Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {R : Rep G n} {o : Site n} {H : Hol G}

/- finite stacks. `e` expects nonempty `ι`. -/
variable {ι : Type*} [Fintype ι] (e : ℕ ≃ (ι × ℕ))

def panel (Q : ι → Coefficient F n) : Coefficient F n :=
  ⟨∑ i, (Q i).x, fun i => (Q (e i).1).support (e i).2,
    fun i => (Q (e i).1).regular (e i).2, ∑ i, (Q i).forced⟩

lemma stackValue (Q : ι → Coefficient F n) (j) (U : Config G n) :
    (panel e Q).forced j U = ∑ i, (Q i).forced j U := by simp only [panel,Finset.sum_apply]

section Verify
variable {Q : ι → Coefficient F n}

lemma panel_format (h : ∀ i, (Q i).Format o H R) : (panel e Q).Format o H R := by
  constructor
  · exact fun i => (h _).smooth _
  · exact fun i => (h _).origin _
  · exact fun i => (h _).identity_null _
  · exact fun i => (h _).projects _
  · intro i U hv; rw [stackValue] at hv; contrapose! hv
    exact Finset.sum_eq_zero fun j _ => not_ne_iff.mp fun hr => hv ((h j).forcing _ U hr)
  · intro i hi; by_contra hv; apply hi
    funext U; rw [stackValue]; change _ = (0:ℂ); refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (Q j).forced i = 0 from not_ne_iff.mp fun hr => hv ((h j).carried i hr)]; rfl
  · intro i k U; rw [stackValue,stackValue]; exact Finset.sum_congr rfl fun j _ => (h j).invariant i k U
  · intro i U V hU hV
    rw [stackValue,stackValue]; exact Finset.sum_congr rfl fun j _ => (h j).supported i U V hU hV
  intro i
  rw [show (panel e Q).forced i = _ from funext (stackValue e Q i)]
  exact Finset.measurable_fun_sum _ fun j _ => (h j).borel i

lemma panel_cap {v : ℝ} (c : ι → ℝ) (h : ∀ i, (Q i).remBound o R v (c i)) :
    (panel e Q).remBound o R v (∑ i, c i) := by
  classical
  unfold Coefficient.remBound at h
  choose a b ha hb hl hv EA BA using h
  choose E hE hX using EA
  choose B hB hY using BA
  refine ⟨∑ i, a i,∑ i,b i,Finset.sum_nonneg (fun i _ => ha i),Finset.sum_nonneg (fun i _ => hb i),
    ?_,hv (e 0).1,⟨fun i => E (e i).1 (e i).2, ?_, fun i => hX _ _⟩,fun i => ∑ j,B j i, ?_,?_⟩
  · rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => hl i
  · let M (x : ι×ℕ) := R.p.mass ((Q x.1).support x.2) (E x.1 x.2)
    have hn (x) : 0 ≤ M x := (hE _).1 _
    have hm : Summable M := (summable_prod_of_nonneg hn).mpr ⟨fun i => (hE i).2.1,Summable.of_finite⟩
    change SumBudget (fun i => M (e i)) _
    refine ⟨fun i => hn _,e.summable_iff.mpr hm,?_⟩
    rw [e.tsum_eq,hm.tsum_prod,tsum_fintype]; exact Finset.sum_le_sum fun i _ => (hE _).2.2
  · let M (x : ι) (i : ℕ) := R.p.mass (R.activities.forced i).support (B x i)
    have he (i) : R.p.mass (R.activities.forced i).support (∑ j, B j i) = ∑ j,M j i :=
      Finset.mul_sum _ _ _
    simp_rw [he]
    have hh (i) (_ : i∈Finset.univ) : Summable (M i) := (hB i).2.1
    refine ⟨fun i => Finset.sum_nonneg fun j _ => (hB j).1 i, summable_sum hh,?_⟩
    rw [Summable.tsum_finsetSum hh,Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => (hB i).2.2
  intro i; refine ⟨Finset.sum_nonneg fun j _ => (hY j i).1,fun U => ?_⟩
  rw [stackValue]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => (hY j i).2 U)

lemma panel_density (S : SectionData F) (Q : ι → Coefficient F n) {σ C Λ δ w : ℝ} (hr : R.Lawful σ C Λ δ w)
    (h : ∀ i, ∃ v c, (Q i).remBound o R v c) (U : Config G n) :
    (panel e Q).density o S R U = ∑ i, (Q i).density o S R U := by
  classical
  choose v c hv using h
  let T := panel e Q
  have he : T.exponentialEntry o S R U = ∑ i, (Q i).exponentialEntry o S R U := by
    let p := S.footprint o
    let t := R.p.threshold
    let L : F.Coeff →ₗ[ℂ] ℂ := {
      toFun x := x 0 + masked R.p.threshold (S.footprint o) (S.places (F.scaled t⁻¹ (F.core x)) o) U
      map_add' x y := by
        by_cases hh : Healthy R.p.threshold (S.footprint o) U
        · simp only [map_add, masked_eq _ _ _ U hh, SectionData.places,S.eval_linear.map_add,Pi.add_apply]; abel
        simp only [masked_ne _ _ _ U hh,Pi.add_apply,add_zero]
      map_smul' a x := by
        by_cases hh : Healthy R.p.threshold (S.footprint o) U
        · simp only [map_smul, masked_eq _ _ _ U hh, SectionData.places,S.eval_linear.map_smul,Pi.smul_apply]; exact (smul_add _ _ _).symm
        simp only [masked_ne _ _ _ U hh,Pi.smul_apply,add_zero]; rfl }
    let M (x : ι × ℕ) := (Q x.1).maskedTerm R x.2 U
    change L T.x + (∑' i, M (e i)) = ∑ i, (L (Q i).x + ∑' j, M (i,j))
    have hm : Summable M := by
      refine Summable.of_norm ((summable_prod_of_nonneg (f:=fun x => ‖M x‖) (fun _ => norm_nonneg _)).mpr
        ⟨fun i => (Coefficient.regular_series (hv i)).absolute U,Summable.of_finite⟩)
    rw [show T.x = ∑ i, (Q i).x from rfl,map_sum,Finset.sum_add_distrib,
      e.tsum_eq, hm.tsum_prod,tsum_fintype]
  have hp : ∑' b, T.marked R b U = ∑ i, ∑' b, (Q i).marked R b U := by
    have ht i (_ : i∈Finset.univ) := (Coefficient.marked_series hr (hv i)).summable U
    rw [← Summable.tsum_finsetSum ht]; refine tsum_congr fun i => ?_
    by_cases hu : R.activities.admissible R.p U i
    · unfold Coefficient.marked
      simp_rw [if_pos hu,T,stackValue, Finset.sum_mul]; rw [Finset.sum_comm]
    simp [Coefficient.marked, hu]
  change T.density _ _ _ _ = _
  unfold Coefficient.density; rw [he,hp,Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
end Verify
end YM.ProjectorNext.Equivariance
