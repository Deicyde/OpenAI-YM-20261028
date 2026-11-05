import YM.Extra.SOURCE_HISTORIES.Dressing

/-!
# Countable labeled superposition

To integrate a history one needs to sum actual paid coefficient families with
the same vacuum. Give genuinely countable operations: keep separate copies of
*regular* atoms, even zero ones; but when two *forced* operations pay the
same address (which may also be used by the vacuum!), add their coefficients,
keeping that address, hence its SAME exclusions/support/inventory. All
equalities are pointwise, including at the indicators. Absolute budget proven,
not `tsum` conditional rearrangement.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {d : ℕ} {ι : Type*} {G : Gauge} {F : Labels.Frame G d}
variable {o : Site n} {R : Rep G n} {σ C Λ δ w : ℝ}

variable (e : ℕ ≃ ι × ℕ) (P : ι → Coefficient F n)

def merge : Coefficient F n where
  x := ∑' i, (P i).x
  regular k := (P (e k).1).regular (e k).2
  support k := (P (e k).1).support (e k).2
  forced k U := ∑' i, (P i).forced k U

/-- Format proof, incl predicate reads under *fixed* vacuum. Algebraic;
also need price proof to ensure the tsum actually converges. -/
theorem merge_format [Countable ι] {H : Hol G} (h : ∀ i, (P i).Format o H R) :
    (merge e P).Format o H R where
  origin k := (h _).origin (e k).2
  identity_null k := (h _).identity_null (e k).2
  projects k := (h _).projects (e k).2
  smooth k := (h _).smooth (e k).2
  forcing k U hU := by
    contrapose! hU
    have he (i) : (P i).forced k U = 0 := not_not.mp (fun w => hU ((h i).forcing k U w))
    simp [merge, he]
  carried k hk := by
    contrapose! hk
    have he (i) : (P i).forced k = 0 := not_not.mp fun w => hk ((h i).carried k w)
    funext U
    simp [merge, he]
  borel k := Measurable.tsum fun i => (h i).borel k
  supported k U V hA hF := tsum_congr fun i => (h i).supported k U V hA hF
  invariant k u U := tsum_congr fun i => (h i).invariant k u U

/-- Charge exactly even when some labels wrap (or have zero coefficients),
in the actual grown `mass` (including its positive exponent and cover size).
No sharing of λ-orders implicit. -/
theorem merge_budget {t : ι → ℝ} {v : ℝ} (hp : 0 < v) (h : ∀ i, (P i).remBound o R v (t i)) (ht : Summable t) :
    (merge e P).remBound o R v (∑' i, t i) ∧
      Dominated (fun x : ι×ℕ => (P x.1).maskedTerm R x.2) ∧ Dominated (fun x : ι×ℕ => (P x.1).forced x.2) := by
  classical
  unfold Coefficient.remBound at h
  choose a b ha hb hw hv hR' hK' using h
  choose E hE hR using hR'
  choose D hD hK using hK' 
  have h₁ : Summable a := .of_nonneg_of_le ha (fun i => le_trans (le_add_of_nonneg_right (hb i)) (hw i)) ht
  have h₂ : Summable b := .of_nonneg_of_le hb (fun i => le_trans (le_add_of_nonneg_left (ha i)) (hw i)) ht
  let xmass (x : ι × ℕ) := R.p.mass ((P x.1).support x.2) (E x.1 x.2)
  let fmass (x : ι × ℕ) := R.p.mass (R.activities.forced x.2).support (D x.1 x.2)
  have hx := budget_prod (f:=xmass) hE h₁
  have hf := budget_prod (f:=fmass) hD (h₂.mul_left v)
  have hu (x : ι×ℕ) (U) : ‖(P x.1).forced x.2 U‖ ≤ D x.1 x.2 := (hK x.1 x.2).2 U
  have hh (x : ι×ℕ) : D x.1 x.2 ≤ fmass x := R.p.loMass _ _ (hK x.1 x.2).1
  have hj (j : ℕ) : Summable fun i => D i j := .of_nonneg_of_le (fun i => (hK i j).1)
    (fun i => hh (i,j)) (hf.2.1.prod_symm.prod_factor j)
  refine ⟨?_,⟨xmass,hx.2.1,?_⟩,fmass,hf.2.1,fun i U => (hu i U).trans (hh _)⟩
  · refine ⟨∑' i, a i,∑' i, b i,tsum_nonneg ha,tsum_nonneg hb, ?_, hp,⟨fun k => E (e k).1 (e k).2, ?_,
      fun k => hR (e k).1 (e k).2⟩, fun k => ∑' i, D i k, ?_, fun j => ⟨tsum_nonneg (fun i => (hK i j).1),?_⟩⟩
    · rw [← h₁.tsum_add h₂]; exact (h₁.add h₂).tsum_le_tsum hw ht
    · change SumBudget (fun k => xmass (e k)) _
      exact ⟨fun k => hx.1 _, hx.2.1.comp_injective e.injective,(e.tsum_eq xmass).trans_le hx.2.2⟩
    · have hy (j : ℕ) : R.p.mass (R.activities.forced j).support (∑' i, D i j) = ∑' i, fmass (i,j) := by
        unfold fmass BudgetPoint.mass; rw [← tsum_mul_left]
      simp_rw [hy]
      refine ⟨fun j => tsum_nonneg (fun i => hf.1 _), hf.2.1.prod_symm.prod,?_⟩
      calc
        _ = ∑' i, ∑' j, fmass (i,j) := Summable.tsum_comm hf.2.1
        _ = ∑' x, fmass x := hf.2.1.tsum_prod.symm
        _ ≤ _ := hf.2.2.trans_eq tsum_mul_left
    intro U
    have hs : Summable fun i => ‖(P i).forced j U‖ := .of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun i => hu (i,j) U) (hj j)
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i => hu (i,j) U) (hj j))
  intro i U
  refine le_trans (b:=E i.1 i.2) ?_ (R.p.loMass _ _ (hR i.1 i.2).1)
  dsimp only [Coefficient.maskedTerm]
  by_cases hu : Healthy R.p.threshold ((P i.1).support i.2) U
  · rw [masked_eq _ _ _ _ hu]; exact (hR ..).2 U hu [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hu,norm_zero]; exact (hR i.1 i.2).1

/-- The linear primary *piece*, incl unit as a global coefficient. -/
def part (S : SectionData F) (o : Site n) (R : Rep G n) (U : Config G n) : F.Coeff →ₗ[ℂ] ℂ where
  toFun x := x 0 + masked R.p.threshold (S.footprint o)
    (S.places (F.scaled R.p.threshold⁻¹ (F.core x)) o) U
  map_add' x y := by
    by_cases he : Healthy R.p.threshold (S.footprint o) U
    · simp only [Pi.add_apply,masked_eq _ _ _ _ he, map_add, SectionData.places, S.eval_linear.map_add]; abel
    simp [he]
  map_smul' x y := by
    by_cases he : Healthy R.p.threshold (S.footprint o) U
    · simp only [Pi.smul_apply,masked_eq _ _ _ _ he,map_smul,SectionData.places,S.eval_linear.map_smul,smul_add,RingHom.id_apply]
    simp [he]

/-- Merge is pointwise linear at density level. Finite or countable.
Note needs REAL activities lawful with summability even to conclude here. -/
theorem merge_density {t : ι → ℝ} {v : ℝ} (hp : 0 < v) (hr : R.Lawful σ C Λ δ w)
    (h : ∀ i, (P i).remBound o R v (t i)) (ht : Summable t) (hx : Summable fun i => F.coeffSize (P i).x)
    (B : SectionData F) (U) :
    HasSum (fun i => (P i).density o B R U) ((merge e P).density o B R U) := by
  obtain ⟨hh,hA,hK⟩ := merge_budget e P hp h ht
  have he (i : Coefficient F n) : i.exponentialEntry o B R U = part B o R U i.x + ∑' j, i.maskedTerm R j U := rfl
  have hs : HasSum (fun i => (P i).exponentialEntry o B R U) ((merge e P).exponentialEntry o B R U) := by
    let f (x : ι × ℕ) := (P x.1).maskedTerm R x.2 U
    have hj : Summable f := hA.summable U
    simp_rw [he]
    have hu : ∑' j, (merge e P).maskedTerm R j U = ∑' x, f x := e.tsum_eq f
    rw [hu, hj.tsum_prod]
    exact ((part B o R U).toContinuousLinearMap.hasSum (Size.series F hx).of_norm.hasSum).add hj.prod.hasSum
  have hq : HasSum (fun i => ∑' j, (P i).marked R j U) (∑' j, (merge e P).marked R j U) := by
    let f := fun x : ι×ℕ => (P x.1).forced x.2 U * dressed R x.2 U
    have hl : Summable f := by
      obtain ⟨c,-,-,hc⟩ := dressed_budget hr
      obtain ⟨a,ha,hk⟩ := hK
      apply Summable.of_norm_bounded (ha.mul_right c)
      intro i; unfold f
      rw [norm_mul]; exact mul_le_mul (hk i U) (hc ..) (norm_nonneg _) ((norm_nonneg _).trans (hk i U))
    have hj (i : ι) := dress_eq hr (rem_dominated (h i)) U
    simp_rw [hj, dress_eq hr (rem_dominated hh) U]
    change HasSum (fun i => ∑' j, f (i,j)) (∑' j, (∑' i,(P i).forced j U)*dressed R j U)
    simp_rw [← tsum_mul_right]
    rw [show ∑' j : ℕ, ∑' i, (P i).forced j U * dressed R j U = ∑' i, ∑' j : ℕ, f (i,j) from
      Summable.tsum_comm hl]
    exact hl.prod.hasSum
  exact (hs.mul_left (R.eval U : ℂ)).add (hq.mul_left (Real.exp (R.exponent U) : ℂ))

/-- Regular address constructor for merges, independent of the coefficients. -/
def code (ι : Type*) [Nonempty ι] [Countable ι] : ℕ ≃ ι × ℕ := by
  letI : Encodable (ι × ℕ) := Encodable.ofCountable _
  letI : Denumerable (ι × ℕ) := Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv (ι × ℕ)).symm

end YM.Extra.Histories
