import YM.MultiNext.VACUUM_STABILITY.Component.FirstEst

set_option warningAsError false

/-!
# First exponential collection at all paid evaluations
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Component.Pasture
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V I : Type} {G : Gauge} {n : Side} {B : Brush V G n} (A : Pasture I B)

private lemma value_split (U K : Finset ℕ) (L : Support n) : valid (B:=B) L (Finset.disjSum U K) ↔
    B.compulsory L K ∧ BulkGas.admits (fun i => (B.u i).zone) (Finset.univ \ B.ban K) U := by
  unfold valid; rw [Finset.toRight_disjSum]
  constructor
  · rintro ⟨hf,h⟩
    constructor
    · exact ⟨fun i hi j hj hn => hf (show Sum.inr i∈(disjSum U K) by simp only [inr_mem_disjSum]; exact hi)
        (show Sum.inr j∈(disjSum U K) by simp only [inr_mem_disjSum]; exact hj) fun he => hn (Sum.inr.inj he), h⟩
    constructor
    · exact fun i hi j hj hn => hf (show Sum.inl i∈disjSum U K by simp only [inl_mem_disjSum]; exact hi)
        (show Sum.inl j∈disjSum U K by simp only [inl_mem_disjSum]; exact hj) fun he => hn (Sum.inl.inj he)
    intro i hi j hj; refine Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩; intro hk
    obtain ⟨k,hk,H⟩:=Finset.mem_biUnion.mp hk
    have hh : Disjoint ((B.u i).zone) (B.pack k).zone := hf (show Sum.inl i∈disjSum U K by simp [hi])
      (show Sum.inr k∈disjSum U K by simp [hk]) (by simp)
    exact Finset.disjoint_left.mp hh hj H
  rintro ⟨⟨hk,he⟩,hu,H⟩
  refine ⟨?_,he⟩
  have hv (i j) (hi : i∈U) (hj : j∈K) : Disjoint ((B.u i).zone) (B.pack j).zone := disjoint_left.mpr fun x hx hy =>
    (Finset.mem_sdiff.mp (H i hi hx)).2 (mem_biUnion.mpr ⟨j,hj,hy⟩)
  rintro (i|i) hi (j|j) hj hh
  · exact hu (Finset.inl_mem_disjSum.mp hi) (Finset.inl_mem_disjSum.mp hj) fun he => hh (he ▸ rfl)
  · exact hv _ _ (Finset.inl_mem_disjSum.mp hi) (Finset.inr_mem_disjSum.mp hj)
  · exact (hv _ _ (Finset.inl_mem_disjSum.mp hj) (Finset.inr_mem_disjSum.mp hi)).symm
  exact hk (Finset.inr_mem_disjSum.mp hi) (Finset.inr_mem_disjSum.mp hj) fun he => hh (he ▸ rfl)

variable [Fintype V] {P : BudgetPoint} {z : V→ℂ}

private lemma to_warm (U : Config G n) (s : Finset ℕ) : B.entry P z U s=
    ∑' b : Finset ℕ, plant B P U z (Finset.disjSum b s) := by
  have hf b := value_split (B:=B) b s (flags P.threshold U)
  unfold Brush.entry; rw [BulkGas.Z_eq]; split
  · rename_i he
    rw [← tsum_mul_left]; apply tsum_congr; intro b; unfold plant; split
    · rename_i hb
      rw [if_pos ((hf b).2 ⟨he,hb⟩),Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight,Finset.toLeft_disjSum,
        Finset.toRight_disjSum,mul_comm]; rfl
    rename_i hb; split; rename_i hh
    · exact False.elim (hb (((hf b).1 hh).2))
    rw [mul_zero]
  rename_i he; symm; refine (tsum_congr (g:=fun _ => 0) ?_).trans tsum_zero
  intro b; exact if_neg fun h => he (((hf b).1 h).1)

lemma counts_plants (U : Config G n) {c r κ} (h : PathBudget (B:=B) P z c r κ) (hr : 0 ≤ r) :
    Summable fun i => ‖plant B P U z i‖ := by
  obtain ⟨⟨f,hf,hF⟩,g,hg,hG⟩:=h
  have hc := Absolute.account (fun i => ⟨_,(B.u i).origin⟩) hF hr
  have hk := Absolute.account (fun i : ℕ => (B.pack i).property.1.mono (B.pack i).property.2) hG hr
  let k := consumes B P U z
  have hs : Summable fun i => ‖k i‖ := by
    have hu : Summable (Sum.elim f g) := Hearth.union_sum hc hk
    refine hu.of_nonneg_of_le (fun i => norm_nonneg _) ?_
    rintro (i|i)
    · exact (B.u i).rate_echo P z _ (hf _) U
    exact (hg i).2 _
  have ht := (summable_finsetProd_of_summable_norm hs).norm
  refine ht.of_nonneg_of_le (fun i => norm_nonneg _) ?_
  intro i; unfold plant; split; exact le_rfl; exact norm_zero.le.trans (norm_nonneg _)

lemma planted (U : Config G n) {κ c r : ℝ} (h : PathBudget (B:=B) P z c r κ) (hr : 0 ≤ r) :
    Summable (B.entry P z U) ∧ ∑' i, B.entry P z U i=∑' i,plant B P U z i := by
  let f := plant B P U z
  have he : Summable f := (counts_plants U h hr).of_norm
  let e := (Finset.sumEquiv.toEquiv : Finset Fruit ≃ (Finset ℕ) × (Finset ℕ)).trans (Equiv.prodComm _ _)
  have hx : Summable (f ∘ e.symm) := Equiv.summable_iff e.symm |>.mpr he
  have hv : B.entry P z U = fun i => ∑' j,(f ∘ e.symm) (i,j) := funext fun i => to_warm U i
  rw [hv]; refine ⟨hx.prod,?_⟩
  rw [←hx.tsum_prod]; exact e.symm.tsum_eq _

lemma arrives (U : Config G n) {κ c r} (h : PathBudget (B:=B) P z c r κ) (hr : 0≤r) :
    HasSum (A.view P U z) (∑' i,B.entry P z U i) := by
  rw [(planted U h hr).2]; refine (A.carries _ P U z id rfl).1 (show Summable _ from ?_).hasSum
  exact (counts_plants U h hr).of_norm
end YM.Multi.Vacuum.Component.Pasture
