import YM.Next.MULTISOURCE.Imprint

/-! Afield budgets suffice. Unselected all p, actual rooted budget on all copies. -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Writers
open RG Wilson Lattice Marker Function Finset Pack Overlay Mix
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {n : Side} {G : Gauge}
variable {P : Rep G n} {o : V → Site n} {D : Hot R → Pulse G n} {k : Hot R → ℝ} {κ w : ℝ}
variable (Y : Writers P κ D o k)

omit [Fintype V] in
private lemma ranked_budget {X : Type*} (g : X→ℝ) (T : X→R.Mode) (b : Bool) (u : V)
    (h : SumBudget (fun i => if u ∈ (T i).val then g i else 0) 1) :
    SumBudget (fun i => if ranked (T i)=b ∧ u∈ (T i).val then g i else 0) 1 := by
  refine permit_le h le_rfl fun i => ?_
  split_ifs with he h' h'; exacts [⟨by simpa [h'] using h.1 i, le_rfl⟩,
    False.elim (h' he.2), ⟨le_rfl,by simpa [h'] using h.1 i⟩,⟨le_rfl,le_rfl⟩]

omit [Fintype V] in
lemma crown_budget (A : Afield P.p κ o D k w) (hw : 0 < w) (u : V) :
    SumBudget (fun i => if u∈ (Y.toBands.rays i).val then Y.receipt.crown (fun _ => w) 0 i else 0) 1 := by
  let f (i : ℕ) := if u ∈ (Y.toBands.rays i).val then Y.receipt.crown (fun _ => w) 0 i else 0
  let g (x : Hot R × ℕ) := f (Y.code x)
  have ht x i : g (x,i) = if x ∈ rootAt R u then
      3 * w^x.sites.card * (burn P.p 0 (Y.soil x i)* Y.fee x i) else 0 := by
    simp [g,f,Stubs.crown,toBands,receipt,loaf,Poly.toll,burn,Hot.sites]
    split <;> ring
  have hf (x : Hot R) : SumBudget (fun i => g (x,i)) (if u∈x.sites then 3*current w k x else 0) := by
    by_cases h : u∈x.sites
    · simp_rw [ht,if_pos h,if_pos (mem_rootAt.mpr h)]
      rw [current,← mul_assoc]; exact permit_mul (Y.finiteCost x) (by positivity)
    simp only [ht,mem_rootAt, h,↓reduceIte]; simp [SumBudget]
  have hS := (summable_prod_of_nonneg (show 0 ≤ g from fun ⟨x,i⟩ => (hf x).1 i)).mpr
    ⟨fun i => (hf i).2.1,(hasSum_fintype _).summable⟩
  refine ⟨fun j => ?_, Y.code.summable_iff.mp hS,?_⟩
  · obtain ⟨⟨x,i⟩,rfl⟩ := Y.code.surjective j
    exact (hf x).1 i
  change ∑' i, f i ≤ _
  rw [← Y.code.tsum_eq f, hS.tsum_prod, tsum_fintype]
  refine (sum_le_sum fun i _ => (hf i).2.2).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  change 3 * (∑ i∈rootAt R u,current w k i) ≤ _
  linarith [A.paid u]

omit [Fintype V] in
lemma cord_budget (A : Afield P.p κ o D k w) (hw : 0 < w) (hc : κ ≤ 1) (u : V) :
    SumBudget (fun j : ℕ × ℕ => if u∈ (Y.toBands.marks j.1 j.2).val then
      Y.receipt.cord (fun _ => w) 0 j else 0) 1 := by
  let f (j : ℕ × ℕ) := if u∈ (Y.toBands.marks j.1 j.2).val then
      Y.receipt.cord (fun _ => w) 0 j else 0
  let T (z : Hot R × Pack n) : ℕ × ℕ := (Y.slot z.2,Y.code (z.1,0))
  let X := ((rootAt R u) ×ˢ Finset.univ).image T
  have H (x : ℕ × ℕ) (h : x∉X) : f x=0 := by
    unfold f; split_ifs with hi
    · have he : Y.toBands.entries x.1 x.2=0 := by
        unfold toBands; dsimp only
        split <;> rename_i hu
        · apply False.elim; apply h
          let v := Y.code.symm x.2
          have hx : v.2=0 := hu.2
          refine mem_image.mpr ⟨(v.1,ofAddress P.activities x.1), mem_product.mpr
            ⟨mem_rootAt.mpr hi,mem_univ _⟩, Prod.ext hu.1 ?_⟩
          change Y.code (v.1,0)=_
          rw [← hx]; exact Y.code.apply_symm_apply _
        rfl
      simp [Stubs.cord, receipt,he,loaf]
    rfl
  have hn {i j} (he : Y.slot i=Y.slot j) : i=j := (Y.valid _).symm.trans
    ((congrArg (ofAddress P.activities) he).trans (Y.valid j))
  have hi : Injective T := fun i j h => Prod.ext (congrArg (fun x : Hot R × ℕ => x.1) (Y.code.injective (congrArg Prod.snd h)))
    (hn (congrArg Prod.fst h))
  have hv (i) (hi : i∈rootAt R u) (x) : f (T (i,x)) ≤ w^i.sites.card * (burn P.p 0 x.zone * Y.ticket i x) := by
    have hj : u∈ (Y.toBands.marks (Y.slot x) (Y.code (i,0))).val := by
      simp only [toBands,Equiv.symm_apply_apply]; exact mem_rootAt.mp hi
    unfold f T
    rw [if_pos hj]
    unfold Stubs.cord
    simp only [receipt, toBands, Equiv.symm_apply_apply,Y.valid,eq_self, true_and,↓reduceIte]
    rw [show (P.activities.forced (Y.slot x)).support=x.zone from congrArg Pack.zone (Y.valid x)]
    split
    · simp only [Poly.toll,prod_const]; exact le_of_eq rfl
    simp only [loaf, mul_zero]; exact mul_nonneg (by positivity) (mul_nonneg (burn_pos ..).le
      (Y.quantity ..).2.2.1)
  refine ⟨fun i => ?_,summable_of_ne_finset_zero H,?_⟩
  · dsimp only
    split
    · exact mul_nonneg (Poly.worth (fun _ => hw) _).le (mul_nonneg (Real.exp_pos _).le (Y.receipt.usable i))
    exact le_rfl
  change ∑' i, f i ≤ 1
  rw [tsum_eq_sum H,sum_image hi.injOn,sum_product]
  refine (le_trans (b:=∑ i∈rootAt R u,current w k i) (sum_le_sum fun i hi => ?_) (le_trans (A.paid u) (by norm_num)))
  apply le_trans (sum_le_sum fun x _ => hv i hi x)
  rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((Y.total i).trans (by
    have hk : 0 ≤ k i := (A.present i).2.2.2.1
    exact mul_le_of_le_one_left hk hc)) (by positivity)

omit [Fintype V] in
lemma honors (A : Afield P.p κ o D k w) (hw : 0 < w) (hc : κ ≤ 1) (hs : Spaced o P.p.B)
    (hB : 8 ≤ P.p.B) : Stubs.Holds Y.toBands w := by
  have hh (b : Bool) : Y.receipt.funded (fun _ => w) 0 b 1 :=
    ⟨fun i => ranked_budget _ _ b i (Y.crown_budget A hw i),fun i => ranked_budget _ _ b i (Y.cord_budget A hw hc i)⟩
  refine ⟨fun i => ?_,Y.active,fun i j he => ⟨hB,(by have hv := hs i j he; rwa [sq] at hv)⟩,
    Y.receipt,hh false, Or.inl (hh true)⟩
  calc
    _ ≤ w * k (Hot.one R i) := mul_le_mul_of_nonneg_left (Y.valued _) hw.le
    _ = current w k (Hot.one R i) := by simp [current]
    _ ≤ ∑ i∈rootAt R i,current w k i := single_le_sum (f:=current w k) (fun v _ => mul_nonneg (by positivity : 0 ≤ w^v.sites.card) (A.present v).2.2.2.1)
      (show Hot.one R i ∈ rootAt R i by simp)
    _ ≤ _ := (A.paid i).trans (by norm_num)
end YM.Multi.Writers
