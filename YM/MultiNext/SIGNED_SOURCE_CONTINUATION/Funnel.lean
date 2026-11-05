import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Aisles
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Tally

set_option warningAsError false

/-!
# Gathering source estimates (part one)
Pass sum tickets for countably many operands into the SAME history.
No mask upgrades across threshold borders!
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open Push.RelayDifference Multi
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Body
variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n} {A : Hol G}
variable {U : GridU n} {κ r : ℝ}

section Aggregate
variable {I V : Type*} {f : I → V → ℝ} {u : I→ℝ}



lemma sumcast (h : ∀ i,SumBudget (f i) (u i)) (hu : Summable u) :
    SumBudget (Function.uncurry f) (∑' i,u i) := by
  let v i := ∑' j, f i j
  have hs : Summable v := hu.of_nonneg_of_le (fun i => tsum_nonneg (h i).1) fun i => (h i).2.2
  have he : 0 ≤ Function.uncurry f := fun i => (h i.1).1 i.2
  have hp := (summable_prod_of_nonneg he).mpr ⟨fun i => (h i).2.1, hs⟩
  exact ⟨he,hp,hp.tsum_prod.trans_le (hs.tsum_le_tsum (fun i => (h i).2.2) hu)⟩
lemma sumcast_collect (h : SumBudget (Function.uncurry f) r) :
    SumBudget (fun j => ∑' i, f i j) r := by
  have hp i j : 0 ≤ f i j := h.1 (i,j)
  have hs := h.2.1
  exact ⟨fun j => tsum_nonneg (fun i => hp i j), hs.prod_symm.prod, hs.tsum_comm.trans_le (hs.tsum_prod.ge.trans h.2.2)⟩

lemma count_many {x : I → F.Coeff} (h : ∀ i,F.coeffSize (x i) ≤ u i) (he : SumBudget u r) :
    Summable (fun i => ‖x i‖) ∧ F.coeffSize (∑' i,x i) ≤ r := by
  have hs : Summable fun i => ‖x i‖ := he.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) fun i =>
    (norm_cost F _).trans (h i)
  have hp (j : F.Index) : Summable fun i => ‖x i j‖ := hs.of_nonneg_of_le (fun i => norm_nonneg _) fun i => norm_le_pi_norm _ j
  have hi : Summable (fun i => F.coeffSize (x i)) := he.2.1.of_nonneg_of_le (fun i => coeff_pos ..) h
  refine ⟨hs,?_⟩
  refine le_trans (b:=∑ j : F.Index, ∑' i, ‖x i j‖) (Finset.sum_le_sum (fun j _ =>
    (congr_arg (‖·‖) (tsum_apply hs.of_norm)).le.trans (norm_tsum_le_tsum_norm (hp j)))) ?_
  rw [← Summable.tsum_finsetSum (s:=Finset.univ (α:=F.Index)) (f:=fun j i => ‖x i j‖) (fun i _ => hp i)]
  exact (hi.tsum_le_tsum h he.2.1).trans he.2.2
end Aggregate

section
variable {I : Type*} [Countable I] (f : I × ℕ ↪ ℕ) (D : I → Body F n) (S : I → GridU n)

def rollup : Body F n := (∑' i, Body.coord (D i), hang f fun i => payload (D i.1) i.2,
    fun j x => ∑' i, flag (D i) j x)

section Admission
variable (hf : ∀ k : I × ℕ,U (f k)=S k.1 k.2)
include hf


-- Denominator κ must be shared across all operands
omit [Countable I] in
lemma Tally.rollup {c : I→ℝ} (T : ∀ i,Tally o R (S i) (D i) κ (c i)) (hk : 0 < κ) (H : SumBudget c r) :
    cap o R U (SignedSource.rollup f D) κ r := by
  let a i := (T i).energy; let b i := (T i).breath
  let t i j := (T i).stamp j
  have he i : 0≤ a i ∧ 0≤b i := ⟨(T i).e_nn,(T i).b_nn⟩
  have h₁ i : a i + b i ≤ c i := (T i).pay
  have ha : Summable a := H.2.1.of_nonneg_of_le (fun i => (he i).1) fun i => (le_add_of_nonneg_right (he _).2).trans (h₁ i)
  have hb : Summable b := H.2.1.of_nonneg_of_le (fun i => (he i).2) fun i => (le_add_of_nonneg_left (he _).1).trans (h₁ i)
  have hea := sumcast (f:=fun i j => R.p.mass (S i j) ((T i).seed j)) (fun i => (T i).energyPay) ha
  have heb := sumcast (f:=fun i j => R.p.mass (R.activities.forced j).support (t i j)) (fun i => (T i).breathPay)
    (hb.mul_left κ)
  have hnn i j : 0 ≤ t i j := ((T i).tag j).1
  have hs : Summable (uncurry t) := heb.2.1.of_nonneg_of_le (fun ⟨i,j⟩ => hnn i j)
    fun ⟨i,j⟩ => R.p.loMass _ _ (hnn i j)
  refine Tally.billed ⟨∑' i,a i,∑' i,b i,hang f fun q => (T q.1).seed q.2,fun j => ∑' i,t i j,
    tsum_nonneg (fun i => (he i).1),tsum_nonneg (fun i => (he i).2), ha.tsum_add hb |>.symm.trans_le (((ha.add hb).tsum_le_tsum
      h₁ H.2.1).trans H.2.2),hk,?_,?_,fun i => ?_,fun i => ⟨tsum_nonneg fun _ => hnn _ _,fun x => ?_⟩⟩
  · have hw := budget_of_hang f hea
    let g (q : I × ℕ) := (T q.1).seed q.2
    change SumBudget (fun i => R.p.mass (U i) (hang f g i)) _
    rw [show (fun i => R.p.mass (U i) (hang f g i)) = hang f (fun q => R.p.mass (S q.1 q.2) (g q)) by
      funext i; by_cases he:i∈Set.range f
      · obtain ⟨q,rfl⟩:=he; rw [hang_at,hang_at,hf]
      rw [hang_out f _ _ he,hang_out f _ _ he,BudgetPoint.mass,mul_zero]]
    exact hw
  · have he := sumcast_collect (f:=fun i j => R.p.mass (R.activities.forced j).support (t i j)) heb
    simpa only [BudgetPoint.mass,tsum_mul_left] using he
  · unfold SignedSource.rollup payload
    by_cases he : i∈Set.range f
    · obtain ⟨⟨j,k⟩,rfl⟩:=he
      change R.p.supBounds o (U (f _)) (hang f (fun j => payload (D j.1) j.2) (f _)) _
      rw [hang_at,hang_at,hf]; exact (T j).sexp k
    change R.p.supBounds o (U i) (hang f (fun j => payload (D j.1) j.2) i) _
    rw [hang_out _ _ _ he,hang_out _ _ _ he]; exact (Multi.null_path ..).2 _
  have he : ∀ j, ‖flag (D j) i x‖ ≤ t j i := fun j => ((T j).tag i).2 x
  have ht : Summable fun j => t j i := hs.prod_symm.prod_factor i
  have hv : Summable fun j => ‖flag (D j) i x‖ := ht.of_nonneg_of_le (fun _ => norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum he ht)
end Admission
end
end YM.MultiNext.SignedSource
