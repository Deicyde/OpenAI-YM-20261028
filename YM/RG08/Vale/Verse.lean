import YM.RG08.Vale.Tokens
/-!
# Support of test polynomials in the joint alphabet. ORDINARY address
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Exterior Function Filter Finset Matrix
open Scores Scores.Pages Stationary Analysis Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators
variable {n D k d j:ℕ}
-- Enumerate cost tests through k

def rangeT (k:ℕ) : Finset Cham := Finset.univ.biUnion fun i: Fin (k+1)=>Finset.univ.image (fun f:Fin i.val→Axis=>unitsT f)
lemma counted (p: Cham): p∈rangeT k ↔ cashT p≤k := by
  constructor
  · intro h; obtain ⟨i,-,h⟩:= Finset.mem_biUnion.mp h; obtain ⟨w,-,rfl⟩:= Finset.mem_image.mp h
    rw [cash_units]; omega
  intro h
  exact Finset.mem_biUnion.mpr ⟨⟨cashT p,by omega⟩,mem_univ _,mem_image.mpr ⟨needleT p,mem_univ _,needy p⟩⟩

def PaperT (D k:ℕ) : Submodule ℝ (Exam D) := Submodule.span ℝ (coinsT D '' (rangeT k))
lemma PaperT_beck (p:Cham)(h:cashT p≤k) : coinsT D p ∈ PaperT D k := Submodule.subset_span ⟨p,(counted _).mpr h,rfl⟩
lemma paper_mono (h:k≤j): PaperT D k≤ PaperT D j := Submodule.span_mono (Set.image_mono fun p hp=> (counted p).2 (((counted p).1 hp).trans h))
private lemma emerging {n:ℕ}(q:Fin n→Axis)(x:E4): (∏ i,x (q i)) = ∏ i, x i ^ (unitsT q i) := by
  induction n with
  | zero=> simp [unitsT]
  | succ k ih => rw [← Fin.cons_self_tail q, Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,units_cons,Pi.add_apply,pow_add,prod_mul_distrib]
                 rw [ih]; simp [oneAxis,Pi.single_apply,ite_apply,mul_comm]
lemma tensorT (T: Tensor.T E4 ℝ k) : mental D k T∈PaperT D k := by
  let m (q:Fin k→Axis) := T (basis ∘ q)*(∏ i:Axis, (((unitsT q i).factorial:ℕ):ℝ))
  let c q := coinsT D (unitsT (k:=k) q)
  have hz : mental D k T = ∑ q,m q • c q := by
    apply Subtype.ext; ext x
    change T (fun _=> x) = _; rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]
    conv_lhs => rw [← show (∑ i:Axis, x i • basis i)=x from by ext i; simp]
    rw [T.map_sum (fun _ (i:Axis)=> x i • basis i)]
    refine sum_congr rfl fun i _=> ?_
    rw [T.map_smul_univ (fun a=> x (i a)) _]; unfold m
    change (∏ a, x (i a))* _= _* beck (unitsT i) _
    unfold beck; rw [prod_div_distrib,emerging]; field_simp; unfold Function.comp; ring
  rw [hz]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (PaperT_beck _ (cash_units (k:=k) i|>.le))

-- roll of a homogeneous page (using d reserved)
open Planned.PrimaryIntegral295 Place
lemma page_poly (q:Cham): beck q ∈ Place.exactDegree ℝ (cashT q) := by
  refine exact_of_smooth ((beck_cont q).contDiffAt.of_le le_top) fun x t=>?_
  simp only [beck, PiLp.smul_apply, smul_eq_mul, mul_pow, mul_div_assoc, prod_mul_distrib, prod_pow_eq_pow_sum,cashT]
lemma passT {p:Exam D} (h:p.val∈ rangeLt ℝ (k+1)): p ∈ PaperT D k := by
  obtain ⟨v,hv,he⟩:= range_decompose h
  choose M hm H using fun i=> pure_sym (hv i)
  rw [show p=∑ i:Fin (k+1),mental D i.val (M i) from Subtype.ext (by rw [he,AddSubmonoidClass.coe_finsetSum]; exact Finset.sum_congr rfl fun i _=> H i)]
  exact Submodule.sum_mem _ fun i _=> paper_mono (by omega : i.val≤k) (tensorT _)
end YM.RG08.Vale
