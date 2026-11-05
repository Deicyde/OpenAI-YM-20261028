import YM.OPE.Trees.Height
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-!
# Ancestral telescoping/accounts
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Finset Filter
open scoped Classical Topology BigOperators
variable {I:Type}{s:Arboreal I}{a:Finset I}{i j k:I}

variable (s a)
def leg (i:I):= (s.middle a).filter (fun j=> s.Anc j i)
lemma leg_in (i j): j∈ s.leg a i↔ j∈ s.middle a ∧ s.Anc j i:= mem_filter
-- for s_i relative to parent spacing

def stepAt (t:I→ℝ)(i:I):= t i-t (s.parent i)
def ratioAt (r:I→ℝ)(i:I):= r i/r (s.parent i)
variable {s a}
lemma step_mem (hv:i≠s.root)(he:i∈a): s.leg a i= insert i (s.leg a (s.parent i)):=by
    ext k; rw [s.leg_in, mem_insert, s.leg_in]; constructor
    · rintro ⟨hz,hk⟩; by_cases hx:k=i; · exact Or.inl hx
      exact Or.inr ⟨hz,hk.back (Ne.symm hx)⟩
    rintro (rfl|⟨hk,hk'⟩); exacts [⟨mem_erase.mpr ⟨hv,he⟩,Anc.same ..⟩,⟨hk,hk'.joins (Anc.step ..)⟩]
lemma leg_not (hv:i≠s.root) : i∉ s.leg a (s.parent i):=fun h=> not_lt_of_ge (s.leg_in ..|>.1 h).2.depth (s.step i hv)
lemma beginLeg (s:Arboreal I)(a):s.leg a s.root=∅:=eq_empty_of_forall_notMem (fun _ h=> (mem_erase.mp (s.leg_in ..|>.mp h).1).1 (s.leg_in ..|>.mp h).2.excess)
lemma level_sum (t:I→ℝ)(he:s.Active a)(hi:i∈a) : (∑ k∈ s.leg a i,s.stepAt t k)+t s.root = t i:=by
    induction i using s.hill with
    | h=>rw [beginLeg,sum_empty,zero_add]
    | hp i h ih=> rw [step_mem h hi,sum_insert (leg_not h),add_assoc, ih (he.parent hi)]; unfold stepAt; ring

lemma leg_mono {r:I→ℝ} (hs:∀ i∈ s.middle a, 0 ≤ s.stepAt r i) (h : s.Active a)(hi:i∈a): r i ≤ (∑ k∈ s.middle a, s.stepAt r k)+r s.root:=by -- r variable
    rw [← level_sum r h hi]; exact add_le_add_left (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i hi _=> hs i hi)) _ -- right?
end YM.OPE.Arboreal
