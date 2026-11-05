import YM.RG08.Wax.Exponential
import YM.RG08.Bands.Vernal
/-! # Graded Poll formula, factorial free due to square-zero.

 Weddings cut to any lattice source dictionary preserving slot set and
 disjointness. Ports later support projection/numerators with same normalization.
 -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands Analysis
open scoped Topology ContDiff BigOperators Matrix
variable {I X : Type} [DecidableEq I] [Fintype X] [DecidableEq X]
variable {u v t:Finset I}{α:Type} -- c imply
section recursor
variable {W:Type*}[AddCommGroup W][Module ℝ W]
def directVote (T:Finset I):= (partners T).filter fun i=> i.1≠∅
lemma shrank (p:Finset I× Finset I) (h:p∈directVote t): p.2.card<t.card:=by
  obtain ⟨h,hp⟩:=mem_filter.mp h; have he := par_count h; have hu : 0<p.1.card:= card_pos.mpr (nonempty_iff_ne_empty.mpr hp); omega
-- polynomial evaluator works on graded kernel spines as nonconvolution ring via this protocol. scale on factor before multiplication: T'=source-positive marks. mpV disjoint operation.
def banner (T:Finset I) (U:Topaz I W) (mul: W→W→W) (stock:W) : W:= if T=∅ then stock else (↑T.card:ℝ)⁻¹ • ∑ p : directVote T, mul (sons U p.val.1) (banner p.val.2 U mul stock)
termination_by T.card
decreasing_by
   all_goals exact shrank _ p.property
lemma banner_one (k) (F : Topaz I W)(v:W→ W → W) : banner ∅ F v k=k:= by rw [banner,if_pos rfl]
lemma banner_s (k) (F : Topaz I W)(v:W→W→W)(hz : ∀ x,v 0 x=0)(t:Finset I):
   sons (fun T=> banner T F v k) t=festival v (sons F) (fun T=>banner T F v k) t := by
    by_cases h:t=∅
    · subst t; simp only [sons_empty,festival,par_once,sum_singleton,hz,banner_one]
    unfold festival
    let s i:= v (sons F (i: Finset I×Finset I).1) (banner i.2 F v k)
    calc
      _ = ∑ i∈directVote t,s i:= by
          have hp:t.card≠0:=card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
          change (t.card:ℝ) • banner t F v k= _; rw [banner,if_neg h, smul_inv_smul₀ (by exact_mod_cast hp),← Finset.sum_coe_sort (directVote t)]
      _ = _:= Finset.sum_subset (s₁:=directVote t) (filter_subset ..) (fun p hp hu=>by unfold s; rw [show p.1=∅ from not_not.mp (fun h=> hu (mem_filter.mpr ⟨hp,h⟩)),sons_empty,hz]) -- s defeq?
lemma bannerC (k) (F:Topaz I W)(v:W→W→W)(hz : ∀ x,v 0 x=0)(h:F ∅=0): Bulb k v F (fun t=>banner t F v k):= ⟨h,banner_one ..,funext (banner_s k F v hz)⟩
end recursor

-- graded heat operands. spanned
variable [Fintype α] [DecidableEq α] {u:I→ ℕ} {Z:Topaz I (HeatS α)}
def vanes (k:I→ℕ)(s:Finset I): ℕ:= ∑ i∈s,k i
lemma wind_cell (u:I→ℕ)(T:Finset I× Finset I)(h:T∈partners t): vanes u t=vanes u T.1+vanes u T.2:= by unfold vanes; obtain ⟨rfl,hp⟩:= (norms_par _ _).mp h; exact sum_union hp
@[simp] lemma vanes_empty (u:I→ℕ): vanes u ∅=0:=by simp [vanes]

lemma reels_sum {u:Finset I}{Z:I→HeatS α}{τ:ℕ}(h:∀ i∈u,Reels τ (Z i)): Reels τ (∑ i∈u,Z i) := by induction u using Finset.induction_on with
   | empty=> rw [sum_empty]; exact Reels.none
   | insert i s hi ih=>rw [sum_insert hi]; exact Reels.more (h i (mem_insert_self ..)) (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma walksR (h:∀ T,Reels (vanes u T) (Z T))(t): Reels (vanes u t) (banner t Z borne (upstart α)) := by
    induction t using strongInductionOn with
    | _ b ih=>
       rw [banner]; split; next hb=> subst b; simp only [vanes_empty]; exact reels_start
       apply Reels.sm; refine reels_sum (fun i _=>?_)
       have hl := ((mem_filter.mp i.property).1 : i.val ∈ partners b)
       rw [wind_cell u _ hl]; refine borne_r (Reels.sm (τ:= vanes u i.val.1) (h _) _) (ih _ ?_)
       apply ssubset_iff_subset_ne.mpr; exact ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp hl).1).2,fun v=> not_lt_of_ge (congr_arg Finset.card v).ge (shrank _ i.property)⟩
-- laws
end YM.RG08.Wax
