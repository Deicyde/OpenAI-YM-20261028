import YM.MergeProof.SwitchCost
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Postcards
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge   Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
structure Hat (B:Census V)(R:Rep G f) where
   M : Lotus.Leaf R
   s : B.Mode
   shiny : s.val.Nonempty
   charge: ℂ
variable (M:Hat B R)
def sumFee (w:V→ℝ):ℝ:= Poly.toll w M.s*‖M.charge‖
def fare (w:V→ℝ):= sumFee M w * M.M.weight
def sing (w:V→ℝ):Poly B:= Poly.send M.s (M.charge/(sumFee M w:ℂ))
def stamp : Poly B:= Poly.send M.s M.charge
lemma powered : M.s≠B.quiet:=fun h=> M.shiny.ne_empty (congr_arg Subtype.val h)
lemma virtue (w:V→ℝ) : (sing M w).part B.quiet=0 ∧ sing M w * sing M w=0:= by
   refine ⟨?_,?_⟩; unfold sing; simp [(powered M).symm]
   by_contra hn; obtain ⟨z,hz⟩:= Extra.Trajectories.merges_of_tagged_mul hn; obtain ⟨i,hi⟩:= M.shiny; exact Finset.disjoint_left.mp hz.1 hi hi

lemma sent (s:B.Mode)(x p:ℂ): p • Poly.send s x= Poly.send s (p*x):= by ext i; simp only [Poly.part_smul,Poly.part_send]; split; rfl; simp
variable {w:V→ℝ}(h:∀ i,0<w i)
include h
lemma timed : 0 ≤ sumFee M w:= mul_nonneg (Poly.worth h _).le (norm_nonneg _)
lemma private_b : sumFee M w=0 ↔ M.charge=0:=by unfold sumFee; rw [mul_eq_zero, or_iff_right (Poly.worth h M.s).ne']; exact norm_eq_zero
lemma paid : Poly.price w (sing M w) ≤ 1:=by
   unfold sing; rw [Poly.solo]; by_cases hp:sumFee M w=0
   · rw [hp]; simp
   have ht:0<sumFee M w:=(timed M h).lt_of_ne (Ne.symm hp); rw [norm_div,Complex.norm_real,Real.norm_of_nonneg ht.le, ← mul_div_assoc]; change sumFee M w / sumFee M w≤1; rw [div_self hp]
lemma purchase : (↑(sumFee M w):ℂ) • sing M w=stamp M:=by
   rw [sing,sent,stamp]; congr 1; by_cases ht:M.charge=0; · simp [ht]
   have he: (↑(sumFee M w):ℂ)≠0:=by exact_mod_cast mt (private_b M h).1 ht
   field_simp
omit h
variable [Fintype ι](q:ι→ Hat B R)
def WKey (M:Hat B R): Wing:=M.M.turn
def legs : Finset Wing:=Finset.univ.image fun i:ι=>WKey (q i)
def planter (i:Wing):ℕ⊕ℕ:= match i with | .logKey k=>.inl k | .gasKey k=>.inr k

def logDeck : Finset ℕ:= ((legs q).image planter).toLeft
def gasDeck : Finset ℕ:= ((legs q).image planter).toRight
lemma cams (p:ℕ): p∈ logDeck q↔ ∃ i:ι,WKey (q i)=.logKey p:=by
   unfold logDeck legs; rw [mem_toLeft,image_image];simp only [Finset.mem_image,Function.comp_apply,mem_univ,true_and];apply exists_congr; intro i; cases WKey (q i) <;> simp [planter]
lemma slots (p:ℕ): p∈ gasDeck q↔ ∃ i:ι,WKey (q i)=.gasKey p:=by
   unfold gasDeck legs; rw [mem_toRight,image_image]; simp only [Finset.mem_image,Function.comp_apply,mem_univ,true_and];apply exists_congr; intro i; cases WKey (q i) <;> simp [planter]
def amount (U:Config G f):Poly B:= (((M.M.ingredient U):ℂ)) • stamp M
def rush (j:Wing)(U:Config G f):= ∑ i:ι, if WKey (q i)=j then amount (q i) U else 0
lemma rush_vacuous (j:Wing)(U:Config G f)(hv:∀ i,WKey (q i) ≠ j): rush q j U=0:=sum_eq_zero fun i _=> if_neg (hv _)
lemma still (j:Wing)(U: Config G f): (rush q j U).part B.quiet=0:=by
   unfold rush; rw [Poly.part_sum];apply Finset.sum_eq_zero; intro i _; split; · unfold amount stamp; rw [Poly.part_smul,Poly.part_send,if_neg (powered (q i)).symm,mul_zero]
   rfl
lemma varnish (U:Config G f): amount M U=Poly.send M.s ((↑(M.M.ingredient U):ℂ)*M.charge):=sent ..
end YM.MergeProof.Menu
