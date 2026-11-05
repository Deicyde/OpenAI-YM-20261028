import YM.WilsonBulk.Broadcast.Chapter
import YM.WilsonBulk.Grid.Paper

/-!
# Mixing gear: moving to alphabet of coarse mesh with both fine residue
  and coarse slots. Sector reaction stencils then have finite support with
  full (coarse units) width at any assigned post-block demand level.
  Exact split and page semantics for collisions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Push FreeResolvent
open Work.F08 RG Sheet Pert.Bulk
variable {α β γ : Type} {f c n L : Side} {σ θ p : ℝ}
abbrev Echelon (α β : Type) (L : Side) := (Co L α) ⊕ β
abbrev fodder (α β : Type) (L : Side) := Market (Echelon α β L)

def tally {s : Side} (i : Co s α) : Co s (α⊕β) := (i.1,Sum.inl i.2)
def wage {s : Side} (i : Co s β) : Co s (α⊕β) := (i.1,Sum.inr i.2)
-- finite physical admission equivalence

def promenade (α β : Type) (g : Ratio c f) : Chamber (Co f α) (Co c β) ≃ Co c (Echelon α β g.count) := (Equiv.sumCongr (splitCo g α) (Equiv.refl _)).trans (Equiv.prodSumDistrib ..).symm
lemma pays_here (g : Ratio c f) (i : Co f α) : promenade α β g (Sum.inl i)=tally (splitCo g α i) := rfl
lemma pays_there (g : Ratio c f) (i : Co c β) : promenade α β g (Sum.inr i)=wage i := rfl
abbrev town (g : Ratio c f) := promenade α β g
-- infinite analog for one leg

def ascent (β : Type) (L : Side) (x : Market α) : fodder α β L := let y:=district L α x; (y.1,Sum.inl y.2)
def descent (α : Type) (L : Side) (x : Market β) : fodder α β L := (x.1, Sum.inr x.2)
lemma ascent_bucks (g : Ratio c f) (u : Market α) : promenade α β g (Sum.inl (small f α u))=small c _ (ascent β g.count u) := by rw [pays_here,← towns]; rfl
lemma descent_cash (g : Ratio c f) (v : Market β) : promenade α β g (Sum.inr (small c β v))=small c _ (descent α g.count v) := rfl
lemma ascent_roll (g : Ratio c f) (z : Site c) (x : Co f α) : rolls z _ (promenade α β g (Sum.inl x))=promenade α β g (Sum.inl (rolls (g.embed z) _ x)) := by
  obtain ⟨q,rfl⟩:= (splitCo g α).symm.surjective x; rcases q with ⟨q,t,u⟩; simp only [rolls_apply,pays_here,Equiv.apply_symm_apply]
  rw [show (splitCo g α).symm (q,t,u)=(g.assemble (q,t),u) from ?_,split_co]; simp only [tally]; congr 3
  · rw [show g.assemble (q,t)+g.embed z=g.assemble (q+z,t) from by unfold Ratio.assemble; dsimp only; rw [show g.embed (q+z)=g.embed q+g.embed z from map_add g.root q z]; abel,Ratio.assemble_parent]
  · simp
  · apply (splitCo g α).injective; rw [Equiv.apply_symm_apply,split_co]; simp
lemma descent_roll (g : Ratio c f) (z : Site c) (v : Co c β) : rolls z _ (promenade α β g (Sum.inr v))=promenade α β g (Sum.inr (rolls z _ v)) := rfl

lemma zero_cost (σ : ℝ) {p : ℝ} (hp : 0≤p) : (0:Row α β).strip σ p := fun i j=> by
  simp [Width,SumBudget,hp]
lemma acts_vanished (n : Side) : (0 : Row α β).acts n=0 := by ext1 x y; simp [Row.acts]
-- Sum interfaces, stack by cases on R

def brace (P : Row α β) (Q : Row α γ) : Row α (β⊕γ) := fun i j z=> Sum.elim (fun j=>P i j z) (fun j=> Q i j z) j
lemma brace_cost (P : Row α β) (Q : Row α γ) (h : P.strip σ p) (hp : Q.strip σ p) : (brace P Q).strip σ p := fun a b=> match b with | Sum.inl j=> h a j | Sum.inr j=> hp a j
lemma stack_cost (P : Row β α) (Q : Row γ α) (h : P.strip σ p) (hp : Q.strip σ p) : (stackRows P Q).strip σ p:= by simpa only [max_self] using strip_stack h hp
@[simp] lemma brace_tally (P : Row α β) (Q : Row α γ) (n : Side) (i j) : (brace P Q).acts n i (tally j)= P.acts n i j := rfl
@[simp] lemma stack_tally (P : Row β α) (Q : Row γ α) (n : Side) (i j) : (stackRows P Q).acts n (tally i) j=P.acts n i j := rfl
@[simp] lemma brace_wage (P : Row α β) (Q : Row α γ) (n : Side) (i j) : (brace P Q).acts n i (wage j)= Q.acts n i j := rfl
@[simp] lemma stack_wage (P : Row β α) (Q : Row γ α) (n : Side) (i j) : (stackRows P Q).acts n (wage i) j=Q.acts n i j := rfl

-- Fine lift into joint alphabet

def varnish (L : Side) (α β : Type) : Cross L α (Echelon α β L) := brace (unitRow _) 0
lemma varnish_cost (α β : Type) : (varnish L α β).strip σ 1 := brace_cost _ _ strip_unit (zero_cost _ zero_le_one)
lemma varnish_at (g : Ratio c f) (i j : Co f α) : installed g (varnish g.count α β) i (promenade _ _ g (Sum.inl j))= if i=j then 1 else 0 := by simp only [installed,Matrix.submatrix_apply,id_eq,pays_here,varnish,brace_tally,acts_unit,Matrix.one_apply, (splitCo g α).injective.eq_iff]
lemma varnish_not (g : Ratio c f) (i : Co f α) (j : Co c β) : installed g (varnish g.count α β) i (promenade _ _ g (Sum.inr j))=0 := by rw [installed, Matrix.submatrix_apply,id_eq,pays_there, varnish,brace_wage,acts_vanished]; rfl
end YM.WilsonBulk.Parapet
