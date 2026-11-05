import YM.RG08.Carrel.Passage

/-! # Extract path template U at any chosen anchor slot -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Glyph Filter Finset Function
open scoped BigOperators Topology Classical ENNReal
variable {I:Type}{n:ℕ}{P:Side}{F G:Flake n (Market I)}{σ p:ℝ}

def neck (i:Fin n)(F:Flake n (Market I))(w:Slide I n):=if (w i).1=0 then F w else 0
lemma assumptive (i:Fin n)(h:Cohort F): grown (neck i F)=F:=by
 funext w
 rw [grown];simp_rw [neck,show ∀ q x,F (sway q x)=F x from h];unfold sway pass;dsimp only [comp_apply];simp_rw [← sub_eq_add_neg,sub_eq_zero]; simp [tsum_ite_eq, eq_comm]
lemma sensible [Fintype I](i:Fin n)(h:Held (carpet I) σ p F)(hp:0≤p):Won (neck i F) σ ((Fintype.card I:ℝ)*p):=by
  refine ⟨mul_nonneg (by positivity) hp,?_⟩
  calc
   Cost _ _ ≤ (∑ u:I,∑' w,Forms.row (mark (carpet I) σ F) i (0,u) w) := ?_
   _ ≤ (∑ _ : I,ENNReal.ofReal p):=Finset.sum_le_sum fun u _=>ensign.mp h i (0,u)
   _ = _:=by
      simp [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card I:ℝ))]
  rw [← tsum_fintype (L:=SummationFilter.unconditional I) (fun u:I => ∑' w, Forms.row (mark (carpet I) σ F) i (0,u) w),ENNReal.tsum_comm];apply ENNReal.tsum_le_tsum;intro w
  unfold neck
  split_ifs with ht
  · apply le_trans _ (ENNReal.le_tsum (f:=fun c:I=>Forms.row _ i ((0:Cover),c) w) (w i).2)
    unfold Forms.row mark;rw [if_pos (by simp [←ht]),shelf_diam]
  simp [bill]

lemma grown_sub (h:Won F σ p)(H:Won G σ p)(ht:0≤σ)(i:Fin n):grown (F-G)=grown F-grown G:=by
 have he(w:Slide I n): Injective (fun p:Cover=>sway (-p) w):=by
    intro a b hh; have hx:=congrArg Prod.fst (congrFun hh i);change (w i).1 + -a=(w i).1+-b at hx;exact neg_inj.mp (add_left_cancel hx)
 funext w
 change (∑' q:Cover,(F (sway (-q) w)-G (sway (-q) w)))=_-_
 exact ((word_sum h ht).comp_injective (he w)).tsum_sub ((word_sum H ht).comp_injective (he w))

-- linear & symmetrization ret.
lemma ordered (F:Flake n (Market I))(i:Fin n)(e:Equiv.Perm (Fin n))(H:Cohort F):
    woven (pour (P:=P) F i) e=pour (woven F e) i:=by
 funext w
 change pour F i _= _; rw [common H i (e.symm i),pour,pour,←(twist e).tsum_eq]
 apply tsum_congr; intro x
 change (lantern _ (w ∘ e)).indicator F (x ∘ e)=_
 have he : x ∘ e∈lantern (e.symm i) (w ∘ e) ↔ x∈lantern i w:=by
   change (x (e (e.symm i))=_ ∧ _ )↔(x i=_ ∧ _)
   change (x (e (e.symm i))= reach (w (e (e.symm i))) ∧ _ )↔_
   rw [Equiv.apply_symm_apply];congr! 1
   constructor
   · intro h;funext j;obtain ⟨k,rfl⟩:= e.surjective j;exact congrFun h k
   exact fun hg=> congrArg (· ∘ e) hg
 unfold Set.indicator; simp only [he];rfl

end YM.RG08.Carrel
