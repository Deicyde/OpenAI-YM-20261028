import YM.OPE.Trees.Scene
/-!
# Align configurations for contractions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{L:Register G}{S:Table L} {H:DiffPlan S} (A:Table L)(hA:A.Symmetric)
    {I J K:Type}[Fintype I][Fintype J][Fintype K]{a b c:Finset I}{i:I}{x:I→ E4}{p:I→ L.Token} {w:Mode H}(P:Prescription H){y:J→ E4}{q:J→ L.Token}

private lemma permutation {I J:Type}[Fintype I][Fintype J]{x:I→E4}{p:I→L.Token}{x':J→E4}{p':J→L.Token}(A:Table L)(he:A.Symmetric)(hx:Injective x)(e:J≃I)(hv:x ∘ e=x')(hp:p ∘ e=p') : observe A x p= observe A x' p':=by rw [← hv,← hp]; exact (perm_observe A he e p hx).symm

private def tandem (he:a∪b=c)(h:Disjoint a b) : ((↑a:Type)⊕ (↑b:Type)) ≃ (↑c:Type):= (Equiv.Finset.union _ _ h).trans (Equiv.setCongr (show ((a∪b:Finset I) : Set I) = (c:Set I) from congr_arg _ he))
private def alias_ (he:a∪b=c)(h:Disjoint a b)(J:Type): ((↑a:Type) ⊕ ((↑b:Type)⊕ J))≃ ((↑c:Type)⊕ J):= (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr (tandem he h) (Equiv.refl _))
private lemma colored {V:Type*}(s:I→V)(t:J→ V)(he:a∪b=c)(h:Disjoint a b) : beside (crop s c) t ∘ alias_ he h J= beside (crop s a) (beside (crop s b) t):=by
    funext i; rcases i with i|(i|i)<;> rfl
include hA
lemma logs_combine (he:a∪b=c) (h:Disjoint a b) (hx:Injective (beside (crop x c) y)) : whole A c x p y q=whole A a x p (beside (crop x b) y) (beside (crop p b) q):= permutation A hA hx (alias_ he h J) (colored x _ he h) (colored p _ he h)
private def basis0 (i:I) : Unit ≃ (↑({i}:Finset I):Type):=
    ⟨fun _=> ⟨i,mem_singleton_self _⟩,fun _=>(),fun _=>rfl,fun u=> by refine Subtype.ext ?_; exact (mem_singleton.mp u.property).symm⟩
lemma one_combine (he:insert i b=c)(hv:i∉ b)(hx:Injective (beside (crop x c) y)) : whole A c x (update p i (P.letter w)) y q = pickOne P A x i w (beside (crop x b) y) (beside (crop p b) q):=by
    have h : Disjoint ({i}:Finset I) b:= Finset.disjoint_singleton_left.mpr hv; let P':=update p i (P.letter w); let e:= (Equiv.sumCongr (basis0 i) (Equiv.refl ((↑b:Type)⊕J))).trans (alias_ (show {i}∪ b=c by rw [singleton_union,he]) h J)
    refine permutation A hA hx e ?_ ?_
    · funext j; rcases j with ⟨⟩|(j|j) <;> rfl
    have hu:crop (update p i (P.letter w)) b= crop p b:= funext (fun j=> update_of_ne (show j.val≠i from fun he=>hv (he ▸ j.property)) _ _)
    rw [← hu]; funext j; rcases j with ⟨⟩|j; swap; rcases j with j|j <;> rfl
    change P' i = _; unfold P'; rw [Function.update_self]; rfl
end YM.OPE.Arboreal
