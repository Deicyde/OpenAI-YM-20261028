import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import YM.Next.RANK.Ray
import YM.Next.RANK.ScaleScale

/-!
# Mixed heater reads on common kernel. Note the matrix may mix weight d by order n,
but reading projected on any ambient keys with *own* truncation degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Lattice Wilson RG Labels Price Normal Function Configuration Beamer Rise MvPolynomial Finset Filter LiftMark
open scoped Topology BigOperators Classical
variable {G : Gauge} {W : Family G} {d D : ℕ} {V Z : Type*}
def alum (h:d≤D)(i:KeyIn G d): KeyIn G D:= ⟨i.val,i.property.trans h⟩
variable (h:d≤D)
lemma alum_thaw (p:Label G d): rename (alum h) (thawKey p)=thawKey (raiseLabel G h p):=by
   apply rename_injective (R:=ℂ) (f:=(Subtype.val : KeyIn G D → Key G)) (by exact Subtype.val_injective)
   rw [returns,rename_rename]; exact returns _
lemma feeD (F:V→ Address G) (P:poly V): trim (exchange (ink D F) P) (key G D) d=rename (alum h) (trim (exchange (ink d F) P) (key G d) d):=by
   rw [← show trim (rename (alum h) _) _ _= rename (alum h) (trim (exchange (ink d F) P) (key G d) d) from trim_rename (alum h) (key G D) _ d]; apply verdict_map d _ (Q:=(rename (alum h)).comp (exchange (ink d F))) _ P
   intro i
   have hc:= show (univ (α:=KeyIn G d)).image (alum h)⊆univ from subset_univ _
   simp only [AlgHom.comp_apply,exchange_x,ink,glyph,map_sum,map_smul, Finsupp.linearCombination_single,rename_X]
   let r:=level (key G D) d
   change r _=r _; rw [map_sum,map_sum, ← sum_subset hc ?_, sum_image]; rotate_left
   · exact (show Injective (alum (G:=G) h) from fun _ _ hh=>Subtype.ext (congr_arg (fun i: KeyIn G D => i.val) hh)).injOn
   · intro x hx hz; have hX: ¬generation x.val ≤ d:= fun ht=> hz (mem_image.mpr ⟨⟨x.val,ht⟩,mem_univ _,rfl⟩)
     rw [map_smul,show r (MvPolynomial.X x)=0 from ?_,smul_zero]
     change trim (monomial (Finsupp.single x 1) (1:ℂ)) (key G D) d=_; rw [trim_mono,Finsupp.weight_single,one_smul,if_neg (show ¬ key G D x ≤ d from hX)]
   rfl
lemma costs_X (F:V→ Address G) (P:poly V) : trim (exchange (features D F 1) P) Configuration.bear d = rename Sum.inl (rename (alum h) (Rise.trim (exchange (ink d F) P) (key G d) d)):=by
   rw [← feeD h,← show Rise.trim _ bear d=rename (Sum.inl : KeyIn G D → KeyIn G D ⊕ V) (trim (exchange (ink D F) P) (key G D) d) from trim_rename ..]
   apply verdict_map d _ (Q:=(rename Sum.inl).comp (exchange (ink D F))) ?_ P; intro i
   rw [AlgHom.comp_apply, Normal.exchange_x,intern,trim_add, X,X,trim_mono]
   rw [Finsupp.weight_single]; simp only [one_smul,bear,Sum.elim_inr, if_neg (show ¬ D+1≤ d by omega),add_zero]

lemma alignedX (F: V→ Address G) (ρ:ℝ)(hp:0<ρ) {k N p : ℕ} {v u : W.label d} {R: W.label d→ₗ[ℂ] W.label d} (hg: Price.Solves W ρ d k N p R v u)(P:poly V)(hw:Verdict F d P ((W.labels.level d).coords.symm ((W.labels.level d).scaled (shrink W k N p) (R u)))):
   trim (exchange (features D F ρ) P) bear d=rename Sum.inl (thawKey (raiseLabel G h ((W.labels.level d).coords.symm v))):=by
    unfold Verdict at hw; rw [costs] at hw; have hX:= rename_injective (R:=ℂ) Sum.inl Sum.inl_injective hw
    rw [spaced D F ρ, jets_keep,costs_X h,hX,alum_thaw h]
    unfold Solves at hg; rw [hg,thawKey]
    let W':= (W.labels.level d).coords.symm; rw [show (raiseLabel G h (W' (weightTag W d ρ v))).val= jets generation (ρ:ℂ) (raiseLabel G h (W' v)).val from pure_weight (C:=W) ρ v,← peel, cycles]; rfl
    exact Complex.ofReal_ne_zero.mpr hp.ne'
end YM.Next.Rank.Perch
