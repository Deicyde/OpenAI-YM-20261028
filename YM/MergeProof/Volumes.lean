import YM.MergeProof.Memo


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Extra.Histories.Relay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}
namespace Tale
variable {n c : Side}{R:Rep G n}{E:Rep G c}{H:GaugeDoor R E}{S:StepData c n}
lemma plus {X:Wing→Prop}{f g : Config G n→ℂ}{Z K:Box n→ Config G n→ℂ}{Z' K':Box c→ Config G c→ℂ}{α o v δ μ}{r s p q:ℝ}(h:Tale X o v α f Z Z' δ r p H)(hp:Tale X o v α g K K' μ s q H)(hw:SoundDoor S H) : Tale X o v α (f+g) (Z+K) (Z'+K') (δ+μ) (r+s) (p+q) H:=by
    have hx(j:Bool): Tale X o v α (twain f g j) (twain Z K j) (twain Z' K' j) (twain δ μ j) (twain r s j) (twain p q j) H:=by cases j; exact hp; exact h
    refine Tale.upon hw hx ?_ ?_ ?_ ?_ ⟨?_,Summable.of_finite,?_⟩ ⟨?_,Summable.of_finite,?_⟩
    · intro i; exact (show ∑ j:Bool, twain f g j i=(f+g) i from Fintype.sum_bool _) ▸ hasSum_fintype _
    · intro i j; exact (show ∑ m:Bool, twain Z K m i j=(Z+K) i j from Fintype.sum_bool _) ▸ hasSum_fintype _
    · intro i j; exact (show ∑ m:Bool, twain Z' K' m i j=(Z'+K') i j from Fintype.sum_bool _) ▸ hasSum_fintype _
    · exact (show ∑ b:Bool,twain δ μ b=δ+μ from Fintype.sum_bool _) ▸ hasSum_fintype (twain δ μ)
    · intro j; obtain ⟨ι,u,M,s,ψ,h⟩:=hx j; exact sumBudget_credit h.purchase
    · exact (by rw [tsum_fintype,Fintype.sum_bool]; rfl)
    · intro j; obtain ⟨ι,u,M,s,ψ,h⟩:=hx j; obtain ⟨a,hv,ht⟩:=h.cost.toll; exact sumBudget_credit hv
    exact (by rw [tsum_fintype,Fintype.sum_bool]; rfl)
end Tale
variable {n:Side}{R:Rep G n}{o:Site n}
lemma duo_profile {P Q:Coefficient F n}{t u v:ℝ}(hp:P.remBound o R t u)(hq:Q.remBound o R t v): profile R.activities (beside P Q).forced=profile R.activities P.forced+profile R.activities Q.forced:=by
   rw [sideK]; funext p U; change ∑' s:{i//barcode R.activities i=p}, (P.forced s.val U+Q.forced s.val U)=_+_
   exact Summable.tsum_add (((rem_dominated hp).summable U).comp_injective Subtype.val_injective) (((rem_dominated hq).summable U).comp_injective Subtype.val_injective)
lemma hall {ι:Type*}(B:SectionData F)(e:ℕ≃ι×ℕ)(P:ι→ Coefficient F n){t : ι → ℝ}{v : ℝ}(hp:0 < v)
    (h : ∀ i, (P i).remBound o R v (t i)) (ht : Summable t)(hx:Summable fun i=>F.coeffSize (P i).x) (U:Config G n) : HasSum (fun i => (P i).exponentialEntry o B R U) ((Extra.Histories.merge e P).exponentialEntry o B R U) := by
    have ha:= merge_budget e P hp h ht|>.2.1
    let f (x : ι × ℕ) := (P x.1).maskedTerm R x.2 U
    have hj : Summable f := ha.summable U
    have he (i : Coefficient F n) : i.exponentialEntry o B R U = part B o R U i.x + ∑' j, i.maskedTerm R j U := rfl
    simp_rw [he]; rw [show ∑' j, (Extra.Histories.merge e P).maskedTerm R j U= _ from e.tsum_eq f,hj.tsum_prod]
    exact ((part B o R U).toContinuousLinearMap.hasSum (Size.series F hx).of_norm.hasSum).add hj.prod.hasSum
lemma duo_exp (B:SectionData F){P Q:Coefficient F n}{t u v:ℝ}(hp:P.remBound o R t u)(hq:Q.remBound o R t v): (beside P Q).exponentialEntry o B R=P.exponentialEntry o B R+Q.exponentialEntry o B R:=by
    have hr(i:Bool) : (twain P Q i).remBound o R t (twain u v i) := by cases i; exact hq; exact hp
    have h0:0 < t:=by obtain ⟨a,b,-,-,-,h,-⟩:=hp; exact h
    funext U
    have h:= hall B (code _) (twain P Q) h0 hr Summable.of_finite Summable.of_finite U|>.tsum_eq; rw [tsum_fintype,Fintype.sum_bool] at h; exact h.symm
end YM.MergeProof
