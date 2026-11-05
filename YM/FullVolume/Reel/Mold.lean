import YM.FullVolume.Spiral.Rune
import YM.FullVolume.Panel.Spokes
/-! Real-linear on the priced germs. Use *actual open neighborhoods* of the base so includes full ordered derivatives at Healthy =, and on path arrays with history-specific conventions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{R E : Rep G n}{Y:Hol G} {κ a b t e u w c σ v:ℝ} {Z : Support n} {B: SectionData F} {ι:Type}
section pack
variable {S:ℕ→Support n}{M:Local.Raw F n}{P:ι→ Local.Raw F n}
variable (K:Keeper R.p R.activities)(y:ι→ℂ) (hp: R.Lawful a b c v u)(hk:0<κ) (hH:Readable Y B R.p n w) (hM:Have R M S B Y w u κ)(hP:∀ i,Have R (P i) S B Y w u κ)
include K hp hk hH hM hP
local notation "T"=> K.supply (fun i=>joint B 0 (S i))
local notation "D"=> R.p
lemma moldW [Fintype ι] (hA:∀ i,Sculpts R.p (S i) (M.bulk i) (∑ j,y j • (P j).bulk i)) :
   coda B Y 0 S M R=∑ i,y i • coda B Y 0 S (P i) R:=by
    let A:= mint T M Y; let A' i:= mint T (P i) Y
    let x i:=gala K B Y (P i) S
    have hc(i): (tell (x i)).Format 0 Y R:= invest (A' i) K (usage T (hP i).format hp hH)
    have he(i):= sum_weigh (f:=fun j=>(P j).bulk i) (y:=y) (Y:=Y) (F:=F) univ (fun j=>(hP j).format.regular i) hH.order; let g j i:= (P j).row 0 S Y R.p.threshold i
    have hg i:M.row 0 S Y R.p.threshold i=∑ j,y j • g j i:= (Sculpts.weights (hA i) (hM.format.regular _) ((he i).1) hH.order).trans (he i|>.2)
    have hP₀ : ∀ i,Sculpts R.p (joint B 0 (S i)) (A.regular i) (∑ j,y j • (A' j).regular i):=by
       intro i V hz
       let p (a:F.Coeff):Config G n→ℂ:= Local.presented B 0 R.p.threshold a
       have hv' : p (M.row 0 S Y R.p.threshold i)=∑ j,y j • p (g j i):=by unfold p; rw [hg i,map_sum]; simp only [map_smul]
       filter_upwards [hA i V (Finset.disjoint_of_subset_left Finset.subset_union_left hz)] with W h
       let z:=increment V W; change M.bulk i z-p (M.row 0 S Y R.p.threshold i) z=_; rw [show M.bulk i z=_ from h,hv',Function.comp_apply,Finset.sum_apply, Finset.sum_apply,Function.comp_apply,Finset.sum_apply, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; change y j • _ - y j • _=y j • ( (P j).bulk i z- p (g j i) z); exact (smul_sub ..).symm
    have hP₁ : ∀ i, rebate Y B 0 (S i) R.p.threshold (M.bulk i)=∑ j,y j • rebate Y B 0 (S i) R.p.threshold ((P j).bulk i):=by
       intro i; let M'(u:Config G n→ℂ):= maskLinear R.p.threshold (S i) u; let J:=joint B 0 (S i)
       have h₁:M' (M.bulk i)=∑ j,y j • M' ((P j).bulk i):=by
           unfold M'; rw [show maskLinear R.p.threshold (S i) (M.bulk i)= _ from funext (hA i|>.sculpt)]; change maskLinear _ _ (∑ _, _)= _; rw [map_sum]; simp_rw [map_smul]
       let g₀:= maskLinear (G:=G) R.p.threshold J
       have h₂:g₀ (A.regular i)=∑ j,y j • g₀ ((A' j).regular i):=by rw [show g₀ (A.regular i)=g₀ _ from funext ((hP₀ i).sculpt)]; rw [map_sum];simp_rw [map_smul]
       let t:= Local.primary B (0:Site n) R.p.threshold; change M' (M.bulk i)- t (M.row 0 S Y _ i)-g₀ (A.regular i)=∑ j,y j • (M' ((P j).bulk i)-t (g j i)-g₀ ((A' j).regular i)); rw [h₁,hg i,map_sum,h₂]; simp only [map_smul,smul_sub,sum_sub_distrib]

    choose a₁ b₁ c₁ hx' using fun i=> (hP i).wage; obtain ⟨x₁,y₁,z₁,hT⟩:= hM.wage
    let t:= R.p.threshold
    let U:Response G n:=clipSum (fun i=> joint B 0 (S i)) (fun i=> rebate Y B 0 (S i) t (M.bulk i)); let V j:Response G n:= clipSum (fun i=>joint B 0 (S i)) (fun i=> rebate Y B 0 (S i) t ((P j).bulk i))
    have hV : U=∑ j,y j • V j:=by
        funext i K; unfold U t; simp_rw [hP₁]; unfold V clipSum cram; simp_rw [Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; rw [Summable.tsum_finsetSum _ ]; apply sum_congr rfl; intro i _; rw [tsum_mul_left]; -- check orientation
        intro j _; exact (((Local.Raw.dominated_pieces 0 hH (hP j).format ((hx' j).income hk le_rfl)).2.summable K).comp_injective Subtype.val_injective).mul_left _
    exact hV
end pack
end YM.MergeProof.Matric
