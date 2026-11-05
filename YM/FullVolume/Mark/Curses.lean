import YM.FullVolume.Mark.Hinge
/-! Quantitative chord from subtracting individual column offers.

Every statement about a differenced offer includes summability in the base
arena. For infinite regular families we never weaken supports or assume a
pointwise normed space of arbitrary `Healthy` germs. Rotation uses a *common*
Move within one step (actual), and across cutoffs may use even different
permutations (tracked through boarding).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
section
variable {n:Side}{R:Rep G n}(P Q: Coefficient F n){a b c κ:ℝ}
def breakP : Coefficient F n:= ⟨P.x-Q.x,P.support,P.regular-Q.regular,P.forced-Q.forced⟩
lemma tell_br (P Q:Pin F n): tell (P-Q)= breakP (tell P) (tell Q):=rfl
lemma cogent (K:Keeper R.p R.activities)(h:P.remBound 0 R κ a)(hx: Q.remBound 0 R κ b): stowK K (breakP P Q)= stowK K P-stowK K Q:=by
   funext i; by_cases ht:i∈ range (cart K)
   · obtain ⟨i,rfl⟩:=ht
     funext V
     rw [stowed,Pi.sub_apply,stowed,stowed]; let p:=i.val
     let f j:=P.forced j V; let g j:=Q.forced j V; exact Summable.tsum_sub (((rem_dominated h).summable V).comp_injective (Subtype.val_injective)) (((rem_dominated hx).summable V).comp_injective Subtype.val_injective) -- infer subtype
   rw [pit _ _ ht,Pi.sub_apply,pit _ _ ht,pit _ _ ht,sub_zero]
lemma collected (K:Keeper R.p R.activities)(hp:P.support=Q.support)(h:P.remBound 0 R κ a)(hx: Q.remBound 0 R κ b): capture (breakP P Q) K=capture P K-capture Q K:= Prod.ext (by
   funext i; change liveE (breakP P Q) i = liveE P i-liveE Q i; simp_rw [liveE, show (breakP P Q).support= P.support from rfl, hp]; by_cases he:i∈ Set.range (tongue Q.support); obtain ⟨i,rfl⟩:=he; simp_rw [(tongue Q.support).injective.extend_apply]; rfl
   simp_rw [extend_apply' _ _ _ he]; simp) (cogent P Q K h hx)
lemma stretch_br (z:ℂ): Extra.Histories.stretch z (breakP P Q)=breakP (Extra.Histories.stretch z P) (Extra.Histories.stretch z Q):= by unfold Extra.Histories.stretch breakP; simp [smul_sub]
lemma turn_br (m : Motion) (S : R.activities.Moves m.1 0): audition S (breakP P Q) = breakP (audition S P) (audition S Q):=by
   have hf : reorient S (breakP P Q) = breakP (reorient S P) (reorient S Q):=by
      unfold reorient breakP; rw [map_sub]; rfl
   unfold audition; split; rw [hf]; simp [barAll,breakP,star_sub,← Pi.star_def]; exact ⟨rfl,rfl⟩
   exact hf
lemma turn_same (m:Motion)(S : R.activities.Moves m.1 0)(h:P.support=Q.support): (audition S P).support=(audition S Q).support:=by unfold audition; split<;>simp [barAll, Push.Local.reorient,h]
section merge
variable {ι:Type} {X F' :ι→ Coefficient F n}
variable (e:ℕ≃ι×ℕ)
lemma melt (h:Summable fun i=>(X i).x)(hb:Summable fun i=>(F' i).x)(hv: ∀ i V,Summable fun k=> ((X k).forced i V))(hu:∀ i V,Summable fun k=>(F' k).forced i V): Extra.Histories.merge e (fun i=> breakP (X i) (F' i))= breakP (Extra.Histories.merge e X) (Extra.Histories.merge e F'):=by
    unfold Extra.Histories.merge breakP
    congr 1 -- term ts & K
    · exact h.tsum_sub hb
    funext i V; exact (hv i V).tsum_sub (hu i V)
lemma pencil_br (f:F.Coeff →ₗ[ℂ] ι →ℂ)[Fintype ι] (x:F.Coeff): Extra.Histories.pencil e (fun i=>breakP (X i) (F' i)) f x = breakP (Extra.Histories.pencil e X f x) (Extra.Histories.pencil e F' f x):=by
    unfold Extra.Histories.pencil; simp_rw [stretch_br]; exact melt e Summable.of_finite Summable.of_finite (fun i V=>Summable.of_finite) (fun i V=>Summable.of_finite)
end merge
-- turn proof
end
end YM.MergeProof.Matric
