import YM.MergeProof.North.Wraith
import YM.OPE.Replicas.Corn

/-!
# Many slots per cell: port of YM/MergeProof/North/Wraith.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat
open Extra.Multi GridApprox.Nil Ac
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V J : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
local notation "X"=> Names V slotsZ
variable (v u:V)(B:Equiv.Perm V)(m:Motion)(x:Site c)
    (K:Box c→ Config G c→Poly (Names V slotsZ))(ψ:(V×slotsZ)→Response G c)(t:ℝ)(U : Config G c)
local notation "Q"=> sky m x
local notation "q"=> puff m x
variable (P:J→Support c)(e:Equiv.Perm J)(he:∀ j,P (e j)=sky m x (P j))
local notation "L"=> Equiv.sumCongr q e
local notation "Q0"=> flags t U
set_option quotPrecheck false
local notation "V0"=>pull m.1 x U
variable (s:Finset (FlowKind J c))
variable [Fintype J]
lemma rejoins (Z:J→ Config G c→Poly (Names V slotsZ))(hz:∀ i,Harm v B m (Z i (pull m.1 x U)) (Z (e i) U))(hZ:∀ i,Harm v B m (K i (pull m.1 x U)) (K (puff m x i) U)) (he:∀ j,P (e j)=sky m x (P j))(i:Box c):
       Harm v B m (Accent.closure K Z P t i (pull m.1 x U)) (Accent.closure K Z P t (puff m x i) U):=by
    have hp : Q i.1∩flags t U = Q i.2↔ i.1∩flags t (pull m.1 x U)=i.2:=by
       nth_rw 1 [← Work.H03.flags_send m.1 x]; simp only [shading]; rw [show affine m.1 x=⇑(turnSites m.1 x) from rfl,← Finset.image_inter _ _ (turnSites m.1 x).injective]; exact (Finset.image_injective (turnSites m.1 x).injective).eq_iff
    rw [quarters,quarters];
    let F:= tallyHead K Z P t (pull m.1 x U) i; let G:= tallyHead K Z P t U (q i)
    have hh : ∑ j,G j=∑ j,G ((L).finsetCongr j):=(Equiv.sum_comp ..).symm
    change Harm v B m (∑ j,F j) (∑ j,G j); rw [hh]; refine Harm.seq _ _ _ fun j _=> ?_
    unfold F G tallyHead; rw [show (L).finsetCongr j = j.image L by rw [Equiv.finsetCongr_apply,map_eq_image];rfl];
    have hv: (q i).1∩Q0 = (q i).2 ↔ i.1 ∩ flags t (V0)=i.2:=hp
    simp only [← sealP m x P e he j,ashes m x P e he j,Equiv.apply_eq_iff_eq,hv]; split; swap; exact fun _ _=> (scalar_z _).symm
    rw [prod_image (L).injective.injOn]; apply Harm.prod_; intro j hj; cases j
    next j=> exact hZ j
    next j=> exact hz j
-- row relations only on needed v
omit [Fintype J] in
lemma reborn (hp:B v=u)(he:∀ j:slotsZ,ψ (u,j)= upwards m x (ψ (v,j)))(ht:∀ i,Harm v B m (K i (pull m.1 x U)) (K (puff m x i) U))(i:Box c) :
   Harm v B m (Accent.closure K (conviction ψ (Names V slotsZ)) Prod.snd t i (pull m.1 x U)) (Accent.closure K (conviction ψ (Names V slotsZ)) Prod.snd t (puff m x i) U) :=by
    let P:= Equiv.prodCongr (nome (slotsZ:=slotsZ) B) (sky m x); refine rejoins v B m x K t U Prod.snd P _ ?_ ht (fun i=> rfl) _
    rintro ⟨⟨i,b⟩,s⟩; unfold conviction
    let z:=(i,b); change Harm _ _ _ (Poly.send ((X).fire z) (ψ (i,b) s (V0))) (Poly.send ((X).fire (nome B z)) (ψ (B i,b) (Q s) U)); let a:=(X).fire z
    rw [← go_one B]; by_cases h:v=i
    · rw [show B i=_ from h ▸ hp,he b,upwards,Equiv.symm_apply_apply, show ψ (i,b)=ψ (v,b) from by rw [h]]; exact Harm.solo _ _
    intro k hk; simp only [Poly.part_send]; have hA:k≠a:=fun e=>h ((which v z).1 (show Focused v a from e ▸ hk)).symm
    simp only [(show k≠(X).fire z from hA),Equiv.apply_eq_iff_eq,↓reduceIte];exact (scalar_z _).symm
end YM.MergeProof.Ribbons.ManyCopies
