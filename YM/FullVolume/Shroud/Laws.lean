import YM.FullVolume.Shroud.Replica
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ b w:ℝ}
open Quake Well
namespace Muslin
variable (R:Rep G n)(t κ :ℝ)(h:R.Lawful σ C Λ b w)
set_option quotPrecheck false
local notation "S"=> stitch R t
local notation "p"=> R.p
local notation "u"=> R.p.threshold
local notation "A"=> R.activities
def replayK (n:Side): ℕ ↪ ℕ:=Embedding.inl.trans (guardK (n:=n)).symm.toEmbedding
def reuse (n:Side): Hearts n ↪ ℕ:=Embedding.inr.trans (guardK (n:=n)).symm.toEmbedding
local notation "Lb"=> replayK n
local notation "Rs"=> reuse n
lemma bank (i)(U:Config G n): (S).gasOccurrence R.p (i.map Lb) U =(A).gasOccurrence R.p i U:=by
    let T:=stitch R t; have he(i): T.forced (replayK n i)=R.activities.forced i:=ks R t (.inl i); have hv(i): T.K (replayK n i)=(A).K i:=ks' R t (.inl i)
    have h : T.admissible (p) U (Finset.map Lb i) ↔ (A).admissible (p) U i:= by
        unfold Activities.admissible; rw [paired Lb (Q:=fun i j=> Disjoint ..) (fun i j=>by rw [he,he]), mapped_biUnion Lb (fun i=>congr_arg ForcedAddress.inventory (he i))]
    unfold Activities.gasOccurrence; split; next h'=> have hh:=h.mp h'; rw [if_pos hh, prod_map]; exact Finset.prod_congr rfl (fun i _=>congr_fun (hv i) U)
    next h'=> rw [if_neg (mt h.mpr h')]
lemma owners {b:Finset ℕ}{U:Config G n}{x:Hearts n}(h:(stitch R t).admissible R.p U b)(hx: reuse n x ∈ b): b={reuse n x} ∧ flags R.p.threshold U=x.val:=by
    let V:=(S); let y:=reuse n x; have hg: ((V).forced y)= dyed G x:= ks R t (.inr x)
    have hb:b={y}:= Finset.Subset.antisymm (fun i hi=> Finset.mem_singleton.mpr (by
       by_contra he; have H:Disjoint (V.forced i).support (V.forced y).support:= h.1 hi hx he; rw [hg] at H; obtain ⟨z,hz⟩:= (V.forced i).inventory_ne.mono (V.forced i).inventory_sup; exact Finset.disjoint_left.mp H hz (Finset.mem_univ _))) (Finset.singleton_subset_iff.mpr hx)
    have ht: b.biUnion (fun i=> (V.forced i).inventory) = flags u U:= h.2; rw [hb,singleton_biUnion,hg] at ht; exact ⟨hb,ht.symm⟩
lemma doll (U:Config G n)(x:Hearts n)(h:flags u U=x.val) : (S).gasOccurrence p {reuse n x} U=song R t U:=by
    have he:(S).forced (reuse n x)= dyed G x:= ks R t (.inr x) -- fix
    have hx: (S).admissible p U {reuse n x}:=by refine ⟨?_ ,?_⟩; simp [Set.Pairwise]; rw [singleton_biUnion,he,h];rfl
    unfold Activities.gasOccurrence; rw [if_pos hx,Finset.prod_singleton,show (S).K (reuse n x)=chart R t x from ks' R t (.inr x),chart,if_pos h]
lemma lands (i:ℕ)(h:i ∉ Set.range Lb) : i∈ Set.range Rs:=by
    obtain ⟨i,rfl⟩:= (guardK (n:=n)).symm.surjective i; cases i; exact (h ⟨_,rfl⟩).elim; exact ⟨_,rfl⟩
variable {g' k':ℝ}(hz:(stitch R t).Valid R.p g' k')
include h hz
lemma exposed (U:Config G n): (S).gas R.p U= if flags u U=∅ then (A).gas R.p U else Real.exp (-t* BetaTransport.kinetic R.path R.clip R.p U)*(A).gas p U:=by
    split; next h=> rw [Activities.gas_one («p»:=R.p) _ h, Activities.gas_one («p»:=R.p) _ h]
    next h=>
       let i:Hearts n:= ⟨flags u U, nonempty_iff_ne_empty.mpr h⟩; let y:=reuse n i; let f (k:Finset ℕ):= if k={y} then song R t U else 0
       let T k:= (S).gasOccurrence p k U
       have hf: HasSum f (song R t U):= by
           exact hasSum_ite_eq ({y}:Finset ℕ) _
       have hp: ∑' k,(T k - f k)=(A).gas p U :=by
          apply transferred_packets Lb (g:=fun i=> (A).gasOccurrence p i U) (fun k=>?_) (fun i j hi hj=>?_)
          · have h: Finset.map Lb k ≠ {y}:=by
               intro H; obtain ⟨j,hj,he⟩:= Finset.mem_map.mp ((H.symm ▸ Finset.mem_singleton_self y) : y∈ Finset.map Lb k); have h: (guardK (n:=n)).symm (.inl j)= guardK.symm (.inr i):=he; cases (guardK (n:=n)).symm.injective h
            unfold T; rw [bank R t k U] -- needs unfold T
            unfold f;rw [if_neg h,sub_zero]
          by_cases H:i={y}; subst i; rw [show T {y} = _ from doll R t _ _ rfl, show f {y} = song R t U from if_pos rfl,sub_self]
          obtain ⟨v,rfl⟩:=lands j hj
          have ht : ¬ (S).admissible p U i:=by intro ht; obtain ⟨hv,hp⟩:=owners R t ht hi; exact H (by rw [hv]; exact congr_arg (fun t=>({reuse n t}:Finset ℕ)) (Subtype.ext hp.symm))
          unfold T f Activities.gasOccurrence; rw [if_neg H,if_neg ht,sub_self]
       rw [Summable.tsum_sub ((Activities.gasSeries hz).summable U) hf.summable,hf.tsum_eq] at hp; change (S).gas p U-song R t U=_ at hp; simp only [song] at hp; linarith only [hp]
-- cost cleanup separate
end Muslin
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Muslin.exposed
