import YM.MergeProof.Heap
import YM.MergeProof.North.Ally
import YM.MergeProof.North.Blot
import YM.MergeProof.North.Junction



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V
variable {v u:V}{B:Equiv.Perm V}{E:Equiv.Perm ι}{m:Motion}{x:Site f}{M:ι→Hat (Aged V) R}{π:R.activities.Moves m.1 x}(h:Kin M v u B m x π E)
namespace Kin
set_option quotPrecheck false -- order issue
variable {s:Finset ι}
def Dep (M:ι→Hat (Aged V) R)(v:V)(s:Finset ι):Prop:=∀ i∈s, Focused v ((M i).s)
include h
lemma lit (s:Finset ι): Dep M v s ↔ Dep M u (s.image E):=by
   constructor
   · intro hp i hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hi; exact (h.cares b).mp (hp b hb)
   intro hp i hi; exact (h.cares i).mpr (hp _ (mem_image_of_mem _ hi))
lemma together (ht:Dep M v s): Fits (hatMode M) s↔ Fits (hatMode M) (s.image E):=by
   have H:= Twin.dist (R:=V) E s (f:=fun i=> (M i).s.val) (f':=fun i=>(M i).s.val) Disjoint Disjoint (fun i hi j hj=>by rw [(h.plot _ (ht _ hi)).1,(h.plot _ (ht _ hj)).1];simp only [drum,pares]; exact (Finset.disjoint_image (nome B).injective).symm)
   exact ⟨fun g=> ⟨H.1 g.1,mem_univ _⟩,fun g=> ⟨H.2 g.1,mem_univ _⟩⟩
lemma towed (a:ℕ)(ht:Dep M v s): harvestKind M (.logKey a) s ↔ harvestKind M (.logKey (π.ep a)) (s.image E):=by
    unfold harvestKind; refine and_congr image_nonempty.symm (and_congr ?_ (h.together ht))
    have he(i)(hi:i∈s): i∈atKey M (.logKey a)↔ E i∈ atKey M (.logKey (π.ep a)):=by
       unfold atKey; simp only [mem_filter,mem_univ,true_and]; change WKey _=_↔ (M (E i)).M.turn=_; rw [(h.plot _ (ht _ hi)).2.1]; exact (Team.markRoute π).eq_iff.symm
    constructor
    · intro hx i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact (he j hj).1 (hx hj)
    intro hx i hi; exact (he i hi).2 (hx (mem_image_of_mem _ hi))
abbrev Stacked := Σ i : logDeck M, Rock M (.logKey i.val)
variable (M) in
lemma boatMark (i:ℕ)(s: Menu.Rock M (.logKey i)): i∈logDeck M:=by
   obtain ⟨j,h⟩:=s.val.property.1; exact (cams M _).2 ⟨j,(mem_filter.mp (s.val.property.2.1 h)).2⟩
-- map relevant composites. get lifting.
lemma covers :
    let t(v:V)(s:Stacked (M:=M)):= Dep M v s.2.val.val
    ∃ e:Equiv.Perm (Stacked (M:=M)), (∀ i,t v i↔ t u (e i))∧ ∀ i,t v i → (e i).2.val.val=i.2.val.val.image E ∧ (e i).1.val=π.ep i.1.val:=by
    intro p
    have hx (s j : Stacked (M:=M))(he:s.1.val=j.1.val)(hv:s.2.val.val=j.2.val.val):s=j:=by
       rcases s with ⟨s,a⟩; rcases j with ⟨j,b⟩; obtain rfl:= (Subtype.ext he : s=j); exact congr_arg (Sigma.mk s) (Subtype.ext (Subtype.ext hv))
    have ht(i:{i//p v i}):∃ x:{i//p u i},x.val.1.val=π.ep i.val.1.val ∧ x.val.2.val.val=i.val.2.val.val.image E:=by
       let b:=i.val.2; let k:=i.val.1.val; let s:=b.val.val; have he: Dep M v s:=i.property
       let y:=π.ep k; let x : Rock M (.logKey y):=⟨⟨s.image E,(h.towed k he).mp b.val.property⟩,by dsimp only; rw [card_image_of_injective _ E.injective]; exact b.property⟩
       refine ⟨⟨⟨⟨y,h.boatMark M y x⟩,x⟩,(h.lit s).1 he⟩,rfl,rfl⟩ -- parameter h ?
    choose f Hf hp using ht
    have he: Bijective f:=by
       refine ⟨fun i j he=> Subtype.ext (hx _ _ ?_ ?_),fun i=>?_⟩
       · exact π.ep.injective ((Hf i).symm.trans ((congr_arg (fun i=> i.val.1.val) he).trans (Hf j)))
       · exact Finset.image_injective E.injective ((hp i).symm.trans ((congr_arg (fun i=>i.val.2.val.val) he).trans (hp j)))
       obtain ⟨k,hk⟩:= π.ep.surjective i.val.1.val; let s:= i.val.2.val.val.image E.symm; have hv : s.image E=i.val.2.val.val:=by unfold s; rw [image_image];simp
       have hS : Dep M v s:= (h.lit _).2 (hv ▸ i.property); have ht: harvestKind M (.logKey (π.ep k)) (s.image E):=by rw [hk,hv]; exact i.val.2.val.property
       let r : Rock M (.logKey k):= ⟨⟨s,(h.towed k hS).2 ht⟩,show 2 ≤ s.card from (by rw [← card_image_of_injective s E.injective,hv]; exact i.val.2.property)⟩
       let j:{i//p v i}:= ⟨⟨⟨k,h.boatMark M _ r⟩,r⟩,hS⟩; exact ⟨j,Subtype.ext (hx _ _ ((Hf j).trans hk) ((hp j).trans hv))⟩
    obtain ⟨e,hE,hd⟩:=extends_on he
    exact ⟨e,hd,fun i hi=>by rw [show e i=(f ⟨i,hi⟩).val from hE ⟨i,hi⟩]; exact ⟨hp _,Hf _⟩⟩
end Kin
end YM.MergeProof.Ribbons
