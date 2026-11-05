import YM.MergeProof.North.Pond
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Pond

/- generalized from YM.MergeProof.North.Shan to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V slot
variable {v u:V}{B:Equiv.Perm V}{E:Equiv.Perm ι}{m:Motion}{x:Site f}{M:ι→Hat (Aged V slot) R}{π:R.activities.Moves m.1 x}(h:Kin M v u B m x π E)
namespace Kin
set_option quotPrecheck false -- order issue
variable {s:Finset ι}
include h
lemma taller (p:Stacked (M:=M))(u:V) : Dep M u p.2.val.val ↔ Focused u (heap M (Sum.inr p)).s:=by
   let A:=p.snd.val.val; have hx:(heap M (Sum.inr p)).s.val=A.biUnion (fun i=> (M i).s.val):=rfl
   unfold Focused; change _ ↔ ((heap M (.inr p)).s.val.image Prod.fst) ⊆ _; rw [hx,biUnion_image];exact Finset.biUnion_subset.symm
lemma compass (i j:Stacked (M:=M))(ht:Dep M v i.2.val.val)(hp:j.2.val.val=i.2.val.val.image E)(he:j.1.val=π.ep i.1.val):
   let x:= heap M (Sum.inr i); let y:= heap M (Sum.inr j); y.s=drum (slot:=slot) B x.s∧ y.M=Leaf.route π x.M ∧ y.charge= scalar m x.charge:=by
   intro x y
   have hc {U:Type}[CommMonoid U](f₀:ι→U)(f:ι→U)(hv:∀ i'∈i.2.val.val,f₀ (E i')= f i') : ∏ i'∈j.2.val.val,f₀ i'=∏ i'∈i.2.val.val,f i':=by rw [hp,prod_image E.injective.injOn]; exact prod_congr rfl hv
   refine ⟨Subtype.ext ?_,?_,?_⟩
   · rw [drum, pares]; change j.2.val.val.biUnion _=(i.2.val.val.biUnion _).image _; rw [hp,image_biUnion,biUnion_image]; exact biUnion_congr rfl (fun i hi=> congr_arg Subtype.val (h.plot _ (ht _ hi)).1)
   · have hf(u v:Leaf R): u.turn=v.turn→ u.ingredient=v.ingredient→ u.weight=v.weight→u=v:=by cases u; cases v; intro ha hb hh; congr
     refine hf _ _ (congr_arg Wing.logKey he) (funext fun V=>?_) (hc (fun i=> (M i).M.weight) (fun i=> (M i).M.weight) fun i hi=> by rw [(h.plot _ (ht _ hi)).2.1];rfl)
     exact hc (fun i=>(M i).M.ingredient V) (fun i=>(M i).M.ingredient (pull m.1 _ V)) (fun i hi=> congr_arg (fun i:Leaf R=>i.ingredient V) (h.plot _ (ht _ hi)).2.1)
   refine (hc (fun i=> (M i).charge) (fun i=>scalar m (M i).charge) (fun i hi=> (h.plot _ (ht _ hi)).2.2)).trans ?_; unfold Motion.scalar; split_ifs; symm; exact star_prod ..; rfl
lemma piled : ∃ e:Equiv.Perm (Mound M), Kin (heap M) v u B m x π e:=by
   obtain ⟨e,hq,hp⟩:= h.covers; refine ⟨Equiv.sumCongr (Equiv.refl ι|>.trans E) e, h.here,fun i=> ?_,fun i hi=>?_⟩
   · cases i; exact h.cares _; next i=> exact (h.taller i v).symm.trans ((hq i).trans (h.taller (e i) u))
   cases i; exact h.plot _ hi
   next i=> have hl:=(h.taller i v).2 hi; exact h.compass _ (e i) hl (hp i hl).1 (hp i hl).2
end Kin
end YM.MergeProof.BatchRibbons
