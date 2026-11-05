import Mathlib.RingTheory.Nilpotent.Exp
import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Further.SHELL_BIRTH_49.Fusing.Coal
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker     Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories   Motion
local notation "P"=> Relation.ReflTransGen
lemma transported [DecidableEq I](E:Equiv.Perm I)(p:Finset I)(A B:I→I→Prop)
   (he:∀ i∈p,∀ j∈p, A i j↔ B (E i) (E j)) (hh:∀ i j,A i j→i∈p ∧ j∈p)(ht:∀ i j,B i j→ E.symm i∈p ∧ E.symm j∈p)(i j:I):P A i j↔ P B (E i) (E j):=by
    have he'(k l) (h:B k l):A (E.symm k) (E.symm l):=(he _ (ht k l h).1 _ (ht k l h).2).mpr (by simpa)
    constructor
    · intro h; induction h with
      | refl=> exact .refl
      | tail _ hx ih=> exact .tail ih ((he _ (hh _ _ hx).1 _ (hh _ _ hx).2).mp hx)
    have hf(k l)(h:P B k l): P A (E.symm k) (E.symm l):=by
       induction h with
       | refl => exact .refl
       | tail _ hx ih=> exact .tail ih (he' _ _ hx)
    intro h; simpa using hf _ _ h
open Collide
lemma mem_image_of_injective [DecidableEq J](r:I→J)(h:Injective r) {s:Finset I}{i:I}: r i∈s.image r↔ i∈s:=by constructor; intro he; obtain ⟨j,hp,hx⟩:=mem_image.mp he; exact h hx ▸ hp; exact mem_image_of_mem r
namespace Kilner
variable [DecidableEq I][DecidableEq J] (A:Kiln I V J) -- typo
lemma molecule (E:Equiv.Perm I) (e:Equiv.Perm V)(f:Equiv.Perm J) (p:Finset I)(h:∀ i∈p,A.mention (E i)=(A.mention i).image e ∧ A.wall (E i)=(A.wall i).image f ∧ (A.dirty (E i)↔ A.dirty i)): A.Mole p ↔ A.Mole (p.image E) :=by
   let q:= p.image E; let r:=Equiv.sumCongr e f
   have hi (i:I): E i∈q ↔ i∈p:= mem_image_of_injective _ E.injective
   have hx (i:I)(hh:i∈q): E.symm i∈p:= (hi _).mp (by simpa using hh)
   have hm i (hh:i∈p) j (ha:j∈p) : meets A.mention i j ↔ meets A.mention (E i) (E j):=by
       unfold meets; rw [(h i hh).1,(h j ha).1]; constructor
       · rintro ⟨z,hv,ht⟩; exact ⟨_,mem_image_of_mem _ hv,mem_image_of_mem _ ht⟩
       rintro ⟨z,hv,hk⟩; obtain ⟨w,hw,rfl⟩:=mem_image.mp hv; exact ⟨w,hw,(mem_image_of_injective _ e.injective).1 hk⟩
   have hz : ∀ i j,link A.mention p i j↔ link A.mention q (E i) (E j):=transported E p _ _ (fun i h1 j h2=> (and_congr (hi i|>.symm) (and_congr (hi j|>.symm) (hm _ h1 _ h2)))) (fun _ _ h=>⟨h.1,h.2.1⟩) (fun _ _ h=>⟨hx _ h.1,hx _ h.2.1⟩)
   have hv (i) : A.Hot p i↔ A.Hot q (E i):=by
       constructor
       · rintro ⟨j,hj,hk,hH⟩; exact ⟨E j,(hi j).2 hj,(h j hj).2.2.mpr hk,(hz i j).mp hH⟩
       rintro ⟨j,hj,hk,hH⟩; obtain ⟨w,hw,rfl⟩:=mem_image.mp hj; exact ⟨w,hw,(h w hw).2.2.mp hk,(hz i w).2 hH⟩
   have hr i (hi:i∈p) (z:V⊕J): z∈A.fuel p i↔ r z∈ A.fuel q (E i):= by
       cases z
       next v=> change Sum.inl _ ∈ _↔ Sum.inl (e v)∈ _; rw [A.fuel_left,A.fuel_left,(h i hi).1]; exact (mem_image_of_injective _ e.injective).symm
       next v=> change Sum.inr _ ∈ _↔ Sum.inr (f v)∈ _; rw [A.fuel_right,A.fuel_right,hv,(h i hi).2.1,mem_image_of_injective _ f.injective]
   have hh (i)(hi:i∈p)(j)(hj:j∈p):meets (A.fuel p) i j↔ meets (A.fuel q) (E i) (E j):=by
       constructor
       · rintro ⟨v,hv,hp⟩; exact ⟨r v,(hr i hi v).1 hv,(hr j hj v).1 hp⟩
       rintro ⟨v,ht,hp⟩; obtain ⟨v,rfl⟩:= r.surjective v; exact ⟨v,(hr i hi v).2 ht,(hr j hj v).2 hp⟩
   have hs := transported E p (bond (A.fuel p) p) (bond (A.fuel q) q) (fun i h1 j h2=> and_congr (hi i|>.symm) (and_congr (hi j|>.symm) (hh i h1 j h2))) (fun _ _ h=>⟨h.1,h.2.1⟩) (fun _ _ h=>⟨hx _ h.1,hx _ h.2.1⟩)
   constructor
   · intro g; refine ⟨image_nonempty.mpr g.1, fun i hh j hh'=>?_⟩; obtain ⟨b,hb,rfl⟩:=mem_image.mp hh; obtain ⟨j,hj,rfl⟩:=mem_image.mp hh'; exact (hs b j).mp (g.2 _ hb _ hj)
   intro g; exact ⟨image_nonempty.mp g.1, fun i hh j hv=> (hs _ _).mpr (g.2 (E i) ((hi i).2 hh) (E j) ((hi j).2 hv))⟩
end Kilner
end YM.MergeProof.Ribbons
