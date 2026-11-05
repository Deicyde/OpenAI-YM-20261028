import YM.MergeProof.North.River
import YM.OPE.Grouping.Fibers
import YM.OPE.Grouping.Ebb
import YM.OPE.Grouping.Stator

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/River.lean
to a projection along fibers. The Deck prices a nonempty finite number of children
(not necessarily common across grouping regions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀][DecidableEq S₀] {Δ : Fibers S₀ V}
namespace Salt
variable (Z:Salt V S₀ Δ G n)(t:ℝ)(U:Config G n)(h:Z.Breeze t)
local notation "P"=> Z.vessel t
include h
lemma fieldSpend (i:Box n) : cram (P).spill (fun j=> Poly.send ((P).mode_ (.inr j)) ((P).toll (.inr j) U)) i= Z.river i U:=by
   ext p; unfold cram; rw [Poly.share Summable.of_finite,tsum_fintype]; let A:={a:Z.Brook//(P).spill a=i}
   change ∑ a:A,(Poly.send a.val.val.2 ((Z.river a.val.val.1 U).part a.val.val.2)).part p=(Z.river i U).part p
   by_cases hh : (Z.river i U).part p=0
   · rw [hh]; refine sum_eq_zero fun a _=>?_ ; rw [Poly.part_send]; split; next he=> rw [show a.val.val.1=_ from a.property,← he,hh]
     next=> rfl
   have ht:= (h.permits i).permits U (fun he=>hh (by rw [he,Poly.part_nil])) -- infer
   let v : Z.Brook:= ⟨(i,p),ht.2, (h.permits i).toBorne.place _ _ hh⟩ -- typo
   let b:A:= ⟨v,rfl⟩
   rw [sum_eq_single b]; exact (Poly.part_send ..).trans (if_pos rfl)
   · intro x _ hx; rw [Poly.part_send]; exact if_neg (fun he=> hx (Subtype.ext (Subtype.ext (Prod.ext x.property he.symm))))
   simp
lemma sugar : ∑ j:Z.Seed,Poly.send ((P).mode_ (.inl j)) ((P).toll (.inl j) U)= Mach (Bud S₀) Z.pepper+ ∑ i, Z.air i U:=by
   let f b i:= Poly.send (Z.marker b) (Z.bud t U (b,i))
   have hh b : ∑ i:Bool,f b i=Poly.send (Z.marker b) (Z.syrup b U):=by
     unfold f; rw [Fintype.sum_bool]; unfold bud; by_cases he: Healthy t (Z.kiln (Z.leaf b) (Z.marker b)) U<;> simp [he]
   change ∑ i:Z.Lawn×Bool, f i.1 i.2=_; rw [Fintype.sum_prod_type]; simp_rw [hh, Fintype.sum_sum_type]
   refine congr_arg (Mach _ Z.pepper+·) ?_
   let g i:=Poly.send (Z.marker (.inr i)) (Z.syrup (.inr i) U)
   have he := (border (fun i:Z.Turf=>i.val.1) (p:=g) Summable.of_finite).tsum_eq; rw [tsum_fintype,tsum_fintype] at he
   change ∑ j:Z.Turf,g j=_; rw [← show ∑ l:Support n,∑' i:{i:Z.Turf//i.val.1=l},g i.val=∑ i:Z.Turf,g i from he] -- notation lhs change
   refine sum_congr rfl fun i _=>?_ ; ext p; rw [Poly.share Summable.of_finite,tsum_fintype]; let A:={j:Z.Turf//j.val.1=i}
   change ∑ a:A,(Poly.send a.val.val.2 ((Z.air a.val.val.1 U).part a.val.val.2)).part p=(Z.air i U).part p
   by_cases hh : (Z.air i U).part p=0
   · rw [hh]; refine sum_eq_zero fun a _=>?_ ; rw [Poly.part_send]; split; next he=> rw [a.property,← he,hh]
     next=> rfl
   have hz : p.val.Nonempty:= nonempty_iff_ne_empty.mpr (fun he=> hh (by rw [show p=(Bud S₀).quiet from Subtype.ext he]; exact (h.home i).sil _))
   let a : A:= ⟨⟨(i,p),hz, (h.home i).toBorne.place _ _ hh⟩,rfl⟩
   rw [sum_eq_single a]; exact (Poly.part_send ..).trans (if_pos rfl)
   · intro x _ hx; rw [Poly.part_send]; exact if_neg (fun he=> hx (Subtype.ext (Subtype.ext (Prod.ext x.property he.symm))))
   simp

def mount:= (P).sky t
def soil:= (P).clay t
lemma yields : Fibers.reap Δ (Poly.pass (Mach (Bud S₀) Z.pepper+ ∑ i,Z.air i U)*field (fun i=>Z.river i U) (flags t U))=Poly.pass (∑ i,Z.mount t i U)*field (fun i=>Z.soil t i U) (flags t U):=by
    have he:=(P).startOld t U (Z.wet _ h); rw [Z.sugar _ U h, show (cram (P).spill (fun i=> Poly.send ((P).mode_ (.inr i)) ((P).toll (.inr i) U))) = _ from funext (Z.fieldSpend _ U h)] at he; exact he
lemma taxed (i : Box n) : (Z.soil t i U).part (Bud V).quiet=(Z.river i U).part (Bud S₀).quiet:=
   (P).sober t U (Z.wet _ h) i|>.trans (congr_arg (fun p:Poly (Bud S₀)=> p.part (Bud S₀).quiet) (Z.fieldSpend _ U h _))
end Salt
end YM.MergeProof.Ribbons.Fibers
