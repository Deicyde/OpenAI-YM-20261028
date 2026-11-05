import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.Extra.SOURCE_HISTORIES.Clusters


/- generalized from YM.MergeProof.North.Focal to arbitrary arity -/

/-!
# Borel merger. Complete pairing, no alternates

We use `Further.Shell...` slab combinatorics but a separate projection:
PAIR product only, not minting a counter on erasure of any AB. UsesFinal only.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbon
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Finset Function Marker Extra.Trajectories 
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [Fintype V]
abbrev Name (V slot :Type*):= V × slot
abbrev Aged (V slot :Type*)[Fintype slot][DecidableEq slot][DecidableEq V][Fintype V]:= Stock.census (Name V slot)
abbrev Bud (V : Type*)[DecidableEq V][Fintype V]:= Stock.census V

def span (i:(Aged V slot).Mode) : (Bud V).Mode:= ⟨i.val.image Prod.fst,mem_univ _⟩
def plena (b:(Bud V).Mode) : (Aged V slot).Mode:=⟨b.val×ˢuniv,mem_univ _⟩
def Pays (i:(Aged V slot).Mode) := i=plena (span i)
lemma spans (i:(Aged V slot).Mode)(j) : j∈(span i).val ↔ ∃ k, (j,k)∈ i.val:=by simp [span,eq_comm]
lemma reband (b:(Bud V).Mode) : span (plena (slot:=slot) b)=b:=by
   apply Subtype.ext; ext i; rw [spans]; simp [plena]
lemma worth_iff (i:(Aged V slot).Mode) : Pays i↔ ∀ j∈ (span i).val,∀ k, (j,k)∈i.val:=by
   constructor; intro h j hj k; change i=_ at h; nth_rw 1 [h]; simpa [plena]
   intro h; apply Subtype.ext; ext ⟨j,k⟩; refine ⟨fun h=> mem_product.mpr ⟨(spans i j).2 ⟨k,h⟩,mem_univ k⟩,fun hh=> h j (mem_product.mp hh).1 k⟩

def reap : Poly (Aged V slot)→L[ℂ] Poly (Bud V):= LinearMap.toContinuousLinearMap ({
    toFun:=fun p=>Poly.inject fun s=> p.part (plena s)
    map_add':= fun _ _ => Poly.ext fun _=> rfl
    map_smul':= fun _ _ => Poly.ext fun _=> rfl } : Poly (Aged V slot) →ₗ[ℂ] Poly (Bud V))
lemma harvest (i:(Aged V slot).Mode)(a:ℂ) : reap (Poly.send i a)=if Pays i then Poly.send (span i) a else 0:=by
   ext1 s; change (Poly.send i a).part (plena s)=_; rw [Poly.part_send]; split
   next h=> rw [← h,reband, if_pos (show Pays (plena s) from (by unfold Pays; rw [reband])),Poly.part_send,if_pos rfl]
   next h=> split
            next he=> rw [Poly.part_send, if_neg (fun (ht:s=span i)=> h (ht.symm ▸ he.symm))]
            rfl
lemma combines {q:I→(Aged V slot).Mode} {s:Finset I}(h:Fits q s): (span (unionTag _ _ h)).val=s.biUnion (fun i=>(span (q i)).val):=by
   ext; simp only [spans,unionTag,mem_biUnion]; tauto
lemma afford (i:(Aged V slot).Mode)(h:Pays i)(w:Name V slot→ℝ)(u:V→ℝ)(ht:∀ i, u i=∏ k:slot,w (i,k)): Poly.toll w i=Poly.toll u (span i):=by
   nth_rw 1 [show i=plena (span i) from h]; unfold Poly.toll plena; rw [prod_product]; exact prod_congr rfl fun j _=>by simpa [ht,mul_comm]
lemma recomp {q:I→(Aged V slot).Mode}{s:Finset I}(h:∀ i∈s,Pays (q i))(A:I→ℂ): reap (∏ i∈s,Poly.send (q i) (A i))=∏ i∈s,Poly.send (span (q i)) (A i):=by
   by_cases hv:Fits q s
   · have hp:Fits (fun i=>span (q i)) s:=by
        refine ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hk he=>?_,mem_univ _⟩
        exact disjoint_left.mp (hv.1 hi hj hz) ((worth_iff _).mp (h _ hi) _ hk (default:slot)) ((worth_iff _).mp (h _ hj) _ he (default:slot))
     have hx:Pays (unionTag _ _ hv):=by
        rw [worth_iff,combines]; intro i hi j; obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨k,hk,(worth_iff _).mp (h k hk) i hz j⟩
     rw [tagged_prod _ s hv,harvest,if_pos hx,tagged_prod _ _ hp]; exact congr_arg (fun p=> Poly.send p _) (Subtype.ext (combines hv))
   rw [show (∏ i∈s,Poly.send (q i) (A i))=0 from Classical.byContradiction (fun h=> hv (fits_of_tagged_prod _ h)),map_zero]; symm; by_contra hh
   have hp:= fits_of_tagged_prod (fun i=> span (q i)) hh; exact hv ⟨fun i hi j hj hz=> disjoint_left.mpr fun ⟨x,k⟩ hx he=> disjoint_left.mp (hp.1 hi hj hz) ((spans (q i) x).2 ⟨k,hx⟩) ((spans (q j) x).2 ⟨k,he⟩),mem_univ _⟩
end YM.MergeProof.BatchRibbon
