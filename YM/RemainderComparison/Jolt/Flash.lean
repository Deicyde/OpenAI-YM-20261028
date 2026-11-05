import YM.RemainderComparison.Jolt.Pure
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Band
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Jolt
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes
open Flues ProjectorNext.Equivariance
variable {G:Gauge}{c:Side}{ι κ:Type}{α:Type*}
variable (H:Yard ι α G c) (S:Scone ι α G c)(u:Set ι)(P:BudgetPoint)
open Flues PhysicalNext.Repeat.Turn
local notation "C" => fireplace H S
variable (F:ℕ≃ (fireplace H S).Pellet)
local notation "D"=> Flues.flash H S P u F

lemma stars (i:ℕ): Jolt.phase D u i↔ ∀ j∈ (F i).val, Verse.load u (Flues.rune H S j)=0:=by
   let f:=Flues.rune H S
   change Verse.load u (∑ j∈(F i).val,f j) = 0 ↔ _
   have hp (v:Finset Ovens.Label) : Verse.load u (∑ j∈v,f j)=0 ↔ ∀ j∈v,Verse.load u (f j)=0:=by
      induction v using Finset.induction_on with
      | empty=>simp [Verse.load]
      | @insert i s h ih=> rw [sum_insert h, show ∀ p q: Multiset ι, Verse.load u (p+q)=Verse.load u p+Verse.load u q from fun p q=> by simp [Verse.load],Nat.add_eq_zero_iff,ih]; simp
   exact hp _

variable {s:Signed}{b:Site c}(p q:Equiv.Perm ℕ)
variable (hp:∀ i, (phase H u (p i)↔phase H u i)∧ H.more (p i)=Jolt.spring (H.more i) (s,b)∧ (phase H u i →∀ (V:Config G c) a,H.glow a (p i) V= H.glow a i (pull s b V)))
variable (hq:∀ i,(dawn S u (q i)↔dawn S u i)∧ S.leg (q i)=(S.leg i).image (affine s b)∧ (dawn S u i → ∀ (V:Config G c) a,S.glow a (q i) V=S.glow a i (pull s b V)))
include hp hq
local notation "v"=> Equiv.sumCongr p q
local notation "e"=> StepData.sendSites s b
lemma colony i: ∀ j : Site c,j∈ (C).patch i ↔ StepData.sendSites s b j∈ (C).patch ((Equiv.sumCongr p q) i):= by
   apply (display _ _ _).mp; rcases i with i|i; exact congr_arg ForcedAddress.support ((hp i).2.1)
   exact (hq i).2.1

def spinP : Equiv.Perm (C|>.Pellet):=
    Equiv.subtypeEquiv (Equiv.sumCongr p q).finsetCongr fun i=> by
       let f: Equiv.Perm Ovens.Label:= Equiv.sumCongr p q; let g:= f.finsetCongr i
       have ht' : ∀ i',i'∈lefts i↔p i' ∈ lefts g:=fun _=> (Finset.mem_toLeft.trans (((Turn.given f _ g).1 rfl _).trans Finset.mem_toLeft.symm))
       unfold Pipes.contains; refine and_congr ?_ (and_congr (Turn.seam f (StepData.sendSites s b) (colony H S u p q hp hq) (show ∀ i',i'∈i↔_ from (Turn.given f _ _).1 rfl)) ?_)
       · rw [show lefts (Equiv.finsetCongr _ i)= _ from (Turn.given p (lefts i) _).mpr ht']; exact Finset.map_nonempty.symm
       apply Turn.gaps (Y:=fun i=>(H.more i).support) (X:=fun i=>(H.more i).support) (A:=lefts i) («D»:=lefts g) p (StepData.sendSites s b) (fun i=> colony H S u p q hp hq (.inl i)) ht'
local notation "Δ"=> Jolt.spinP H S u p q hp hq
def glide : Equiv.Perm ℕ:= (F.trans (spinP H S u p q hp hq)).trans F.symm
local notation "ζ" => glide H S u F p q hp hq
lemma horizons i : (Δ) (F i)=F (ζ i):= (F.apply_symm_apply _).symm
lemma torque i j: j∈(F i).val ↔ v j∈ (F (ζ i)).val:=by rw [← horizons]; exact ((Turn.given v _ _).1 rfl j)
lemma years (i:ℕ): phase D u (ζ i) ↔ phase D u i:=by
   rw [stars H S,stars H S]; conv_lhs=> rw [← (v).forall_congr_right]
   apply forall_congr'; intro j; apply imp_congr (torque H S u F p q hp hq i j).symm; rcases j with j|j
   · exact (hp j).1
   exact (hq j).1
lemma whirlF (i:ℕ): (D).more (ζ i)=Jolt.spring ((D).more i) (s,b):=by
   let f:= v
   have hh := torque H S u F p q hp hq i; have ht:= colony H S u p q hp hq
   have hv : ∀ j, j∈lefts (F i).val↔ p j∈ lefts (F (ζ i)).val:=fun j=> Finset.mem_toLeft.trans ((hh _).trans Finset.mem_toLeft.symm)
   have h i V : ((C).kernel (p i)).eligible P.threshold V↔ ((C).kernel i).eligible P.threshold (pull s b V):=by
       rw [show (C).kernel (p i)= _ from (hp i).2.1]; exact Jolt.eligible ..
   refine Eq.symm ((Jolt.valids ..).2 ⟨Turn.gains f e ht hh,?_ ,fun V=> ?_⟩)
   · exact Turn.gains (Y:=fun i=>(H.more i).inventory) (X:=fun i=>(H.more i).inventory) p e (fun i=> (Turn.display e _ _).1 (congr_arg ForcedAddress.inventory ((hp i).2.1))) hv
   change (∀ j∈ lefts (F (ζ i)).val,((C).kernel j).eligible P.threshold V)↔ _
   conv_lhs=> rw [← p.forall_congr_right]
   exact forall_congr' fun j=> imp_congr (hv j).symm (h j V)
lemma spins (i:ℕ)(he:phase D u i) (V:Config G c) (a:α) : (D).glow a (ζ i) V=(D).glow a i (pull s b V):=by
   unfold Flues.flash; dsimp only; refine if_congr ?_ ?_ rfl
   · rw [show addr F P (ζ i)= _ from whirlF H S u P F p q hp hq i]; exact eligible ..
   symm; apply Turn.values v _ _ (torque H S u F p q hp hq i); intro j hj; have he:= (stars ..).mp he j hj; rcases j with j|j
   · exact ((hp j).2.2 he V a).symm
   have hv: dawn S u (q j):= (hq j).1.mpr he
   change Scone.tinct S u a j (pull s b V)= Scone.tinct S u a (q j) V; unfold Scone.tinct; rw [if_pos (show Verse.load u (S.glyph j)=0 from he), if_pos (show Verse.load u _=0 from hv),(hq j).2.2 he V a]
omit hp hq
lemma gathers (h:Orbit H u)(he:Whirls S u):Orbit D u:=by
   constructor
   · intro i hx a b; ext U; unfold Flues.flash; dsimp only; split; next=>
       apply prod_congr rfl; intro j hj; have hz:= (stars ..).1 hx j hj; rcases j with j|j
       · exact congr_fun (h.quiet _ hz ..) _
       change Scone.tinct S u a j U=Scone.tinct S u b j U; unfold Scone.tinct; rw [he.quiet j hz a b]
     rfl
   intro s b; obtain ⟨p,hp⟩:=h.spins s b; obtain ⟨q,hq⟩:=he.spins s b
   exact ⟨glide H S u F p q hp hq,fun i => ⟨years H S u P F p q hp hq i,whirlF H S u P F p q hp hq i,spins H S u P F p q hp hq i⟩⟩

end YM.RemainderComparison.Jolt
