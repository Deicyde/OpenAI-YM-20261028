import YM.MergeProof.North.Muscat
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Wiring
import YM.MultipleContact.Bunch.Frost
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme
import YM.MultipleContact.Bunch.Botan
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Nigella
import YM.MultipleContact.Bunch.Buoy
import YM.MultipleContact.Bunch.Gild
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Pond
import YM.MultipleContact.Bunch.Shan
import YM.MultipleContact.Bunch.SkyFall
import YM.MultipleContact.Bunch.Quark
import YM.MultipleContact.Bunch.Menu
import YM.MultipleContact.Bunch.Wraith
import YM.MultipleContact.Bunch.Thumb
import YM.MultipleContact.Bunch.Arbor
import YM.MultipleContact.Bunch.Platform
import YM.MultipleContact.Bunch.Islands
import YM.MultipleContact.Bunch.Quiet
import YM.MultipleContact.Bunch.Price
import YM.MultipleContact.Bunch.Antique
import YM.MultipleContact.Bunch.Apiary
import YM.MultipleContact.Bunch.Stable
import YM.MultipleContact.Bunch.Belvedere
import YM.MultipleContact.Bunch.Thunder
import YM.MultipleContact.Bunch.Muscat

/- generalized from YM.MergeProof.North.Fram to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:History G) {N m p k:ℕ}(δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,Name V slot→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:ℕ→slot→ℝ)(B:V→Equiv.Perm V)
set_option quotPrecheck false
local notation "Ξ"=> (Aged V slot)
local notation "P'"=> H.levels.budget
local notation "ω"=> (fun i (j:Name V slot)=> w i j.2)
local notation "R"=> H.rep N p
local notation "Q"=> R N
variable {l:Name V slot→ℂ}(σ χ:ℕ→ℝ){μ j:ℕ}
    {S:∀ m:ℕ,m≤N→ Config G (H.S.side m p)→Poly (Aged V slot)}
    (h:H.Selected) (hr:Thor (slot:=slot) H δ r D σ χ μ)(ht':μ≤k)(hQ: Migrating H k p N E)
    (hΔ: ∀ m:ℕ, k ≤ m→∀ hm:m<N, S m hm.le=(H.levels.clock.op m p).push ((H.rep N p (m+1)).beta) (S (m+1) hm))
    (hp:∀ m:ℕ,k ≤ m→∀ hm:m≤N,Integrable (S m hm) (prior G _))
    (ht:Matchup H r δ p j k o (fun i (j:Name V slot)=> w i j.2) (Aged V slot)) (hO:∀ m:ℕ, k ≤ m→m≤j→∀ i,i≠v→∀ b:slot,o m (i,b)=affine (P i).1 (E m i) (o m (v,b)))
local notation "W"=> (fun i (j:Name V slot)=>δ i*w (i+1) j.2)
variable (x:ℕ→ℝ)
include h hr ht' hQ hΔ hp ht hO
local notation "d'"=> (fun i (b:slot)=> (1:ℝ)/(2*w i b))
local notation "X"=> Sprout H E o P v w B (S:=S) (l:=l)
variable (hN:j≤N)(hY:∀ m:ℕ,k ≤ m→∀ hi:m<j, MergeProof.Float.Runs (D N p m (hi.trans_le hN)) (H.levels.clock.op m p) (x m)) (hX:∀ m:ℕ,k ≤ m→ m<j → 0 ≤ x m)(hf:∀ m:ℕ,k ≤ m→m<j→∀ i,x m*w m i ≤ w (m+1) i)
include hY hN hX hf
lemma framing (hk:k<j)(F K t) (W':slot→ℝ)(hU:Arc (R j) F K (S j hN) v P (E j) B (o j) (fun i=>W' i.2) ((P' j).supportExponent+1/2) ((P' j).supportExponent+1) 1 (χ j) t l) (he:∀ i,i≠v→∀ b:slot,l (i,b)=scalar (P i) (l (v,b))) (hξ:χ j≤1)(hc:∀ i,8*w j i ≤ W' i) (hD:Arsenal (R j)) : ∃ g L, Arc (R k) g L (S k (hk.le.trans hN)) v P (E k) B (o k) (W k) ((P' k).supportExponent+1/2) ((P' k).supportExponent+1) 1 (χ k) (δ k) l:=by
    have hP:= h.represents N p j hN
    have hw(i):0 < w j i:=ht.pos j hk.le le_rfl (v,i); have hw'(i):0 < W' i:=lt_of_lt_of_le (mul_pos (by norm_num) (hw i)) (hc i)
    have hT : X j hN:=by
       rw [← hP.vac] at hU; obtain ⟨g,L,hg,hb,hF⟩:= stem hD hU hP.good.labels he (fun i=> hw' _) hξ (by norm_num) zero_le_one (fun U=>(Tour.bright H h N p j hN U).ne'); refine ⟨g,L,fun i=>?_ ,fun i=>(hg i).1,hb,?_⟩
       · apply (hg (v,i)).2.more; change 2*(1/W' i)+2*(χ j/W' i) ≤ 1/(2*w j i)
         calc 2*(1/W' i)+2*(χ j/W' i) ≤ 2*(1/W' i)+2*(1/W' i):= add_le_add le_rfl (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hξ (hw' i).le) zero_le_two)
              _ = 4/W' i:=by ring
              _ ≤ 1/(2*w j i) := (div_le_div_iff₀ (hw' i) (mul_pos (by norm_num) (hw i))).mpr (by linarith only [hc i])
       rw [← hP.vac]; exact hF.prune (fun i=> hw' _) (fun i=>hw _) (slighter (fun i=>hw' i.2) (ht.pos j hk.le le_rfl) (w:=1) (fun i=>by have he:= hc i.2; change w j i.2 ≤ 1*W' i.2; linarith only [he,hw i.2]) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num)
    have hF(m)(hm:k ≤ m)(hj:m≤j): X m (hj.trans hN):=by
       induction hj using Nat.decreasingInduction with
       | self=> exact hT
       | of_succ i hi IH=> obtain ⟨g,L,H,x⟩:=musky H δ r D E o P v w B σ χ h hr ht' hQ hΔ hp ht hO x hN hY hX hf hm hi (IH (hm.trans i.le_succ)); exact x
    obtain ⟨g,L,H,-⟩:= musky H δ r D E o P v w B σ χ h hr ht' hQ hΔ hp ht hO x hN hY hX hf le_rfl hk (hF _ k.le_succ hk); exact ⟨g,L,H⟩
end
end YM.MergeProof.BatchRibbons
