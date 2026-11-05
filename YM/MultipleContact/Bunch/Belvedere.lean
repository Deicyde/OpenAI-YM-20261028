import YM.MergeProof.North.Arbor
import YM.MergeProof.North.Stable
import YM.MergeProof.North.Tan
import YM.MergeProof.South.Admit
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

/- generalized from YM.MergeProof.North.Belvedere to arbitrary arity -/


set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:RG.History G) {N m p:ℕ}
local notation "f"=> H.S.side (m+1) p
local notation "c"=> H.S.side m p
local notation "X0"=> H.rep N p m
local notation "X1"=> H.rep N p (m+1)
local notation "Z"=> H.levels.clock.op m p
local notation "P0"=> (H.levels.budget m)
local notation "P1"=> (H.levels.budget (m+1))
variable {x d t u w :ℝ} {I: Name V slot→ℝ} {J:Name V slot→ℝ}
    {θ:Config G (H.S.side (m+1) p)→Poly (Aged V slot)} {o:Name V slot→Site (H.S.side (m+1) p)}
    {F: Name V slot→ Config G (H.S.side (m+1) p)→ℂ} {L: Name V slot→ℕ→ Config G (H.S.side (m+1) p)→ℂ}
    {D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (C:ℕ→ℕ)
    {P:V→Motion}{E:V→Site (H.S.side m p)}{v:V}{B:V→Equiv.Perm V}
    {l:Name V slot→ℂ}
set_option quotPrecheck false
local notation "Ω"=> (Z).ratio.parent ∘ o
local notation "ρ"=> (Z).push (X1).beta θ
local notation "T"=> fun i=> (Z).ratio.embed (E i)
local notation "kp"=> fun i=> profile (X1).activities (L i)
variable {A:slot→ℝ}
lemma Serves.sold {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side}{R:RG.Rep G n}{v:V}{x t:ℝ}{o:Name V slot→Site n}{P E b i k a y} (h:BatchRibbons.Serves R a k y v P E b o i x t): Served R a k y o i x t:=by obtain ⟨H,Z',hT,hk,hv,_,r⟩:=h; exact ⟨H,Z',hT,hk,hv,r⟩
lemma chimes_parent (hC:∀ i,i≠v → ∀ j:slot,o (i,j)=affine (P i).1 ((Z).ratio.embed (E i)) (o (v,j))) {K:Name V slot→ Res G (H.S.side m p)} (ht:May v P (fun i=> (Z).ratio.embed (E i)) B F (kp) l)(hp:∀ i,i≠v→∀ j:slot,K (i,j)=floatUp (P i) (E i) (K (v,j))): chimes v P E B o (Ω) F (kp) K l Z:=by
    intro i hi; have he:=ht i hi
    refine ⟨he.1,fun j=> ⟨hC i hi j,?_,(he.2 j).1,(he.2 j).2.1,hp i hi j,(he.2 j).2.2⟩⟩
    change (Z).ratio.parent (o (i,j)) = _; rw [hC i hi j]; exact Push.Local.parent_affine _ (H.S.block_odd _) _ _ _

variable (h:H.Selected)(hm:m<N)(hD:Duty H C m d t u)(ht:Volant (H.levels.clock.op m p) D (C m) ((H.levels.budget (m+1)).supportExponent-4) t ((H.levels.budget m).supportExponent+1/2) ((H.levels.budget m).supportExponent+1) 1 u)(hR:Unites (slot:=slot) (H.levels.clock.op m p) D (C m) ((H.levels.budget (m+1)).supportExponent-4) t ((H.levels.budget m).supportExponent+1/2) ((H.levels.budget m).supportExponent+1) 1 u)
    (hI:∀ i,0<I i)(hs:Serves (H.rep N p (m+1)) F (fun i=>profile (H.rep N p (m+1)).activities (L i)) θ v P (fun i=> (H.levels.clock.op m p).ratio.embed (E i)) B o I w 1)(hX:(H.levels.budget (m+1)).supportExponent-4≤w)(hO:Occupancy o (C m))(hO':Occupancy ((H.levels.clock.op m p).ratio.parent ∘ o) (C m)) (hT:∀ i,i≠v→∀ j:slot,I (i,j)=I (v,j))
    (hC:∀ i,i≠v → ∀ j:slot,o (i,j)=affine (P i).1 ((H.levels.clock.op m p).ratio.embed (E i)) (o (v,j)))
    (hp:May v P (fun i=> (H.levels.clock.op m p).ratio.embed (E i)) B F (fun i=> profile (H.rep N p (m+1)).activities (L i)) l)(hK:∀ i,Dominated (L i))
    (hB:∀ j:slot,let i: Name V slot:=(v,j); Blade (H.rep N p (m+1)) (o i) (F i) (profile (H.rep N p (m+1)).activities (L i)) (l i) (A j))
    (hc:∀ i: Name V slot,2* I i * A i.2≤1)(hx:MergeProof.Float.Runs D (H.levels.clock.op m p) x)(hx':0≤x)
include h hm hD ht hR hI hs hX hO hO' hT hC hp hK hB hc hx hx'
set_option maxHeartbeats 550000 in
lemma flaring (hθ: Integrable θ (prior G _)):∃ (g:Name V slot→ Config G c→ℂ)(k:Name V slot→ℕ→ Config G c→ℂ), (∀ i,Dominated (k i))∧ (∀ i U,(ρ U).part ((Aged V slot).fire i)=coin X0 (g i) (k i) U)∧ May v P E B g (fun i=>profile (X0).activities (k i)) l ∧ (∀ j:slot,Blade X0 (Ω (v,j)) (g (v,j)) (profile (X0).activities (k (v,j))) (l (v,j)) (x*A j)) ∧ Arc (X0) g k (ρ) v P E B (Ω) (fun i=>d*I i) ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u d l:=by
    have hA := h.represents N p (m+1) hm; have hA' := h.represents N p m hm.le; have hkr:= H.levels.transition_mass m p (X1).beta; have hv:= (h.steps N p m hm).1.symm
    choose W k hh hz hP he using fun i=> Float.slosh (hB i) hA.good (hK (v,i)) hx hx' hA'.good.labels hv hkr
    let e(i:V):= (hA'.good.labels.moves (P i).1 (E i)).some
    let g(i:Name V slot) := if i.1=v then W i.2 else stepUp (P i.1) (E i.1) (W i.2)
    let k'(i:Name V slot) := if i.1=v then k i.2 else (fun j=>stepUp (P i.1) (E i.1) (k i.2 ((e i.1).kp.symm j)))
    have hy(i:Name V slot): Dominated (k' i):=by unfold k'; split; exact hz i.2; exact conduits _ _ _ (hz i.2) (e i.1)
    have hm':May v P E B g (fun i=>profile (X0).activities (k' i)) l:=by
        intro i hi; have he:=hp i hi; refine ⟨he.1,fun j=> ?_⟩
        refine ⟨by simp [g,hi], ?_,(he.2 j).2.2⟩; simp only [k',if_pos rfl,if_neg hi]; apply roam _ _ (e i); intro i U;simp
    have hsi (i:Name V slot):(fun U=>(θ U).part ((Aged V slot).fire i))= coin X1 (F i) (L i):=by
      funext U; let Ls i:= profile (X1).activities (L i); have HH:Served X1 F (fun i=>profile (X1).activities (L i)) θ o I w 1:= hs.sold; exact HH.relay (J:=Aged V slot) hK hA.good.labels U|>.1 i
    have hs' (i:Name V slot):(ρ · |>.part ((Aged V slot).fire i))=(Z).push (X1).beta (coin (X1) (F i) (L i)):= (push_get hkr hθ _).trans (by rw [hsi i])
    have hfl(i: Name V slot)(U:Config G (H.S.side m p)): (ρ U).part ((Aged V slot).fire i)=coin X0 (g i) (k' i) U:=by
      rcases i with ⟨i,j⟩; apply (congr_fun (hs' (i,j)) U).trans
      by_cases hi:i=v
      · subst i; rw [show g (v,j)=W j from if_pos rfl,show k' (v,j)=k j from if_pos rfl]; exact congr_fun (he j) U
      have h₁:= Float.opals (P i) H h hm (T i) (F (v,j)) (hA.good.labels.moves _ _).some (hK (v,j)) (hK (i,j)) ((hp i hi).2 j).2.1; rw [← ((hp i hi).2 j).1] at h₁
      have h₂:= Float.opals (P i) H h hm.le (E i) (g (v,j)) (e i) (hy (v,j)) (hy (i,j)) ((hm' i hi).2 j).2.1; rw [← ((hm' i hi).2 j).1] at h₂
      change (Z).push (X1).beta (coin (X1) (F (i,j)) (L (i,j))) U=_; rw [h₁,h₂]
      have hh:= unison (P i) H m N p 0 (E i) _ (Float.spill_in (hB j) hA.good (hK (v,j)))
      simp only [blast,pow_zero,one_smul] at hh; change (Z).push _ _=_ at hh; rw [hh, show g (v,j)=W j from if_pos rfl, show k' (v,j)=k j from if_pos rfl, ← he j]

    have Hq (j:slot): Blade X0 (Ω (v,j)) (g (v,j)) (profile (X0).activities (k' (v,j))) (l (v,j)) (x*A j):=by rw [show g (v,j)=W j from if_pos rfl,show k' (v,j)=k j from if_pos rfl]; exact hh j
    have HJ(i:slot):∃ z:Set Wing,z.Finite∧ Tale z (o (v,i)) (Ω (v,i)) 1 (F (v,i)) (profile (X1).activities (L (v,i))) (profile (X0).activities (k' (v,i))) (l (v,i)) (A i) 0 D:=by
       rw [show k' (v,i)= k i from if_pos rfl]
       exact hP i
    have hCH: chimes v P E B o (Ω) F (kp) (fun i=>profile (X0).activities (k' i)) l (Z):= chimes_parent H hC hp (fun i he j=>((hm' i he).2 j).2.1)
    have hf : Arc (X0) g k' (ρ) v P E B (Ω) (fun i=>d*I i) ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u d l:=by
      apply freshArc H N m p C h hm hD ht hR hI hs hX hO hO' hT (s:=A) (r:=0) hc (by simp) (fun j=>HJ j) hCH (fun i=>hA.good.labels.moves (P i).1 (T i))
    exact ⟨g,k',hy,hfl,hm',Hq,hf⟩
end YM.MergeProof.BatchRibbons
