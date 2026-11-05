import YM.MergeProof.North.Calm
import YM.MergeProof.North.River
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
import YM.MultipleContact.Bunch.Calm
import YM.MultipleContact.Bunch.Ebb
import YM.MultipleContact.Bunch.River

/- generalized from YM.MergeProof.North.Liturgy to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons.Twin
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Finset Function Marker Extra.Trajectories Accent BatchRibbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
open Extra.Histories Push Push.Local Motion Equiv
variable {V I J : Type*}[DecidableEq I][DecidableEq J] [DecidableEq V][Fintype V]{G:Gauge}{n:Side}
variable {D:Deck V slot I J G n}{E:Equiv.Perm I}{F:Equiv.Perm J}{b:Equiv.Perm V}{v u:V}{m:Motion}{x:Site n}(h:Glow D E F v u m x b)
local notation "P!"=> Equiv.sumCongr E F
set_option quotPrecheck false
namespace Glow
variable [Fintype I][Fintype J]
lemma coated (s:D.Quills){v:V} (hv:D.quip s=(Bud V).fire v) : Dip D v (D.glyph s):=by
   intro i hi; refine subset_trans (subset_biUnion_of_mem D.kiln.mention hi) ?_; rw [← D.paint,hv]; rfl
omit [Fintype I][DecidableEq I] in
lemma deposit {T W:Type*}[Fintype W][DecidableEq T](U L:Config G n)(e:Perm W)(P: W→Prop)(τ:Perm T)
    (f:W→T)(g:W→(Bud V).Mode)(u1 v1:V)(m:Motion)(K:W→Config G n→ℂ) (ht:∀ i,P i→f (e i)=τ (f i)) (hh:∀ i,(g i=(Bud V).fire v1)↔ (g (e i)=(Bud V).fire u1)) (hz:∀ i,g i=(Bud V).fire v1→P i) (hp:∀ i,P i→K (e i) U= scalar m (K i L)) (i:T):
   (tally f (fun i U=>Poly.send (g i) (K i U)) (τ i) U).part ((Bud V).fire u1)=scalar m ((tally f (fun i U=>Poly.send (g i) (K i U)) i L).part ((Bud V).fire v1)):=by
   change (cram f (fun i=>Poly.send (g i) (K i U)) (τ i)).part _= scalar m ((cram f (fun i=>Poly.send (g i) (K i L)) i).part _)
   rw [expand_eq,expand_eq, Poly.share Summable.of_finite,Poly.share Summable.of_finite, ← e.tsum_eq, scalar_tsum]; refine tsum_congr (fun b=>?_)
   by_cases hx:g b=(Bud V).fire v1
   · have hc:= hz b hx
     simp_rw [ht b hc,hx,(hh b).mp hx,Equiv.apply_eq_iff_eq]; split; next H=> simpa only [Poly.part_send,↓reduceIte] using hp b hc
     next h=> exact (scalar_z _).symm
   have hb' : g (e b) ≠ (Bud V).fire u1:= fun he=> hx ((hh b).2 he); have h₁:=Ne.symm hx; have h₂:=hb'.symm; split_ifs<;>simp [h₁,h₂,scalar_z]
include h
lemma versus (x':D.Quills)(y':D.Quills)(hp:Dip D v (D.glyph x') ↔ Dip D u (D.glyph y'))(hm:Dip D v (D.glyph x')→D.quip y'=pars b (D.quip x'))(he:b v=u): D.quip x'=(Bud V).fire v↔ D.quip y'=(Bud V).fire u:=by
   have hf (hg:Dip D v (D.glyph x')) : (D.quip x'=(Bud V).fire v ↔ D.quip y'=(Bud V).fire u):=by
      rw [hm hg, show (Bud V).fire u= pars b ((Bud V).fire v) from ?_,Equiv.apply_eq_iff_eq]; apply Subtype.ext; rw [pares]; simp [Census.fire,he]
   by_cases hz:Dip D v (D.glyph x')
   · exact hf hz
   exact ⟨fun hh=>False.elim (hz (coated x' hh)),fun hh=>False.elim (hz (hp.2 (coated y' hh)))⟩
lemma coupled (he:b v=u) (t:ℝ)(U:Config G n)(S: Support n) : (D.sky t (MergeProof.sky m x S) U).part ((Bud V).fire u) = scalar m ((D.sky t S (pull m.1 x U)).part ((Bud V).fire v)):=by
    obtain ⟨e,hp,H⟩:=h.soars D.Comb (fun s hv=>h.whisk hv)
    let q:=fun i:D.Paper=>Dip D v i.val; have hz (s:D.Paper)(ht:q s):=h.tops (Sum.inl s) (Sum.inl (e s)) ht (H s ht) U
    exact deposit U (pull m.1 x U) e q (MergeProof.sky m x) (fun i=> D.reach i.val) (fun i=> D.quip (.inl i)) u v m (fun i U=>D.bud U (.inl i)) (fun s hh=>(hz s hh).1) (fun s=> h.versus _ _ (hp s) (fun hh=> (hz s hh).2.1) he) (fun s=>coated _) (fun i hh=> (hz i hh).2.2) S
lemma flew (he:b v=u) (t:ℝ)(U:Config G n)(S: Box n) : (D.clay t (MergeProof.puff m x S) U).part ((Bud V).fire u) = scalar m ((D.clay t S (pull m.1 x U)).part ((Bud V).fire v)):=by
    obtain ⟨e,hp,H⟩:=h.soars D.Tank (fun s hv=>h.sink hv)
    let q:=fun i:D.Ink=>Dip D v i.val; have hz (s:D.Ink)(ht:q s):=h.spat s (e s) ht (H s ht) t U
    exact deposit U (pull m.1 x U) e q (MergeProof.puff m x) (fun i=> D.fuse i.val) (fun i=> D.quip (.inr i)) u v m (fun i U=>D.nectar t U i) (fun s hh=>(hz s hh).1) (fun s=> h.versus _ _ (hp s) (fun hh=> (hz s hh).2.1) he) (fun s=>coated _) (fun i hh=> (hz i hh).2.2) S
end Glow
variable {Z:Salt V slot G n} {α η q ℓ g s:ℝ} {w:Name V slot→ℝ} {t:ℝ}
lemma twines (hr:Twin Z t m x v u b)(U:Config G n) : (∀ S,(Z.mount t (sky m x S) U).part ((Bud V).fire u)= scalar m ((Z.mount t S (pull m.1 x U)).part ((Bud V).fire v)))∧ ∀ S,(Z.soil t (puff m x S) U).part ((Bud V).fire u)=scalar m ((Z.soil t S (pull m.1 x U)).part ((Bud V).fire v)):=by
    obtain ⟨E,F,h⟩:=orbital hr; exact ⟨h.coupled hr.who t U,h.flew hr.who t U⟩
end YM.MergeProof.BatchRibbons.Twin
