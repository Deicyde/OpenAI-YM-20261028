import YM.MergeProof.North.Liturgy
import YM.OPE.Grouping.Calm
import YM.OPE.Grouping.River

/-!
# Lift the symmetry after each fusion

Refines `Liturgy.lean` from the proof of the centered pair merger.
`coated` and `versus` extended to read *all* focus parts, including quiet and
all interactions within a replication cell. Thus the output estimates can power
further fusions down the mesh without forgetting the coherence inherited from the
original cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers.CopyFamily
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
open Extra.Histories Push Push.Local Motion Equiv
variable {V I J : Type*}[DecidableEq I][DecidableEq J] [DecidableEq V][Fintype V]{G:Gauge}{n:Side}
variable {X₀ : Type*} [Fintype X₀][DecidableEq X₀] {Δ : Fibers X₀ V} {a₀:Equiv.Perm X₀} {D:Deck V X₀ Δ I J G n}{E:Equiv.Perm I}{F:Equiv.Perm J}{b:Equiv.Perm V}{v u:Set V}{m:Motion}{x:Site n}(h:Glow D E F v u m x b a₀)
local notation "P!"=> Equiv.sumCongr E F
set_option quotPrecheck false
namespace Glow
variable [Fintype I][Fintype J]
lemma coated (s:D.Quills){v:Set V} (hv:((D.quip s).val:Set V)⊆ v) : Dip D v (D.glyph s):=by
   intro i hi k hk; apply hv; change k∈ (D.quip s).val; rw [D.paint]; exact subset_biUnion_of_mem D.kiln.mention hi hk
omit [Fintype I][DecidableEq I] in
lemma deposit {T W:Type*}[Fintype W][DecidableEq T](U L:Config G n)(e:Perm W)(P: W→Prop)(τ:Perm T)
    (f:W→T)(g:W→(Bud V).Mode)(u1 v1:(Bud V).Mode)(m:Motion)(K:W → Config G n→ℂ) (ht:∀ i,P i→f (e i)=τ (f i)) (hh:∀ i,(g i=v1)↔ (g (e i)=u1)) (hz:∀ i,g i=v1→P i) (hp:∀ i,P i→K (e i) U= scalar m (K i L)) (i:T):
   (tally f (fun i U=>Poly.send (g i) (K i U)) (τ i) U).part u1=scalar m ((tally f (fun i U=>Poly.send (g i) (K i U)) i L).part v1):=by
   change (cram f (fun i=>Poly.send (g i) (K i U)) (τ i)).part _= scalar m ((cram f (fun i=>Poly.send (g i) (K i L)) i).part _)
   rw [expand_eq,expand_eq, Poly.share Summable.of_finite,Poly.share Summable.of_finite, ← e.tsum_eq, scalar_tsum]; refine tsum_congr (fun b=>?_)
   by_cases hx:g b=v1
   · have hc:= hz b hx
     simp_rw [ht b hc,hx,(hh b).mp hx,Equiv.apply_eq_iff_eq]; split; next H=> simpa only [Poly.part_send,↓reduceIte] using hp b hc
     next h=> exact (scalar_z _).symm
   have hb' : g (e b) ≠ u1:= fun he=> hx ((hh b).2 he); have h₁:=Ne.symm hx; have h₂:=hb'.symm; split_ifs<;>simp [h₁,h₂,scalar_z]
include h
lemma versus (x':D.Quills)(y':D.Quills)(hp:Dip D v (D.glyph x') ↔ Dip D u (D.glyph y'))(hm:Dip D v (D.glyph x')→D.quip y'=pars b (D.quip x')) (he:∀ i,b i ∈ u ↔ i∈v)
      (p:(Bud V).Mode) (hx:(p.val:Set V)⊆v) : D.quip x'=p↔ D.quip y'=pars b p :=by
   have hf (hg:Dip D v (D.glyph x')) : (D.quip x'=p ↔ D.quip y'=pars b p):=by rw [hm hg,Equiv.apply_eq_iff_eq]
   by_cases hz:Dip D v (D.glyph x')
   · exact hf hz
   have h_u : ((pars b p).val:Set V)⊆ u := by
     rw [pares,coe_image,Set.image_subset_iff,show b ⁻¹' u=v from Set.ext he]; exact hx
   exact ⟨fun hh=>False.elim (hz (coated x' (hh ▸ hx))),fun hh=>False.elim (hz (hp.2 (coated y' (hh ▸ h_u))))⟩
lemma coupled (he:∀ i,b i ∈ u ↔ i∈v)(p:(Bud V).Mode)(hq:(p.val:Set V)⊆ v) (t:ℝ)(U:Config G n)(S: Support n) : (D.sky t (MergeProof.sky m x S) U).part (pars b p) = scalar m ((D.sky t S (pull m.1 x U)).part p):=by
    obtain ⟨e,hp,H⟩:=h.soars D.Comb (fun s hv=>h.whisk hv)
    let q:=fun i:D.Paper=>Dip D v i.val; have hz (s:D.Paper)(ht:q s):=h.tops (Sum.inl s) (Sum.inl (e s)) ht (H s ht) U
    exact deposit U (pull m.1 x U) e q (MergeProof.sky m x) (fun i=> D.reach i.val) (fun i=> D.quip (.inl i)) (pars b p) p m (fun i U=>D.bud U (.inl i)) (fun s hh=>(hz s hh).1) (fun s=> h.versus (.inl s) (.inl (e s)) (hp s) (fun hh=> (hz s hh).2.1) he p hq) (fun i h=>coated (D:=D) (.inl i) (h ▸ hq)) (fun i hh=> (hz i hh).2.2) S
lemma flew (he:∀ i,b i ∈ u ↔ i∈v)(p:(Bud V).Mode)(hq:(p.val:Set V)⊆ v) (t:ℝ)(U:Config G n)(S: Box n) : (D.clay t (MergeProof.puff m x S) U).part (pars b p) = scalar m ((D.clay t S (pull m.1 x U)).part p):=by
    obtain ⟨e,hp,H⟩:=h.soars D.Tank (fun s hv=>h.sink hv)
    let q:=fun i:D.Ink=>Dip D v i.val; have hz (s:D.Ink)(ht:q s):=h.spat s (e s) ht (H s ht) t U
    exact deposit U (pull m.1 x U) e q (MergeProof.puff m x) (fun i=> D.fuse i.val) (fun i=> D.quip (.inr i)) (pars b p) p m (fun i U=>D.nectar t U i) (fun s hh=>(hz s hh).1) (fun s=> h.versus (.inr s) (.inr (e s)) (hp s) (fun hh=> (hz s hh).2.1) he p hq) (fun i h=>coated (D:=D) (.inr i) (h ▸ hq)) (fun i hh=> (hz i hh).2.2) S
end Glow
variable {Z:Salt V X₀ Δ G n} {α η q ℓ g s:ℝ} {w:X₀→ℝ} {t:ℝ}
lemma twines (hr:CopyFamily Z t m x v u a₀ b)(U:Config G n)(p:(Bud V).Mode)(hq:(p.val:Set V)⊆ v) :
    (∀ S,(Z.mount t (sky m x S) U).part (pars b p)= scalar m ((Z.mount t S (pull m.1 x U)).part p)) ∧
    ∀ S,(Z.soil t (puff m x S) U).part (pars b p)=scalar m ((Z.soil t S (pull m.1 x U)).part p) :=by
    obtain ⟨E,F,h⟩:=orbital hr; exact ⟨h.coupled hr.who p hq t U,h.flew hr.who p hq t U⟩
end YM.MergeProof.Ribbons.Fibers.CopyFamily
