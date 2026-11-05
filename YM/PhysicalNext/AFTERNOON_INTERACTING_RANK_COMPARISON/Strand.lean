import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Film
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gel
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures
/-!
# Single-probe memory through the actual Reader kernel

Lift addresses which depend on mask, paths and flags at the correct location.
Accounting retains low HERE on their FULL masked values. Not assuming relation
of underlying H extensions beyond the mask as matter of projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ : ℝ} {L : Lantern G S} {k : Teller G} {W ι α ρ κ : Type} [Fintype W] [DecidableEq W] {θ : W→ Site f} {u : W→ Site c}
-- LOG relation on structural data, value ONLY at splice window.
structure Bridle (E : ι↪κ) (P : ι→Plug G u τ) (Q : κ→Plug G u τ) : Prop where
  same i : (P i).extent=(Q (E i)).extent
  bank i : (P i).inventory=(Q (E i)).inventory
  marks i : (P i).fires=(Q (E i)).fires
  old j : (Q j).fires.val.card ≤ 1 → j∈ Set.range E
  prices i : (P i).fires.val.card ≤ 1 → ∀ U,(P i).tolls U=(Q (E i)).tolls U

section
variable (A : Rep G f) (B : Rep G c) (Z : α → Zest G S x L.park B.p.threshold) (C : Boosted T k x) (hp : u=S.ratio.parent ∘ θ) {n} (hv : 25*radiusB x+30≤n)
    (K H : ρ→ Lifted G θ A.p.threshold) (P : ι → Flake S G x L.park u B.p.threshold) (Q : κ → Flake S G x L.park u B.p.threshold)
    (E : ι↪κ)
structure InputMatched : Prop where
  keys i : Gel.name (K i)=Gel.name (H i)
  pennies i : (K i).fires.val.card ≤ 1 → K i=H i
  flakes i : P i=Q (E i)
  old j : (Q j).notes.val.card ≤ 1 → j∈ Set.range E
local notation "M0" => picture A B Z K P C hv hp
local notation "M" => picture A B Z H Q C hv hp
variable {A B K H P Q E} (h : InputMatched (S:=S) A B (L:=L) (x:=x) K H P Q E)
abbrev liftE {α ρ ι κ : Type} (E : ι↪κ) := ((Embedding.refl (α⊕ρ)).sumMap E)
local notation "XL" => liftE (α:=α) (ρ:=ρ) E
include h
lemma names (i : Spectrum α ρ ι) : (M (XL i)).X=(M0 i).X ∧ (M (XL i)).goal=(M0 i).goal ∧ (M (XL i)).supplies=(M0 i).supplies∧(M (XL i)).wants=(M0 i).wants∧(M (XL i)).permit=(M0 i).permit∧ (M (XL i)).barricade=(M0 i).barricade ∧ (M (XL i)).encumbrance=(M0 i).encumbrance ∧ (M (XL i)).hues=(M0 i).hues:= by
  rcases i with (i|i)|i
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · let a:=S.ratio; have hx := h.keys i
    have hg := congr_arg (fun t : Gel.Setting θ=> t.val.1.val) hx
    have hy:(H i).extent=(K i).extent:=congr_arg Prod.fst hg.symm
    exact ⟨congr_arg (wings S n) hy,rfl,rfl,congr_arg Prod.snd hg.symm,rfl,rfl,hy,congr_arg (fun t:Gel.Setting θ=>t.val.2) hx.symm⟩
  have hx := h.flakes i
  have ht : M (XL (.inr i)) = M0 (.inr i) := congr_arg flakeTone hx.symm
  rw [ht]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma jural (s : Finset (Spectrum α ρ ι)) : (Spark (zones M0) s ∧ enlist M0 s) ↔ Spark (zones M) (s.map XL) ∧ enlist M (s.map XL):= by
  let A := M0; let B:= M; let x:= XL; have hp:= names Z C hp hv h
  refine and_congr (casts x _ _ s (fun i=>Eq.symm (hp i).1)) ?_
  unfold enlist Display.premise
  rw [viewers x _ (fun i=>(B i).barricade) _ (fun i=>(hp i).2.2.2.2.2.1.symm),viewers x _ (fun i=>(B i).encumbrance) _ (fun i=>(hp i).2.2.2.2.2.2.1.symm),filming x _ (fun i=>(B i).supplies) _ (fun i=>(hp i).2.2.1.symm), filming x _ (fun i=>(B i).wants) _ (fun i=>(hp i).2.2.2.1.symm)]
  exact and_congr Iff.rfl (viewers x _ _ _ (fun i=>congr_arg Subtype.val (hp i).2.2.2.2.2.2.2.symm))

def lowClub : Club M0 ↪ Club M where
  toFun i:= ⟨i.val.map XL,(jural Z C hp hv h _).1 i.property⟩
  inj' _ _ hz:=Subtype.ext (map_injective _ (congr_arg Subtype.val hz))
local notation "A0" => lowClub Z C hp hv h
lemma litClub (i : Club M0) : zone M0 i=zone M (A0 i) ∧ cardGoal M0 i.val=cardGoal M (A0 i).val∧ fires M0 i.val=fires M (A0 i).val:= by
  have hh:= names Z C hp hv h; exact ⟨filming XL _ _ _ fun i=> (hh i).1.symm,filming XL _ _ _ fun i=> (hh i).2.1.symm,congr_arg scene (filming XL _ _ _ fun i=> congr_arg Subtype.val (hh i).2.2.2.2.2.2.2.symm)⟩
lemma chamber (i : Club M0) : promotes M0 i ↔ promotes M (A0 i) := by
  unfold promotes; obtain ⟨-,hz,h⟩:=litClub Z C hp hv h i; rw [hz,h]

def cusp : Inn M0 ↪ Inn M where
  toFun i := ⟨A0 i.val,(chamber Z C hp hv h _).1 i.property⟩
  inj' _ _ hz:=Subtype.ext ((A0).injective (congr_arg Subtype.val hz))
local notation "V0" => cusp Z C hp hv h


end
end YM.PhysicalNext.InteractingRank.Weaver
