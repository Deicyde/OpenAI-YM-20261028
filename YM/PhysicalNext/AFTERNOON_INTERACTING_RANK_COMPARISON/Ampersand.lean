import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Strand
/-! # Low strand naturality through this frame's Party bins -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {τ : ℝ} {V ι κ α β : Type} [Fintype V] [DecidableEq V] {c : V→Site n}
structure Cage (E : α ↪ β) (Q : α→Lining G c τ) (R : β→ Lining G c τ) : Prop where
  same i : (raised (Q i)).extent=(raised (R (E i))).extent
  ancestry i : solute (Q i) ↔ solute (R (E i))
  marks i : (raised (Q i)).fires=(raised (R (E i))).fires
  old j : (raised (R j)).fires.val.card ≤ 1 → j∈ Set.range E
  prices i : (raised (Q i)).fires.val.card ≤ 1 → ∀ U,(raised (Q i)).covets U=(raised (R (E i))).covets U
namespace Bridle
variable {P : ι→ Plug G c τ} {O : κ→ Plug G c τ} {E : ι↪κ} (h : Bridle E P O)
    {Q : α → Lining G c τ} {R : β → Lining G c τ} {F : α↪β} (hp : Cage F Q R)
include h
lemma land (i): (P i).landed ↔ (O (E i)).landed:= by unfold Plug.landed; rw [h.bank]
include hp
local notation "a" => E.sumMap F
local notation "p" => speck P Q
local notation "o" => speck O R

lemma fence i : dish P Q i=dish O R (a i):= by
  rcases i with i|i; exact (dishfest ..).trans ((h.same i).trans (dishfest ..).symm)
  exact hp.same i

 -- type names
omit h hp in
private lemma bloc (t : Finset (ι⊕α)) (x : ι↪κ) (y : α↪β):
    (t.map (x.sumMap y)).toLeft=t.toLeft.map x ∧ (t.map (x.sumMap y)).toRight=t.toRight.map y:= by
  constructor <;> (ext; simp [Finset.mem_map, Sum.exists])
lemma attest i j : fest P Q i j ↔ fest O R (E i) (F j):= by
  unfold fest meets; have ht := fence h hp (.inr j); change dish P Q _ = dish O R (Sum.inr (F j)) at ht
  simp_rw [hp.ancestry j,h.land i,h.same i,ht]
lemma admittance (t : Finset (ι⊕α)) : Spark (dish P Q) t ∧ glasses P Q t ↔ Spark (dish O R) (t.map a) ∧ glasses O R (t.map a):= by
  refine and_congr (casts a _ _ t (fence h hp)) ?_; obtain ⟨hz,hx⟩:=bloc t E F; unfold glasses; rw [hz,hx]; refine and_congr (viewers E _ _ _ h.same) ?_; constructor
  · intro he j hj; obtain ⟨k,hk,rfl⟩:=mem_map.mp hj; obtain ⟨i,hi,hs⟩:=he _ hk
    exact ⟨E i, mem_map_of_mem _ hi,(attest h hp _ _).1 hs⟩
  intro he j hj; obtain ⟨i,hi,ht⟩:= he _ (mem_map_of_mem _ hj); obtain ⟨b,hb,rfl⟩:=mem_map.mp hi; exact ⟨b,hb,(attest h hp b j).2 ht⟩
def ampersand : Party P Q ↪ Party O R where
  toFun i:= ⟨i.val.map a,(admittance h hp i.val).1 i.property⟩
  inj' _ _ ht:= Subtype.ext (map_injective a (congr_arg Subtype.val ht))
local notation "A" => ampersand h hp



omit hp

def brighten : Bright P ↪ Bright O where
  toFun i:= ⟨E i.val,mt (land h _).mpr i.property⟩
  inj' _ _ hz:= Subtype.ext (E.injective (congr_arg Subtype.val hz))
def dimmer : Dimmed P ↪ Dimmed O where
  toFun i:=⟨E i.val,(land h i.val).1 i.property⟩
  inj' _ _ hz:= Subtype.ext (E.injective (congr_arg Subtype.val hz))



end Bridle
end YM.PhysicalNext.InteractingRank.Weaver
