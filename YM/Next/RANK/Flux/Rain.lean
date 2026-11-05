import YM.Next.RANK.Flux.Conform

/-!
# Restoration pressure of the vacuum OP

Push amounts from receipts. No later contour matching. BG preevac included. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t)

/-- Uncolored debt (carried at quiet word). -/
def flat (K : κ → Lining G ζ t) := (∀ i,(raised (K i)).fires=quiet V)

-- boundary letters: Use on every configuration, with flag pressure.
structure Boundary (F : α → CoverReads G ζ t) : Prop where
  amount i : (F i).fires=quiet V
  requires i U : Healthy t (F i).extent U → (F i).value U=0

def witness (F : α → CoverReads G ζ t) : α → Lining G ζ t:= Sum.inr ∘ F
lemma boundary_pay [Fintype ι] [Fintype α] (S : ι→Lifted G ζ t) (F : α → CoverReads G ζ t) (U : Config G n) (h : Boundary F):
    deck_at (Plug.raid ∘ S) U * (∏ i, ((F i).covets U+1))=embellished (Plug.raid ∘ S) (witness F) U:= by
  rw [deck_at,Finset.sum_mul]; apply sum_congr rfl; intro p hp; apply congr_arg; let X:=Plug.raid ∘ S
  have ht : unmark X p (flags t U):= (mem_filter.mp hp).2
  change _=∏ i ∈ univ.filter (fun i:α=> earns X (witness F) i p),((F i).covets U+1)
  symm; apply Finset.prod_subset (Finset.filter_subset ..); intro i hi hh
  have hv: Healthy t (F i).extent U:= by
    apply disjoint_left.mpr; intro j hj hl
    rw [← ht.2] at hl; obtain ⟨k,hk,hK⟩:=mem_biUnion.mp hl
    exact hh (mem_filter.mpr ⟨hi, k,hk,⟨j,(S k).records hK,hj⟩,fun _=> (S k).needed⟩)
  rw [CoverReads.covets,h.requires i U hv,Poly.send_zero,zero_add]

-- Exact formula of continuation

variable (C : α → CoverReads G ζ t)

variable [Fintype ι] [Fintype κ] [Fintype α]

def infrared : Config G n→ veil V:=fun U=>embellished S P U*(∏ i:α, ((C i).covets U+1))

-- names from real P fixed. For future matcher keep via `emb_bg`
-- let Sun, Clouds determined.

-- For ease Lean Fintype of Sun always use intrinsic Fintype for panel once
set_option synthInstance.maxSize 384 in
abbrev Dusty := toRain (evening (panel S P)) (negXs (sunny (panel S P)))
set_option synthInstance.maxSize 384 in
abbrev after := toRain (Dusty S P) (witness C)
lemma soot (F : κ→Lifted G ζ t) (Q : ι→Lining G ζ t) U : deck_at (panel (Plug.raid ∘ F) Q) U=RAIDage (toRain F Q) U:= by rw [rainbows,storm]

lemma placed (U : Config G n) (h : Boundary C) : infrared S P C U= Poly.pass (∑ i : MergeLog (sunny (panel S P)),(Bond (sunny (panel S P)) i).amount t U)*RAIDage (after S P C) U:= by
  let A:=panel S P; let X:=sunny A; let D:=evening A; let T := panel (Plug.raid ∘ D) (negXs X); let f:= ∏ i:α, ((C i).covets U+1); let L:=Dusty S P
  have he : ∀ x, T x=Plug.raid (L x):= fun i=> congr_fun (rainbows ..) i
  have hx: deck_at T U * f=RAIDage (after S P C) U:= by
    let J:=panel (Plug.raid ∘ L) (witness C); calc
      _=deck_at (Plug.raid ∘ L) U * f:= by rw [show T = Plug.raid ∘ L from funext he]
      _ = embellished (Plug.raid ∘ L) (witness C) U:= boundary_pay L C U h
      _= deck_at J U:= (flood ..).symm
      _= _:= soot L _ _
  let B:= Poly.pass (∑ i:MergeLog X,(Bond X i).amount t U)
  change embellished S P U*f= B*_
  rw [show _=B*deck_at T U from (show embellished S P U= B*deck_at T U from aftermath S P U),mul_assoc,hx]

-- vector recall
set_option synthInstance.maxSize 384 in
omit [Fintype α] in
lemma rainy {R : β→Lifted G ζ t} (E : Embedded R S) : Nonempty (Embedded (toRain (toRain R P) (witness C)) (Plug.raid ∘ after S P C)):= by
  let A:=panel S P; let X:=sunny A
  have hp := E.lining P
  obtain ⟨Q⟩:= Embedded.rainfalls hp
  obtain ⟨J⟩:= Q.exhale (negXs (t:=t) X) (fun i=> (Bond X i).chosen)
  let T : Plug.raid ∘ after S P C= panel (Plug.raid ∘ Dusty S P) (witness C) := (rainbows ..).symm
  exact ⟨T.symm ▸ J.lining (witness C)⟩
end YM.Next.Rank.Flux
