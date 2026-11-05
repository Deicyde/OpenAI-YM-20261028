import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Choreo
/-!
# Whole quiet background accounting through Rain mergers

Use to recover on every W. Move geometry in support address equations, not
E Ledger permeability. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S} {O : Orchard S} {R : Rep G c}
    {A : Stores S} {P : Teller G} {W V ι κ α β υ ρ : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c}

section quiet
variable {K : α → Lifted G u τ} {G' : ι → Lining G u τ}
local notation "Wx" => (Plug.raid ∘ K)
local notation "Ω" => Party Wx G'
lemma blanking (hk : ∀ i,(K i).fires=quiet W) (hp : ∀ i,(raised (G' i)).fires=quiet W) (j : Ω) : (toRain K G' j).fires=quiet W:= by
  have he i : (speck Wx G' i).fires=quiet _:=by rcases i with i|i;exacts [hk i,hp i]
  change shining Wx G' j=_; unfold shining; simp only [he]; apply Subtype.ext; ext i; simp [scene,Glyph.quiet,Census.quiet]
lemma short_print (hk : ∀ i,(K i).fires=quiet W) (hp : ∀ i,(raised (G' i)).fires=quiet W) (U) (j : Ω) :
    (toRain K G' j).value U=if Flux.tint Wx G' j U then ∏ i∈j.val,(speck Wx G' i).value U else 0:=by
  have hf i : (speck Wx G' i).fires=quiet W:=by rcases i with i|i;exacts [hk i,hp i]
  change (if _ then _ else _) = _; rw [show shining Wx G' j=quiet _ from blanking hk hp j]
  unfold Flux.toast CoverReads.covets; simp_rw [hf, show Poly.send (quiet W)=algebraMap ℂ (veil W) from rfl, ← map_prod]
  split
  next h => exact (Poly.part_send ..).trans (if_pos rfl)
  rfl
end quiet

section
variable {K : α→ Lifted G u τ} {J : β→Lifted G v τ}
    (b : Config G c →Config G c)
    (X : Equiv.Perm (Site c)) (F : ι≃κ) (L : α≃β)
    {G' : ι → Lining G u τ} {G₁ : κ → Lining G v τ}
structure Waking (X : Equiv.Perm (Site c)) (L : α≃β) (K : α→ Lifted G u τ) (J : β→Lifted G v τ) : Prop where
  extent i : (J (L i)).extent=(K i).extent.map X.toEmbedding
  inventory i : (J (L i)).inventory=(K i).inventory.map X.toEmbedding
  values i a : (K i).value (b a)=(J (L i)).value a
  quiet i : (K i).fires=quiet W
  fresh i : (J i).fires=Glyph.quiet V

structure Changing (X : Equiv.Perm (Site c)) (L : ι≃κ) (Q : ι→ Lining G u τ) (R : κ→Lining G v τ) : Prop where
  extent i : (raised (R (L i))).extent=(raised (Q i)).extent.map X.toEmbedding
  values i a : (raised (Q i)).value (b a)=(raised (R (L i))).value a
  quiet i : (raised (Q i)).fires=quiet W
  fresh i : (raised (R i)).fires=Glyph.quiet V
namespace Waking
variable {L b F X} (h : Waking b X L K J) (hp : Changing b X F G' G₁)
local notation "Ω" => Party (Plug.raid∘ K) G'
local notation "Ω'" => Party (Plug.raid∘ J) G₁
local notation "A" => (Plug.raid∘ K)
local notation "C" => (Plug.raid∘ J)
local notation "Ψ" => dish (Plug.raid∘ K) G'
local notation "Φ" => dish (Plug.raid∘ J) G₁
local notation "υ" => Equiv.sumCongr L F
include h hp
lemma tubes (i) : Φ (υ i)= (Ψ i).map X.toEmbedding:= by rcases i with i|i;exacts [h.extent _,hp.extent _]
lemma moving_bank (s : Finset (α⊕ι)) :
    Spark Ψ s ∧ glasses A G' s ↔ Spark Φ ((υ).finsetCongr s) ∧ glasses C G₁ ((υ).finsetCongr s):=by
  refine and_congr (migrate_connect υ s Ψ Φ (tubes h hp)) ?_
  let U := (υ).finsetCongr s
  have heL : U.toLeft=s.toLeft.map L.toEmbedding:= by
    ext i; rw [Finset.mem_map_equiv,Finset.mem_toLeft,Finset.mem_toLeft]
    exact Finset.mem_map_equiv
  have heR : U.toRight=s.toRight.map F.toEmbedding:= by
    ext i; rw [Finset.mem_map_equiv,Finset.mem_toRight,Finset.mem_toRight]
    exact Finset.mem_map_equiv
  have hg i j: fest A G' i j ↔ fest C G₁ (L i) (F j) := by
    have ha : Plug.landed (A i):= (K i).needed; have hb : Plug.landed (C (L i)):= (J _).needed
    unfold fest; simp only [ha,hb,implies_true,and_true]
    have hv : ∀ U V:Support c,meets (fun _ : Unit=>V) () U ↔ (U ∩ V).Nonempty:=by
      intro U V; constructor; rintro ⟨x,hx,h⟩; exact ⟨x,mem_inter.mpr ⟨hx,h⟩⟩; rintro ⟨x,hx⟩; exact ⟨x,mem_inter.mp hx⟩
    change meets (fun _ : Unit=> (raised (G' j)).extent) () (K i).extent ↔ meets (fun _ : Unit=> (raised (G₁ (F j))).extent) () (J (L i)).extent
    rw [hv,hv,hp.extent,h.extent,← Finset.map_inter,Finset.map_nonempty]
  unfold glasses; change _ ↔ ((U.toLeft:Set β).PairwiseDisjoint (fun i=>(J i).extent)∧ ∀ j∈U.toRight,earns C G₁ j U.toLeft)
  rw [heL,heR]; refine and_congr (migration_disjoint X (fun i=>(K i).extent) (fun i=>(J i).extent) L h.extent _) ?_
  constructor
  · intro h j hj; obtain ⟨i,hi,rfl⟩:= mem_map.mp hj; obtain ⟨j,hj,h0⟩:= h i hi; exact ⟨L j,mem_map.mpr ⟨_,hj,rfl⟩,(hg ..).mp h0⟩
  intro h j hj; obtain ⟨i,hi,H⟩:= h (F j) (mem_map.mpr ⟨_,hj,rfl⟩); obtain ⟨i,hi₁,rfl⟩:=mem_map.mp hi; exact ⟨i,hi₁,(hg ..).mpr H⟩

def carousel : Ω ≃ Ω':= Equiv.subtypeEquiv (υ).finsetCongr (moving_bank h hp)
lemma shuttered (hf : ∀ U,flags τ U=(flags τ (b U)).map X.toEmbedding) : Waking b X (carousel h hp) (toRain K G') (toRain J G₁):= by
  have hE (i : Ω) : lamps C G₁ (carousel h hp i)= (lamps A G' i).map X.toEmbedding:= migration X i.val υ Ψ Φ (tubes h hp)
  have hA (i : Ω) : vital C G₁ (carousel h hp i)=(vital A G' i).map X.toEmbedding:= by
    have h₁:(carousel h hp i).val.toLeft=i.val.toLeft.map L.toEmbedding:= by
      ext j; rw [Finset.mem_map_equiv,Finset.mem_toLeft,Finset.mem_toLeft]; exact Finset.mem_map_equiv
    unfold vital; rw [h₁]; exact migration X i.val.toLeft L (fun i=>(K i).inventory) (fun i=>(J i).inventory) h.inventory
  refine ⟨hE,hA,fun i U=>?_,blanking h.quiet hp.quiet,blanking h.fresh hp.fresh⟩
  rw [short_print h.quiet hp.quiet,short_print h.fresh hp.fresh]
  have ht : tint A G' i (b U)↔tint C G₁ (carousel h hp i) U:= by unfold tint; rw [hE,hA]; exact mark_pass X _ _ _ _ (hf U)
  refine if_congr ht ?_ rfl
  change _=∏ j∈i.val.map (υ).toEmbedding,(speck C G₁ j).value U
  rw [prod_map]; apply prod_congr rfl; intro i _; rcases i with i|i; exacts [h.values i U,hp.values i U]
end Waking
end
end YM.PhysicalNext.InteractingRank.Display.Sew
