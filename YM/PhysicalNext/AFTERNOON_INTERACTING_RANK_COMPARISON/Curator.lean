import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curated
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Film
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Iced

/-!
# Here run forward the actual audition projection

Knows Glaze s covers precisely an associated (commercial) sublist.
Use under room/all Auth and `approvements`. No mixing clusters across
unauthorized copies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Filter Station
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ : ℝ} {L : Lantern G S} {P : Teller G} {W ι α ρ κ : Type} [Fintype W] [DecidableEq W] {θ : W→ Site f} {u : W→ Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold)
    (K : κ → Lifted G θ R.p.threshold)
    (H : α → Flake S G x L.park u R'.p.threshold) (ht : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B) (hv : u=S.ratio.parent ∘ θ) (Y : ρ ↪ α)
local notation "Q" => picture R R' p K H ht hs hv
local notation "LH" => bequeath Q ht
local notation "F" => (H ∘ Y)
local notation "Q₀" => (flakeTone ∘ F)
def magnify (Y : ρ↪α) : ρ↪ Spectrum ι κ α:=Y.trans Embedding.inr
lemma focusing : Film (magnify Y) Q₀ Q:= ⟨fun _=> rfl⟩
local notation "LF" => focusing R R' p K H ht hs hv Y

def wax : Club Q₀ ↪ Bright LH where
  toFun i := by
    let v : Inn Q₀:=⟨i,Or.inr (chiseling F _).2⟩; let X:=(LF).differs v
    refine ⟨X,fun hh=>(chiseling F i).1 ?_⟩
    rw [(LF).dues i]; exact ((heirs Q ht X).2.2.1) ▸ (show (bequeath Q ht X).inventory.Nonempty from hh)
  inj' i j h := (LF).club.injective (congr_arg (fun z:Bright LH=>z.val.val) h)
local notation "WAX" => wax R R' p K H ht hs hv Y
lemma warmed (i : Club Q₀): sunny LH (WAX i)=principal Q₀ ht i (chiseling F _).1 (chiseling F _).2 := by
  have he := bright_valid LH (WAX i); let v:Inn Q₀:=⟨i,Or.inr (chiseling F _).2⟩
  have hv : (WAX i).val=(LF).differs v:=rfl
  change sunny LH (WAX i)=_
  have h : LH (WAX i).val=Plug.regular (principal Q₀ ht i (chiseling F _).1 (chiseling F _).2) := by
    rw [hv,← (LF).movie]; unfold bequeath; rw [dif_neg (show ¬_ from (chiseling F i).1)]
  exact Plug.regular.inj (he.symm.trans h)
-- predicate only recognizes this lane.
variable (Z : α→Prop)
local notation "ZQ" => Glaze R R' p K H ht hs hv Z
variable [Fintype ι] [Fintype κ] [Fintype α] [Fintype ρ]
lemma attained (hz : ∀ i,Z i ↔ i∈Set.range Y):
    univ.filter (fun i: Bright LH => ZQ i.val) = univ.map WAX := by
  ext i; constructor
  · intro hi
    obtain ⟨hX,hz'⟩ := (mem_filter.mp hi).2
    obtain ⟨p',hp⟩:= (LF).backroll i.val.val (by
      rintro (j|j) hj
      · exact False.elim (by have he:= mem_toLeft.mpr hj; rw [hX] at he; exact notMem_empty _ he)
      obtain ⟨m,hm⟩:= (hz j).1 (hz' _ (mem_toRight.mpr hj)); exact ⟨_, congr_arg _ hm⟩ )
    refine mem_map.mpr ⟨p',mem_univ _,Subtype.ext (Subtype.ext hp)⟩
  intro h; obtain ⟨i,_,rfl⟩:= mem_map.mp h
  apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
  let p':= i.val.map (magnify (ι:=ι) (κ:=κ) Y)
  change p'.toLeft=∅ ∧ ∀ i∈p'.toRight,Z i
  constructor
  · apply eq_empty_iff_forall_notMem.mpr; intro j h
    obtain ⟨v,hv,h⟩:= mem_map.mp (mem_toLeft.mp h)
    change Sum.inr _=Sum.inl _ at h; cases h
  intro j h; obtain ⟨v,hv,h⟩:= mem_map.mp (mem_toRight.mp h)
  exact (hz j).2 ⟨v,Sum.inr.inj h⟩

lemma playback (hz : ∀ i,Z i ↔ i∈Set.range Y) (U : Config G c) : Flux.chair (zone Q₀) (fun i=> proceeds Q₀ T i U) univ= pitch («Q»:=R'.p) LH ZQ U:= by
  unfold pitch; rw [attained R R' p K H ht hs hv Y Z hz]; apply frames
  · intro i; change _=(sunny LH (WAX i)).extent; rw [warmed]; rfl
  intro i; rw [warmed]; exact (principal_check Q₀ ht _ _ _ U).symm
end YM.PhysicalNext.InteractingRank.Display
