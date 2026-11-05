import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Film
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gel
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures


/-!
# Earnings from this same purchase across any audition

Issue the unmarked connection needed to the V branch (`ReturnTrip`).

Not assuming Matric/Bouys for the full launch.

Prove the marked
identity here using layout income, actual body receipt, this connection
and `Background`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ σ w : ℝ} {L : Lantern G S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α φ : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold)
    (K : κ → Lifted G θ R.p.threshold) [Fintype κ]
    (H : α → Flake S G x L.park u R'.p.threshold) (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ) {o m Λ δ b : ℝ} (hR : R.Lawful o m Λ δ b)
    [Fintype ι] [Fintype α] [Fintype φ] {D : Allocation G S x w} {J : ChartRatio G}

local notation "Q" => picture R R' p (Gel.freezeKey K) H ht hs hv
def unmarked : Spectrum ι (addressKey f) Empty → PaintCan S G x L.park u R'.p.threshold:=
    picture R R' p (Gel.archived R θ hR) (Empty.elim) ht hs hv
local notation "Q0" => unmarked R R' p ht hs hv hR
def chip (θ : W→Site f): addressKey f ↪ Gel.Setting θ:= ⟨Gel.hush θ,fun _ _ H=>congr_arg (fun (l : Gel.Setting θ)=>l.val.1) H⟩
def coupon (θ : W→Site f): Spectrum ι (addressKey f) Empty ↪ Spectrum ι (Gel.Setting θ) α:=
    ((Embedding.refl ι).sumMap (chip θ)).sumMap (Embedding.ofIsEmpty : Empty ↪ α)
omit [Fintype ι] [Fintype α] in
lemma auditioned (h : Background R K) : Film (coupon θ) Q0 Q:= by
  constructor; rintro ((i|i)|i);rfl
  · exact congr_arg (fun v=> highTone v P ht L Wg hs R.beta R'.p.threshold hv) (Gel.same_vac R hR K h i).symm
  exact i.elim
omit [Fintype ι] [Fintype α] in
lemma clicked i (h : (Q i).hues=quiet W) : i∈ Set.range (coupon θ) := by
  rcases i with (i|i)|i
  · exact ⟨.inl (.inl i),rfl⟩
  · let j:=i.val
    have hv : i= Gel.hush θ j.1 := Subtype.ext (Prod.ext rfl h)
    exact ⟨.inl (.inr j.1),congr_arg (fun v : Gel.Setting θ=> Sum.inl (β:=α) (Sum.inr (α:=ι) v)) hv.symm⟩
  exact False.elim ((H i).nontrivial.ne_empty (show (H i).notes.val= ∅ from congr_arg Subtype.val h))

/-- Requires exact unmarked log (even with holes; e.g. use ReLog later),
interval and label alignment with K base. Vac costs purchased separately. -/
structure ReturnTrip (p' : Config G c → ℂ) (B : Flux.Vac u R') : Prop where
  pays : Flux.Intervals B p' (germ Q0 ht)
  rolls : Nonempty (Flux.Embedded B.f (bequeath Q0 ht))


end YM.PhysicalNext.InteractingRank.Display
