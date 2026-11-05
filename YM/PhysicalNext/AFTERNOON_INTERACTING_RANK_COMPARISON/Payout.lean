import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dockets
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gel
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pricetags

/-!
# Grants from this bin density

`reward`: reusable main backend, every invoked local Mark/K system,
*same* unmarked inputs. Supply the actual pre-marked V density
and normalization receipts and get first system outputs before
marked log. Pricing Spot is on the actual auditions -- obtained
later from any Rank call's `Light` etc., not a renamed
unsupplied many-marker budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Filter Station Thirst
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ l m r e n w : ℝ} {L : Lantern G S} {A : Stores S} {P : Teller G} {W ι α : Type} [Fintype W] [DecidableEq W]
    {θ : W→Site f} {u : W→ Site c}
section
-- immediate for incoming Lift witnesses (no recost licence).
lemma bond_cost (R : Rep G f) (k : Lifted G θ R.p.threshold) (ht : Boosted T P x) (L : Lantern G S) (B : ℕ)
    (hb : 25*radiusB x+30 ≤ B) (β τ : ℝ) (hv : u=S.ratio.parent ∘ θ) (X : Config G c) (A : Stores S) (z : Streak L.park)
    (f : RoomView A x z.wood G) {r : W→ℝ} (a : ℝ) (ha : Lifted.pays R.p k r e a) : stroke (highTone k P ht L B hb β τ hv) r A z X f ≤ penny k.extent R.p e a:= by
  let U:=gazed T z.tag L.χ X x β L.hood f
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  exact Eq.trans_le (show _ = Value.charge R.p e k.extent* Poly.toll r k.fires * ‖k.value U‖ by unfold stroke; dsimp only [highTone, Value.charge,U]; ring) (ha.2 _)
end
section
variable (R : Rep G f) (R' : Rep G c) (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg)
    (p : ι→ Zest G S x L.park R'.p.threshold) [Fintype ι]
local notation "v'" => fun _ : W => r
local notation "B'" => R'.p.B

/-- density purchase BEFORE marker weights. -/
structure Holdings (T : Tube G S) (r l e a : ℝ) : Prop where
  prices : ∃ c, (∀ i,(p i).Wares T r l (c i)) ∧ Hits (fun i=>(p i).zone) c R'.p (ucap e+1) a
lemma discounted {t t' : ℝ} (h : Holdings R' p T r l e t) (ht : t' ≤ l): Holdings R' p T r t' e t:= by
  obtain ⟨p,h,H⟩:=h.prices; exact ⟨p,(fun _=> Zest.Wares.scale_down _ (h _) ht),H⟩

variable (H : α → Flake S G x L.park u R'.p.threshold) [Fintype α] (C : α→Prop)

-- H and W earnings, including hard nonprincipal light guarded predicate.
structure Spot (T : Tube G S) (l : ℝ) (r : W→ℝ) (e v : ℝ) : Prop where
  balance : ∃ (c : α→ℝ),(∀ i,0≤c i) ∧
     (∀ i A U k z,Positioned x A U → stroke (flakeTone (H i)) r A k U z ≤ c i) ∧
     (∀ i, ¬ C i →∀ U A k,Positioned x A U → Shadow (stroke (flakeTone (H i)) r A k U) (viewer T A x k.wood k.tag U) l (c i)) ∧
     ∀ i : W,strike (fun j => (H j).space) c R'.p (fun j=>i∈(H j).notes.val) (Docking.increment e) ≤ v
variable {κ ρ : Type} (hv : u=S.ratio.parent ∘ θ) (K : κ→ Lifted G θ R.p.threshold) [Fintype κ] [Fintype ρ] (Y : ρ→ SourceAt G θ)
local notation "J0"=> Gel.freezeKey K
local notation "Q" => picture R R' p J0 H ht hs hv


end
end YM.PhysicalNext.InteractingRank.Display.Docking
