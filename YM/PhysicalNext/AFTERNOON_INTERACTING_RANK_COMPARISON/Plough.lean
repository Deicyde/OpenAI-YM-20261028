import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Discs
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Furnace
/-! # Adapt a single Epoch unmarked payment to both Glow settings. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Docking
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] [Fintype ι] [Fintype α]
    {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η M l σ e y w v : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Opacity R R' p A hs hR ν (D:=D) (J:=J) e M l σ)
    (Ly : Lease S.patch.L R.p R'.p e M l σ y η)
    (hp : Resin R R' p A hs hR ν E e y)
local notation "Q"=> germinates R R' p A hs hR E
include Ly hp he
lemma fireplace {e' M' l' r : ℝ} (hf : e' ≤ e) (hM : M' ≤ M) (hv : l' ≤ l) (hr : 0<r) : Fireplace R Q A hs J L D r e' M' l' (y/16) (y/4) y:= by
  obtain ⟨z,hz,h⟩:= he.cash.prices; let D':= Q
  have hk : ∃ z,(∀ i,(p i).Wares T M' l' (z i)) ∧ Hits (fun i=>(p i).zone) z R'.p (ucap e'+1) (y/16):= by
    refine ⟨z,fun i=>⟨(hz _).1,fun U B hf hh k=>?_⟩,fun i=> (marches _ _ (fun i=>(hz i).1) h (show ucap e'+1 ≤ _ by unfold ucap; linarith only [hf]) i).trans Ly.due⟩
    obtain ⟨X,hx,H⟩ := Zest.Wares.scale_down _ (hz i) hv|>.2 U B hf hh k
    refine ⟨X,(mul_le_mul_of_nonneg_right (show (p i).infl M' l' ≤ (p i).infl M l' by unfold Zest.infl;split;exact hM;exact le_rfl) ?_).trans hx,H⟩
    exact Tilt.fractional X
  constructor
  refine ⟨_,inferInstance,p,_,he.roofs,⟨hk⟩,fun W h1 h2 θ u H=> ?_⟩
  let T' := carves R R' p A hs hR E he θ u H
  obtain ⟨ht,hk⟩:= in_boxes R R' p A hs hR E he θ u H Ly hp (fun _=>r) (fun _=>hr)
  obtain ⟨z,w,hz,hv',hP,hZ,h,h'⟩:= repair_lower Q _ (fun _=>hr) hk hv
  refine ⟨T', ⟨z,w,hz,hv',hP,hZ,marches _ _ hz h (by unfold ucap;linarith),marches _ _ hv' h' (by unfold ucap;linarith)⟩,fun o t r s v hV=>?_⟩
  exact ⟨ht.pays,ht.rolls⟩
end YM.PhysicalNext.InteractingRank.Display.Sew
