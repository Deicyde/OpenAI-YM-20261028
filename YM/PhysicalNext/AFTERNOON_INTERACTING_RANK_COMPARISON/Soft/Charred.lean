import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tissue
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Weaves
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stocking


/-!
# Auxiliary use of whitened R

Forced K assembly and embedding from the stage-1 calculation
(adapted from Stocking and subsequent Payout style). Unmarked advancement
still requires real Tissue on output when consuming this vacuum. K
pricing here takes the calibrated kinetic support and resources on
those very labels. NOT asserting equality of densities from this step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Display Display.Sew Display.Docking
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W ι κ α β : Type} [Fintype W] [DecidableEq W]
    [Fintype ι] [Fintype α]
section closure
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η M l σ e y w v : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Veins R R' p A hs hR e M l σ)
    (Ly : Lease S.patch.L R.p R'.p e M l σ y η)
    (hp : Resin R R' p A hs hR ν E e y)
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "R0"=> Gel.archived R (blank f) hR
local notation "Q"=> germinates R R' p A hs hR E
local notation "V0"=> courtyard R R' p A hs hR E
local notation "Λ0"=> (v_carves R R' p A hs hR E he (blank f) (blank c) (blink S))
local notation "Fl"=> (Empty.elim : Empty→Flake S G x L.park (blank c) R'.p.threshold)
local notation "wk"=> (Empty.elim : Empty→Prop)
local notation "Wp"=> (Empty.elim : Empty→ℝ)

include Ly hp he
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 600000 in
lemma v_emblazoned : Stripes R'.p V0 (fun _=>1) R'.p.supportExponent (1/M):= by
  obtain ⟨hT,hV⟩:= v_in_boxes R R' p A hs hR E he (blank f) (blank c) (blink S) Ly hp (fun _=>1) (fun _=>zero_lt_one)
  obtain ⟨z,v,hz,hb⟩:= v_commissioned R R' p A hs hR he (blank f) (blank c) (blink S) Ly (fun _=>1) (fun _=>zero_lt_one)
  have ht : Hits (zones X0) (bid z v Wp) R'.p (ucap e+1) (2*σ):= marches _ _ (incomes _ _ _ _ _ _ _ _ _ _ _ _ hz) hb (by unfold ucap; linarith only)
  let T':=Λ0
  let K:= picture R Q p R0 Fl A (show 25*radiusB x+30≤(Q).p.B from hs) (blink S)
  let G:= bequeath K A
  -- create auth directly on this Vac Rep. Transports not an estimate.
  have hh: LetterCost R Q p R0 Fl A hs (blink S) wk z v Wp l M (fun _=>1):= by
    exact ⟨hz.1,hz.2,hz.3,hz.4,hz.5,hz.6⟩
  let g:=Glaze R Q p R0 Fl A hs (blink S) wk
  have hx:rawRadii T' G g 1 e M l y 0:= finances _ _ _ _ _ _ _ _ _ _ _ _ T' hh Ly.lamps Ly.bright zero_lt_one hV Ly.coin ht Ly.inferno Ly.fees (fun i=>i.elim)
  let Y:=after G (measureH T') T'.pay
  have ha : Stripes (Q).p Y (fun _=>1) (e+1) (1/M):= (authenticity T' G g _ (fun _=>zero_lt_one) Ly.bright Ly.lamps Ly.coin Ly.resumes hx).2.2
  obtain ⟨H⟩:= (show Nonempty (Embedded T'.f G) from hT.rolls)
  obtain ⟨C⟩:= rainy G (measureH T') T'.pay H
  have hv : Stripes (Q).p V0 _ (e+1) (1/M):= pull_stripe _ C ha
  exact billed_again _ (show Stripes R'.p V0 (fun _=>1) _ _ from hv) Ly.output (fun _=> zero_lt_one)

lemma churning {σ δ C χ : ℝ} (hx : 1/M≤v) (h : R'.path.Bounds R'.clip σ C χ)
    (hb : ∀ s i,Nonempty (R'.activities.Moves s i)) (ht : Petals R' δ) : Tissue Q σ C χ δ v:= by
  let R'':= Q
  have hh (i : (Λ0).D) : ((Λ0).f i).fires=quiet _:= Vac.debt _ i
  have hz i : (V0 i).fires= quiet _:= blanking (blanking hh (fun _=>rfl)) (fun _=>rfl) i
  have hC:= burnCost R' V0 (v_emblazoned R R' p A hs hR E he Ly hp) hz
  refine ⟨?_, v_travelers R R' p A hs hR E he hp hb, ?_⟩
  · have hF : R''.activities.ForcedFamily R''.p:= plenty _ (seated R' V0) (fun i=> (prepare (bareBurst ∘ V0) i).choose_spec.1) _ _
    obtain ⟨m,hm,hw⟩:=hC
    have hF : R''.activities.ForcedFamily (R'').p:= hF
    refine ⟨h, ⟨noCharge R'',⟨hF.sym,hF.symtest,hF.meas,hF.meas_test,hF.reads,hF.reads_test,hF.permit⟩,?_,noDebit R'',m,hm,fun i=>⟨(hw i).1,(hw i).2.1,(hw i).2.2.trans hx⟩⟩⟩
    intro s i; exact (v_travelers R R' p A hs hR E he hp hb s i).map (whiteTurns _ _ _)
  exact ⟨ht.toss,ht.live,ht.look,ht.price⟩
end closure
end YM.PhysicalNext.InteractingRank.Soft
