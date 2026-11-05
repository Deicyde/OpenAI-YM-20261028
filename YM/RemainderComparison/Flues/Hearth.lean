import YM.RemainderComparison.Flues.Ridges
import YM.RemainderComparison.Typeface.Press

/-!
# Launch on exact P.Ballad input. Countable spectrum.

Produce closable K book directly from physical address & per-decorated
estimates, preserving actual flag/inventory even on duplicate slots. No bound
after reordering only a number on unaligned basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif Typeface
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)(Z:Set ι)(δ:ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l δ H τ K Y I)
local notation "Lt"=> sits Z l δ
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable [Countable ι]
variable [DecidableEq β]{Jm:Marker.Census β}
variable (z:ι→Marker.Poly Jm) {gP:β→ℝ} (hZ : Chorus Jm gP Z z k)
open Mallow Ovens Progress.DirectedRecipe
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)

local notation "VB" => Refrain.read H' D χ E₀ V₀
local notation "f'"=> Refrain.visa H' D

abbrev Elbow:= Σ i:Refrain.Leaf H,Serif.KEntry (brand M x') H i
def badge (Y:Elbow H M x') : ℕ := f' Y.fst
local instance (p:Refrain.Leaf H): Countable (Serif.KEntry Vx H p):= inferInstanceAs (Countable ((j:↥p.val.fst)→ Slots H _ j→Mosaic.Stone _ _ j.val))

def funnel (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0) : Elbow H M x' ↪ ℕ := by
   haveI : Countable (Refrain.Leaf H):= (Refrain.visa H' D).injective.countable
   haveI : Countable (Elbow H M x'):= inferInstanceAs (Countable (Σ i:Refrain.Leaf H, Mosaic.Scene (brand M x') H i.val))
   exact ⟨(Countable.exists_injective_nat (Elbow H M x')).choose,(Countable.exists_injective_nat (Elbow H M x')).choose_spec⟩
local notation "Ω" => funnel H M x' H' D
local notation "Tt" => Elbow H M x'
local notation "Ψ" => stuff Ω (badge H M x' H' D)
set_option quotPrecheck false
local notation "Σ₁" p:max => Mosaic.parade Vx H χ ((p).fst).val (p).snd
local notation "Σ₂" p:max => Mosaic.parade Vy H χ ((p).fst).val (p).snd

def kettle : Yard ι α G c:= ⟨fun i=>(VB).forced (Ψ i),stuff Ω (fun p:Tt=> (Σ₁ p).letters),fun y=>stuff Ω (fun p:Tt=> (Mosaic.parade (brand M y) H χ p.fst.val p.snd|>.emit Lt))⟩
local notation "K'" => kettle H χ M x' l Z δ H' D E₀ V₀
omit [Countable ι] in
lemma written (p:Elbow H M x'): (Σ₁ p).letters=(Σ₂ p).letters:=by
    have hh(i:H.Chapter)(w:Mosaic.Stone Vx H i): (panel Vx H χ i w).letters=(panel Vy H χ i w).letters:=by cases i<;>rfl
    exact Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl fun k _=> hh _ _)

def candle (S:StepData c f)(i:ι) : Support c:= (brand M x' i).crest.image S.ratio.parent
variable (Vq:Config G c)
lemma boils (p:Elbow H M x') : (K').song Z z y Vq (Ω p) = (Σ₂ p).paint Z (sits Z l δ) z Vq:=by unfold Yard.song kettle; dsimp only; rw [stuffed,stuffed,written H χ M x' y]; rfl
lemma cleared {i:ℕ}(he:i∉Set.range Ω) : (K').song Z z y Vq i=0:=by unfold Yard.song kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ he]; simp
lemma echo : ∀ i, Lane (Vy) H χ Z l δ z H' D Vq i=∑' j:{j // Ψ j=i},(K').song Z z y Vq j.val:=by
   intro i; unfold Lane; by_cases h:i∈ Set.range f'
   swap; · rw [Progress.DirectedRecipe.blank _ _ h]; symm; refine (tsum_congr (g:=fun _=> (0:Marker.Poly Jm)) ?_).trans (tsum_zero); rintro ⟨x,hx⟩; apply Flues.cleared; rintro ⟨j,rfl⟩; rw [stuffed] at hx; exact h ⟨j.fst,hx⟩
   obtain ⟨i,rfl⟩:=h; rw [stuffed]; let p:=f' i; let g : Serif.KEntry Vx H i ↪ {j // Ψ j=p}:= ⟨fun j=>⟨(Ω ⟨i,j⟩),stuffed ..⟩,fun j k H'=> Sigma.mk.inj_iff.mp ((Ω).injective (congr_arg Subtype.val H'))|>.2|> eq_of_heq⟩
   unfold haven; symm; refine transferred_sum g (fun j=> boils H χ M x' y l Z δ z H' D E₀ V₀ Vq _) (fun j hj=> cleared _ _ M x' y _ Z _ z H' D _ _ Vq ?_)
   obtain ⟨v,hv⟩:=j; rintro ⟨⟨⟨q,hq⟩,k⟩,rfl⟩; rw [stuffed] at hv; obtain rfl:= (f').injective hv; exact hj ⟨k,Subtype.ext rfl⟩
local notation "VQ" => candle M x' S
local notation "Σμ" => fun i:Elbow H M x'=> (VB).forced (badge H M x' H' D i)
include U
lemma aligned (hv:P'.threshold=Pressure.temp x): Yard.Sounds K' P' VQ:=by
   constructor
   · intro y; let U':= (K').manifest y; have he i := Mosaic.pan (brand M y) H χ F' H' D P' E₀ V₀ hv (i:Tt).fst i.snd
     have hf:= Refrain.qualified P' H' D χ E₀ V₀ hv
     refine ⟨?_,fun i=> hf.symtest (Ψ i), ?_, fun i=>hf.meas_test (Ψ i),?_, fun i=>hf.reads_test (Ψ i),?_⟩
     · intro i; by_cases hm:i∈Set.range Ω
       · obtain ⟨p,rfl⟩:=hm; unfold Yard.manifest kettle; dsimp only; rw [stuffed]; exact fun s U=> congr_arg (_*·) ((he p).2.1.2.2.1 s U)
       unfold Yard.manifest kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hm]; exact fun _ _=>rfl
     · intro i; by_cases hm:i∈Set.range Ω
       · obtain ⟨p,rfl⟩:=hm; unfold Yard.manifest kettle; dsimp only; rw [stuffed]; exact measurable_const.mul (he p|>.2.1.1)
       unfold Yard.manifest kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hm]; exact measurable_const
     · intro i; by_cases hm:i∈Set.range Ω
       · obtain ⟨p,rfl⟩:=hm; unfold Yard.manifest kettle; dsimp only; rw [stuffed,stuffed]; exact fun A B he' hp=>congr_arg (_*·) ((he p).2.1.2.1 A B he' hp)
       unfold Yard.manifest kettle; dsimp only; simp_rw [Progress.DirectedRecipe.blank Ω _ hm]; exact fun _ _ _ _=>rfl
     intro i v hi; by_cases hm:i∈Set.range Ω
     · obtain ⟨p,rfl⟩:=hm; change stuff Ω (fun p:Tt=>(Mosaic.parade (brand M y) H χ p.fst.val p.snd).emit Lt) (Ω p) _ ≠ 0 at hi; rw [stuffed] at hi; change ((VB).forced (Ψ (Ω p))).eligible _ _; rw [stuffed]; exact (he p).2.2 v (right_ne_zero_of_mul hi)
     exact False.elim (hi (by unfold Yard.manifest kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hm]; rfl))
   intro i y j hj V hv'
   by_cases hi:i∈Set.range Ω
   · obtain ⟨k,rfl⟩:=hi; change stuff Ω (fun p:Tt=>(Mosaic.parade (brand M y) H χ p.1.val p.2).emit Lt) (Ω k) _ ≠0 at hv'; unfold kettle at hj; dsimp only at hj
     rw [stuffed,written H χ M x' y] at hj; rw [stuffed] at hv'; unfold Yard.plane kettle; dsimp only; rw [stuffed]; exact (Mosaic.pan (brand M y) H χ F' H' D P' E₀ V₀ hv k.fst k.snd).2.1.2.2.2 j hj V (right_ne_zero_of_mul hv')
   exact False.elim (hv' (by unfold kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hi]; rfl))
end YM.RemainderComparison.Flues
