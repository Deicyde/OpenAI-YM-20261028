import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dispenser
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layout
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.TiltField
import YM.Push.BETA_TRANSPORT.Controlled
import YM.Push.BETA_TRANSPORT.Score
import YM.SectorNext.RECONNECTED_LOCALITY.Tremor


/-!
# Physical density receipt for the Rank comparison step

Not an assumption on the B valuation, final marked log, or most-likely
prior ratio.

A quantitative criterion on the **actual integrand**, sparse
compulsory + gas-free packets with areas/ticket stencils, ANY
V, jointly over A and Y/Ζ, by fine/coarse flag settings.

Uses *unmarked* data
only.

Areas fixed before masks arguments.

No expansion hypotheses including
W, H or even K alternatives.

Also quantitative Wares (pointwise
bound by tilt certificates that fit the hit rates).

We USE this to
derive the needed estimates on *marked* versions.

We go on in Opacity/
to prove such unmarked density expansions themselves (on the restarted
panels and hypotheses there).

Neither amounts
to proving vStep in E.

See REPORT for work/gaps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     SectorTools.PhysicalGaussianSwitch
     AnalyticBridge.LocalGaussianLaws Exterior AnalyticBridge.LocalGaussianLaws.Local
     Precision RG.Supply Tree Bid Push.SectorMeasure Next.Rank Tapes
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ y : ℝ} {F : Orchard S} {T : Tube G S} {A : Stores S} {P : Teller G}

/-- One material. Fixed extents V masks and up-flags sector.
Seed counts include flags via the configured chart. -/
structure Zest (G : Gauge) (S : StepData c f) (x : ℝ) (F : Orchard S) (τ : ℝ) where
  zone : Support c
  up : Support f
  down : Support c
  data : vouchers S
  weight : Shader G S x F ℂ
  key : (up.image S.ratio.parent) ⊆ zone
  sent : down ⊆ zone
  contains : wards data ⊆ zone
  selects : zone.Nonempty
  follows : Sees weight zone down.Nonempty τ
section
variable {R' : BudgetPoint} (R : Rep G f) (L : Lantern G S) {w : ℝ}
    (D : Allocation G S x w) {J : ChartRatio G} {ι : Type} [Fintype ι]

/-- Unscaled, exact Jacobian/C density on every positioned chart,
fine flag slice recorded too. -/
def BodyGrant (T : Tube G S) (R : Rep G f) (L : Lantern G S) (D : Allocation G S x w) (J : ChartRatio G)
    (τ : ℝ) (p : ι→ Zest G S x L.park τ) (Λ : Config G c→ℂ) :=
    ∀ (V : Config G c) A, Positioned x A V → ∀ k : Streak L.park, ∀ z : RoomView A x k.wood G, ∀ m : Support f,
       (if flags R.p.threshold (gazed T k.tag L.χ V x R.beta L.hood z)=m then spooled T L J D R.beta (fun U => (↑(Real.exp (R.exponent U)):ℂ)) A k V z else 0)=Λ V *
         ∑ t : Finset ι,
          if (t:Set ι).PairwiseDisjoint (fun i=>(p i).zone) ∧
             t.biUnion (fun i=>(p i).up)=m ∧ t.biUnion (fun i=>(p i).down)=flags τ V ∧
             A=stapled x (t.sup (fun i=> (p i).data)) V then ∏ i∈t,(p i).weight A k V z else 0
end
namespace Zest
variable (p : Zest G S x F τ)
-- inflation matches the actual output flags inventories. not per interaction.
def infl (r l : ℝ) := if p.down.Nonempty then r else l

/-- Pay per-key on singleton chart, allow localized tilt prices.
This is pointwise BEFORE held/frozen Z and Haar assembly at any tag. -/
def Wares (T : Tube G S) (r l v : ℝ) := 0 ≤ v ∧ ∀ (U : Config G c) (A : Stores S),
    p.zone ∩ flags τ U=p.down → A=stapled x p.data U → ∀ k : Streak F, ∃ L : Tilt.Plan (palette T A k.wood k.tag x U .endpoint),
       p.infl r l * Tilt.total L ≤ v ∧ ∀ y, ‖p.weight A k U y‖ ≤ Tilt.banner L y.2

lemma infl_one {r l} (hr : 1≤r) (hl : 1≤l) : 1≤ p.infl r l:= by unfold infl; split_ifs <;> assumption
lemma Wares.scale_down {r l v t} (he : Wares p T r l v) (hl : t≤l) : Wares p T r t v:= by
  refine ⟨he.1,fun U A hf hp k=>?_⟩; obtain ⟨D,hD,H⟩:=he.2 U A hf hp k
  have h : 0 ≤ Tilt.total D := Tilt.fractional D
  refine ⟨D,le_trans (mul_le_mul_of_nonneg_right ?_ h) hD,H⟩; unfold infl; split_ifs; exact le_rfl; exact hl

/-- Derive price in every expanded chart, not just singleton estimates
at a prior field. This uses the new density/tilted estimate -- cost
assumptions remain on the (unmarked) BEFORE-integral density. -/
lemma Wares.arise {r l v} (h : Wares p T r l v) (hr : 1≤r) (hl : 1≤l)
    (ht : Boosted T P x) (U : Config G c) (hp : Positioned x A U) (hf : p.zone ∩ flags τ U=p.down)
    (k : Streak F) (H : Nearby p.zone U U (stapled x p.data U) A k k):
    Integrable (p.weight A k U) (viewer T A x k.wood k.tag U) ∧
    p.infl r l * (∫ y, ‖p.weight A k U y‖ ∂viewer T A x k.wood k.tag U) ≤ v:= by
  let Q:=stapled x p.data U;let P':= palette T Q k.wood k.tag x U .endpoint; let μ :=viewer T Q x k.wood k.tag U
  obtain ⟨L,hL,h'⟩:=h.2 U Q hf rfl k
  let g:= p.weight Q k U
  have he: Integrable g μ ∧ p.infl r l*(∫ y, ‖g y‖ ∂μ)≤v:= by
    have hu:=position x p.data U; have hQ:P'.PosDef:= ht.fogged _ _ _ _ hu
    obtain ⟨h1,h2⟩:=Tilt.certified_earn hQ L
    have hm : MeasurePreserving Prod.snd μ (Gaussian.cloud P'):= measurePreserving_snd
    obtain ⟨hk,hv⟩:= pay_pull hm (Tilt.banner L) h1.aestronglyMeasurable
    let z (p : RoomView Q x k.wood G):= Tilt.banner L p.2
    have hx : Integrable z μ:= hk.mpr h1
    have hi : Integrable g μ:= hx.mono' ((p.follows.placed Q k).atLens hu).aestronglyMeasurable (Eventually.of_forall h')
    exact ⟨hi,(mul_le_mul_of_nonneg_left ((integral_mono hi.norm hx h').trans (hv.trans_le h2)) (zero_le_one.trans (p.infl_one hr hl))).trans hL⟩
  refine ⟨(integrate_beam p.follows ht (position ..) hp H (fun _=>rfl)).1.mp he.1,?_⟩
  exact (show _*_=p.infl r l * (∫ y, ‖g y‖ ∂μ) from congr_arg (p.infl r l * ·)
      (integrate_beam (p.follows.comp _ measurable_norm) ht (position ..) hp H (fun _=>rfl)).2.symm).trans_le he.2
end Zest
end YM.PhysicalNext.InteractingRank
