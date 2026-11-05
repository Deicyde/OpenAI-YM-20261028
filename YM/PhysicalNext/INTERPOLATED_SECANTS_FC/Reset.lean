import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Fuses
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Comparison
import YM.Next.ROTATIONS.Response
import YM.Next.UV_STRESS.Fringe
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Forced
import YM.Push.COMMON_WITNESSES.Fields



/-!
# Secants through the actual VerifiedReset conversion

NO multiplying by volume in the comparison of affine readings. Full proposed order (p.order)
earned at true addresses; never discard the portion of the drawer not reached by any nonzero
application in a sector. Even through the final indicator and orientation mergers. No change
with test dial on this particular template (`ledger`). These results use the early-assembly
estimates to be supplied at the same x,y; see subsequent modules for that business.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Function Filter Set Lattice Wilson RG Ovens AnalyticBridge.VerifiedReset
  Collection Averaging Progress.DirectedRecipe Push.AbsoluteSums AnalyticBridge.BranchTuning
open Extra.Iteration (numbering Cost.equiv Cost.nonneg)
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Listing G n} {c : Clip} {R : PathData G}
variable {a b : Collection.Source G n} {σ C Λ α H w D μ : ℝ}

structure Unmasked (X : Listing G n) (p : BudgetPoint) (v : Collection.Source G n) (H : ℝ) : Prop where
  smooth i : p.Regular (X.reg i).support (v.logRead i)
  cheap : ∃ u, (∀ i, p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i)) ∧ Quotes.early p X.reg u H

/-- The EARLY purchases needed here; D is the relative incoming displacement, even when zero.
No regular or address bill here supposes affine Hessian already reset. -/
structure Receipts (X : Listing G n) (p : BudgetPoint) (a b : Collection.Source G n) (H w D μ : ℝ) : Prop where
  first : Unmasked X p a H
  second : Unmasked X p b H
  logs : (roots X.reg p.B (Quotes.preExponent p)).Box (fun i (u : Reading G p (X.reg i)) =>
    u.jet (a.logRead i)-u.jet (b.logRead i)) (D*μ)
  hard : ∃ e, (∀ i U, Both D (e i) (a.hardRead i U) (b.hardRead i U)) ∧
    Ac.Hit (fun i => (X.hard i).support) p.B e (p.supportExponent+1) w

section Items


lemma byte {v : Collection.Source G n} {M : ℝ} (hs : ∀ i, p.Regular (X.reg i).support (v.logRead i)) {u : ℕ → ℝ}
    (hu : ∀ i,p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i)) (hh : Quotes.early p X.reg u M) : Projects (X.read v) p M :=
  ⟨hs,u,hu,Quotes.segment _ (fun i => (hu i).1) hh⟩

lemma Unmasked.projects (h : Unmasked X p a H) : Projects (X.read a) p H := by obtain ⟨u,he,hu⟩ := h.cheap; exact byte h.smooth he hu


private lemma extend_regular {Y : Pipes G n} {v w : Tap G n} {S : ℝ} (h : RegularDrift p p.order (Y.pours v) (Y.pours w) S) :
    RegularDrift p p.order ((drawer G n).pours (Rack.widen Y v)) ((drawer G n).pours (Rack.widen Y w)) S := by
  obtain ⟨k,hk,h⟩ := h.receipt; let t := Rack.upE Y
  refine ⟨rfl,stuff t k,fun i => ⟨Rack.positive _ _ (fun i=> (hk i).1) _,fun U hU L hL hd => ?_⟩,fun o => transfer_budget t ?_ ?_ (h o)⟩
  · change ‖leftDerivs (stuff t v.regular i) L U - leftDerivs (stuff t w.regular i) L U‖ ≤ _
    by_cases he : i ∈ range t
    · obtain ⟨i,rfl⟩ := he; rw [stuffed,stuffed,stuffed]
      dsimp only [Pipes.pours,t] at hU hd
      rw [Rack.reg_up Y i] at hU hd
      exact (hk i).2 U hU L hL hd
    rw [blank _ _ he,blank _ _ he,blank _ _ he,sub_self,norm_zero]
  · intro i; simp only [Pipes.pours, t, Rack.reg_up, stuffed]
  intro i hi; rw [blank _ _ hi]; simp [BudgetPoint.mass]

lemma extend_assets {Y : Pipes G n} {v w : Tap G n} {D κ u : ℝ} (h : Assets Y p v w D κ u) :
    Assets (drawer G n) p (Rack.widen Y v) (Rack.widen Y w) D κ u := by
  obtain ⟨b,hb,he,H⟩ := h.certificate; let t := Rack.up Y
  refine ⟨h.delta_nonneg,h.linear,h.mass,h.margin,stuff t b,Rack.positive t b hb,Rack.hits Y _ _ _ _ he,fun i U => ?_⟩
  by_cases hi : i ∈ range t
  · obtain ⟨i,rfl⟩ := hi
    rw [stuffed]; change ‖Pipes.reach _ (Rack.up Y i) U‖ ≤ _ ∧ _
    simp_rw [t, Rack.same_atom]; cases i <;> exact H _ _
  simp_rw [Rack.zero_atom Y v i U hi,Rack.zero_atom Y w i U hi,blank t b hi]; simp
end Items

namespace Receipts
variable (g : G.Simple) (hv : Receipts X p a b H w D μ) (hx : R.Bounds c σ C Λ) (hc : WilsonStartup.Decent c p) (hw : Geo.Width p c σ)
  (α : ℝ)
include hv
lemma log_book : ∃ e, (∀ i, p.supBounds (X.reg i).site (X.reg i).support ((a-b).logRead i) (e i)) ∧ Quotes.early p X.reg e (D*μ) := by
  obtain ⟨e,he,H'⟩ := hv.logs
  exact ⟨e,fun i => (AnalyticBridge.VerifiedReset.sup_varies (hv.first.smooth i) (hv.second.smooth i)).1 ⟨he.positive i,fun U ht l hl h => H' i ⟨U,ht,l,hl,h⟩⟩,
    (seated_iff.mp he).2⟩


include g in
lemma referenced : p.threshold^2 * |delta (X.read a) - delta (X.read b)| ≤ D * μ := by
  obtain ⟨e,hu,he⟩ := hv.log_book
  convert delta_bound g (byte (fun i => reg_sub (hv.first.smooth i) (hv.second.smooth i)) hu he) using 3
  unfold delta Averaging.total; rw [← (hv.first.projects.seriesAt g ..).tsum_sub (hv.second.projects.seriesAt g ..)]
  refine tsum_congr (fun i => ?_); unfold censusAt; dsimp only [Listing.read]; split
  · exact (projection_sub _ (hv.first.smooth i) (hv.second.smooth i) ..).symm
  ring
include g hx hc


omit hv g hx hc in
lemma pack_regular {f : ℕ→ℝ} {Y : Pipes G n} {v w : Tap G n} {M : ℝ} (h : ∀ i,Shoot.variesRegular p (Y.reg i) (v.regular i) (w.regular i) (f i))
    (hp : Quotes.anchored p Y.reg f M) : RegularDrift p p.order (Y.pours v) (Y.pours w) M := ⟨rfl,f,h,hp⟩

include hw

omit hv in
private lemma soft_side {v : Collection.Source G n} (ht : Unmasked X p v H) : ∃ e, Ac.Hit (shelves X R p).softer
    p.B e (p.supportExponent+1) (softNeed G p c σ C α H) ∧ ∀ i U, ‖(branch X R c p v α).logarithm i U‖ ≤ e i := by
  obtain ⟨u,hU,hu⟩ := ht.cheap; let Δ := delta (X.read v); let t := numbering (LKey n)
  have h := (Local.quote_family hx hc hw α Δ hU hu (delta_bound g ht.projects)).2
  exact ⟨(quoteL R p c α Δ u) ∘ t, fun x => Cost.equiv _ (h x),fun i U => Local.quote_soft g α Δ hU ht.smooth (t i) U⟩

omit g hx hc hw hv in
lemma soft_nonneg (u : ℝ) (hμ : 0 ≤ u) (hp : 0 < σ) (hc : 0 ≤ C) : 0 ≤ softNeed G p c σ C α u := by
  have := (budget_pos p G c hp hc).2.2
  have := p.threshold_pos
  have := pair_nonneg G p
  have := Residual.loss_pos G p
  have := Real.exp_le_one_iff.mpr (by norm_num : -(1:ℝ) ≤ 0)
  unfold softNeed hitNeed Quotes.softReset Footprint.payment Footprint.degreeIncome
  have hz : 0 ≤ 1 - Real.exp (-1) := by linarith
  positivity
def share (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C α H μ : ℝ) := softNeed G p c σ C 0 μ + (softNeed G p c σ C α H + softNeed G p c σ C α H)

def recon (w f gold : ℝ) := 2*(Real.exp gold*w + Real.exp 1*f)



omit g hv hx hc hw in
private theorem assess {Y : Pipes G n} {a b : Tap G n} {gold μ : ℝ} (he : RegularDrift p p.order (Y.pours a) (Y.pours b) H)
    (hv : Assets Y p a b D gold μ) (R : PathData G) (c : Clip) :
    let F a := (finish R c p Y a 0 0).activities
    Slew p p.order (F a) (F b) H (D * Bid.quote gold μ) := by
  intro F; obtain ⟨-,e,he,H⟩ := extend_regular he
  exact ⟨⟨rfl,e,he,H⟩, pays_fused (folio G n) (extend_assets hv)⟩


end Receipts
end YM.PhysicalNext.InterpolatedSecantsFc
