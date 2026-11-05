import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Press
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Score

/-!
# Movement and mean at the displayed coordinates

Score producer from actual bought marginal prices and this mean, with
explicit inverse physical widths per normalization. Notice the
factor t' available from `Press` before such a conversion. Reanchoring
powers through `expenditure`. Do not treat held displacement's mean from
some other view as a constant. Purchases written also to allow marks through
every order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.SectorChange
  Next.SectorChange.Gaussian Next.SectorChange.Rows YM.Push.SectorMeasure
  YM.Next.Foundations Precision MeasureTheory Metric Curtain
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

section units
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Gauge} {c : Side} {D : Directions G c → Prop} {U : Config G c} {f : Config G c → E} {w r : ℝ} {k : ℕ}

lemma Ticket.indiv (h : Ticket D k U w r f) (p : ℝ) : Ticket D k U (‖p‖*w) r (fun x => p • f x) := by
  let L := p • ContinuousLinearMap.id ℝ E
  apply (h.linear L).mono _ le_rfl
  apply mul_le_mul_of_nonneg_right _ h.price_nonneg
  apply ContinuousLinearMap.opNorm_le_bound L (norm_nonneg _)
  exact fun i => le_of_eq (norm_smul p i)

lemma Charge.indiv (h : Charge D k U r f) (p : ℝ) : Charge D k U (max 1 ‖p‖*r) (fun x => p • f x) := by
  let L := p • ContinuousLinearMap.id ℝ E
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth,mul_nonneg (le_trans (norm_nonneg p) (le_max_right ..)) h.nonneg,fun l hl hi he => ?_⟩
  erw [show leftDerivs _ l U=L (leftDerivs f l U) from linear_parts L h.smooth hi,mul_pow]
  change ‖p • leftDerivs f l U‖ ≤ _; rw [norm_smul]
  have ht := pow_le_pow_right₀ (le_max_left 1 ‖p‖) (show 1 ≤ l.length from List.length_pos_iff.mpr hl)
  exact mul_le_mul (le_trans (le_max_right 1 ‖p‖) (by simpa using ht)) (h.price l hl hi he) (norm_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_left ..)) _)

lemma Charge.left_neg (h : Charge D k U r f) : Charge D k U r (-f) := by
  have hi := h.indiv (-1)
  simp only [norm_neg,norm_one,max_self,one_mul, neg_smul,one_smul] at hi; exact hi

lemma Charge.with_one (h : Charge D k U r f) (he : ‖f U‖ ≤ w) (hw : 1 ≤ w) : Ticket D k U w r f := by
  refine ⟨h.smooth, zero_le_one.trans hw,h.nonneg,fun l hl hi => ?_⟩
  by_cases hm : l=[]
  · subst l; simpa [leftDerivs]
  exact (h.price l hm hl hi).trans (le_mul_of_one_le_left (pow_nonneg h.nonneg _) hw)
end units

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u u' : Spot d}
    {H R K : Type} {X X' : Support c} {l : Viewport u X H R K} {l' : Viewport u' X' H R K}
    [Fintype H] [Fintype R] {k : ℕ} {O : ℝ}

namespace Notice

variable (a : Notice l) (p : Reel G H R K)

def powder (V : Config G c) (p : Display G H R K) : LogArray G (H⊕R) := tape (a.m V p.1 + d.g • p.2)

lemma powder_arranged (V : Config G c) (h : u.Clearing V) (P : Spot.Visual u) (i:H⊕R) :
    a.powder V (l.info P) i = displaced (u.m V P.1) d.g P.2 (l.read i) := by
  unfold powder Viewport.info; rw [a.arrive V _ h]; rfl





def harvested (i : H) (j : G.ColorIndex) (V : Config G c) := a.m V p.1 (.inl i,j)




lemma hailed (i : H) (j : G.ColorIndex) : a.movement p (.inl i,j)=fun V =>
    d.g⁻¹ • (pressing l p V i j - a.harvested p i j V) := rfl
lemma vacated (i : R) (j : G.ColorIndex) : a.movement p (.inr i,j)=fun _ => p.2.1 (i,j) := rfl

-- Can also use a single block comparison in Euclidean norm.
def term (G : Gauge) (i : G.ColorIndex) : G.Color →L[ℝ] ℝ :=
  ((EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis.coord i).toContinuousLinearMap
lemma translated (i : G.ColorIndex) (x : G.Color) : term G i x=x i := by simp [term]

variable {p}


-- `z=a.imprint V p` uses no surcharge; also compare using the
-- other's imprint with error allowance. Must choose actual paid mean Log
-- directions.





end Notice
end YM.AnalyticBridge.LocalGaussian
