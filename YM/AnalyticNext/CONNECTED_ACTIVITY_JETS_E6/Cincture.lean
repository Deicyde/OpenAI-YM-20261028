import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hallmark
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Street

/-!
# Extension carries state locally even at stencil positions with missing Grant

Manifest still read for value estimates even on angular covariance. Inside
selected F(X).price store, all chosen in ONE k. Off domain keep raw algebra;
no claim on outside Room. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush  Frond  Scroll
variable {v z r Q s : ℝ} {j : ℕ} {U : E → Config G c} {x : E}

namespace Vine
variable (X : Coat T F)

def strain (s : Signed) (p : Rod c f) (u : Directions G f) := Scroll.freely T X.x (pull s 0 X.V) (choice s X.k) p +
    orientedRow T X.R s p X.V (X.signal u)
def bar (u : Directions G f) (p : Mention c f) := if X.selected p.1 (spot S p.2) then
    Coat.scale • strain X p.1 p.2 u else 0
def pot (s : Signed) (p : Rod c f) (u : Directions G f) := if X.selected s (spot S p) then ‖strain X s p u‖^2/2 else 0

def costs (u : Directions G f) (s : Signed) (p : Spot c f) := ∑ i∈ parents p,pot X s i u

def leanB := X.form.transpose *ᵥ stand (bar X 0)
def well := -(X.kernelA.transpose *ᵥ leanB X)
def voltage := erect G (well X)
def shimmer (β : ℝ) := -(gStep β)⁻¹ • (X.plate *ᵥ well X+leanB X)
def worldZ (β : ℝ) (z : Air f G) := voltage X+gStep β • X.atmos z

lemma safe_hull (hp : X.manifest) (s : Signed) (i : Rod c f) (h : X.selected s (spot S i)) :
    Clean (pull s 0 X.V) X.x (focus S i) (radiusB X.x) := by
  unfold selected addr at h; rw [← cost_is_here] at h; apply Clean.turn
  apply (clean_far X.seeds X.V hp h).shrink; rw [separation_self,zero_add]; change X.B ≤ _; omega

variable (p : Room P S T X.x) (hV : X.manifest)
include p hV
lemma strains (u : Directions G f) (s : Signed) (i : Rod c f) (h : X.selected s (spot S i)) : X.realPath s i u=strain X s i u := by
  unfold strain realPath request Scroll.freely; rw [Scroll.frameCost p i ((safe_hull X hV s i h).shrink (by rw [separation_self]; omega))]
lemma warms (u : Directions G f) (s i) : X.surcharge s i u=pot X s i u := by
  unfold surcharge pot; split
  next h=> rw [strains X p hV u s i h]
  next h => rfl
lemma pricingP : X.linearBill=leanB X := by
  suffices he : X.priced 0=bar X 0 by rw [linearBill,he]; rfl
  funext i; unfold Coat.priced bar; split
  next ht => rw [strains X p hV 0 i.1 i.2 ht]
  next => rfl
lemma agrees_all : X.μ=voltage X := by unfold Coat.μ driftM voltage well; rw [pricingP X p hV]
lemma shines (β : ℝ) : X.hatted β=shimmer X β := by unfold hatted shimmer driftM well; rw [pricingP X p hV]
lemma shine (β : ℝ) (z : Air f G) : X.liftA β z = worldZ X β z := by unfold liftA worldZ; rw [agrees_all X p hV]

omit p hV in
lemma displacement_pay (s : Signed) (i : Bond f) (η r : ℝ) {V : E→ Directions G f} (h : Mode U x j z)
    (hp : Brush j η r (fun k=> V k (Channel.edge s i)) x) : Brush j (royalty G*(η*royalty G)) (z+r+z)
      (fun k=> displacement s (V k) (replica S.ratio (U k)) i) x := by
  unfold displacement; split_ifs
  next he => exact (Blaze.decorate (g:=fun k=> (replica S.ratio (U k) (edge s i))⁻¹) (Blaze.reverse
    (f:=fun k=> replica S.ratio (U k) (edge s i)) (Blaze.recopy S h.atLink _)) hp).opposite
  apply hp.climb 
  · have he:= hp.nonneg; have hc:=royalty_ge G; exact (le_mul_of_one_le_right he hc).trans (le_mul_of_one_le_left (by positivity) hc)
  linarith [h.pos]

omit p hV X
lemma signals (G : Gauge) (L : Side) (W γ K : ℝ) (j : ℕ) (χ : Chi) {v : ℝ→ℝ} (h : Rate G L (-(1/2)) v) :
    ∃ C, Rate G L (-(1/2)) C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Forest S.ratio) (X : Coat T F) (U:E→Config G c) (y : E),
      X.χ=χ → X.x=x → X.width=K → Mode U y j (v x) → ∀ i : Bond f, Brush j (|C x|) 1 (fun z=> (vary X (U z)).saved i) y := by
  obtain ⟨C,hC,hp⟩:= jewelled G L χ (K:=K) γ j h
  refine ⟨C,hC,hp.mono ?_⟩
  intro x hx c f S T hS hL E _ _ F X U y hX ht hw hY i
  let Z := K*Pressure.fiery G x L
  have hv : ((vary X (U y)).t)=Pressure.fiery G x L := by change X.t= _; unfold Coat.t; rw [ht,hS]
  have hk : Reliable G Z γ := by unfold Z; rw [← hS]; exact hL.log
  by_cases he:i ∈ F.trunks ∨ X.Hot i
  · rw [show (fun z=> (vary X (U z)).saved i)=(fun z:E=> (0:G.Color)) from funext fun z=> (if_pos he)]
    exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  let V z := F.drape X.Y i*(replica S.ratio (U z) i)⁻¹
  have hb: Brush j (royalty G) (v x) (G.mat ∘ V) y := by
    have hh := offsetB (Blaze.reverse (f:=fun t=> replica S.ratio (U t) i) (Blaze.recopy S hY.atLink i)) (F.drape X.Y i) 1
    simpa only [mul_one] using! hh
  have heq i' : (vary X (U i')).saved i=cutLog χ Z (V i') := by
    unfold Coat.saved; rw [if_neg (show ¬(i∈F.trunks ∨ (vary X (U i')).Hot i) from he)]; change cutLog X.χ (X.width*X.t) _=_
    rw [hX, hw, show X.t=_ from hv]; rfl
  simp_rw [heq]; exact hx _ V _ hb hk
end Vine
end YM.ConnectedActivityE6.Blaze
