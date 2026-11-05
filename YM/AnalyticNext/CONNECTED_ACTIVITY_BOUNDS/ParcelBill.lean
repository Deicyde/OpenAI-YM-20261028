import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Lap
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.LogNormalize
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Warsaw


/-!
# Diagonal log (one flow, compared to same-tags reference)

These are complete color-block traces. Flow requires no extension near
the rough V off its windows. From , local j=0 occurrence plus
its live activity valuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Mint Laps
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}








variable {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- price one log exponent item in signed terms

def letter (S : StepData c f) (x : ℝ) (M : Matrix (Vars G f) (Vars G f) ℝ) (i : Bond f) (t : ℝ) :=
    trace (sectionOf (ledger (eyes S G (radiusB x)) M 0 t) i i)

def flatReference (T : Tube G S) (x : ℝ) (F : Forest S.ratio) := gram T F x (blank S) 1

-- sign as in the integrand exponent (negative trace)
def paired (Y : Mint T F A x) (i : Bond f) := (∫ t in (0:ℝ)..1,
    letter S x (flatReference T x F) i t - letter S x Y.sheet i t)/2



lemma magnitude {q : Promise} {r : Turns} (hb : r.exp_width ≤ q.alpha) (M : Matrix (Vars G f) (Vars G f) ℝ)
    (x : ℝ) (hA : Served q M (dcol S)) (he : r.Takes (eyes S G (radiusB x)) M (dcol S) (paceR x)) (k : Bond f)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : |letter S x M k t| ≤ (Fintype.card G.ColorIndex:ℝ)*((q.mass+1)*r.base) := by
  unfold letter Matrix.trace; apply le_trans (abs_sum_le_sum_abs ..)
  have h i : |ledger (eyes S G (radiusB x)) M 0 t i i| ≤ (q.mass+1)*r.base := by
    simpa [Green.wt] using! row_entry (ledger_price (eyes S G (radiusB x)) hA hb he 0 t ht).1 i i
  exact ((Finset.sum_le_sum (s:=(univ:Finset G.ColorIndex)) (g:=fun _ => ((q.mass+1)*r.base))
    (fun i _ => h (k,i))).trans (by simp))

lemma fee (Y : Mint T F A x) {q : Promise} (g : Turns) (hi : g.exp_width ≤ q.alpha)
    (hA : Served q Y.sheet (dcol S)) (he : g.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x))
    (hb : Served q (flatReference T x F) (dcol S))
    (hf : g.Takes (eyes S G (radiusB x)) (flatReference T x F) (dcol S) (paceR x)) (k : Bond f) :
    |paired Y k| ≤ (Fintype.card G.ColorIndex:ℝ)*((q.mass+1)*g.base) := by
  let Z := (Fintype.card G.ColorIndex:ℝ)*((q.mass+1)*g.base)
  let p t := letter S x (flatReference T x F) k t - letter S x Y.sheet k t
  have h (t : ℝ) (ht : t∈Set.uIcc 0 1) : ‖p t‖ ≤ Z + Z := by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact (abs_sub ..).trans (add_le_add (magnitude hi _ x hb hf k _ ht) (magnitude hi _ x hA he _ _ ht))
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => h t (Set.uIoc_subset_uIcc ht))
  simp only [sub_zero,abs_one, mul_one, Real.norm_eq_abs] at hm
  change |(∫ x in (0:ℝ)..1,p x)/2| ≤ Z; rw [abs_div]; norm_num; linarith only [hm]




end YM.AnalyticNext.ConnectedActivity.Aff
