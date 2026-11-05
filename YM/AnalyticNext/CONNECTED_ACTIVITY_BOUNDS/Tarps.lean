import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Filaments
import YM.Push.RELAY_DIFFERENCE.Applications

/-!
# Removing cuff remainder as borne TERMS; inbound channels

Exact with actual arrays, no length uniform threshold claim here. Pinned budgets supply ℓ series both sides. Keep
principal factor at outgoing *full* chart energy, far off this construction too. Still uses ONE β not future β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths  Calls Mixed  
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x W : ℝ} {A : Stores S}
    {F : Forest S.ratio}

private lemma inners (R : ℕ→ G.Color) (h : Summable R) :
    HasSum (fun i : ℕ × ℕ => inner ℝ (R i.1) (R i.2)/2) (‖∑' i,R i‖^2/2) := by
  have hm : Summable (fun i : ℕ × ℕ => inner ℝ (R i.1) (R i.2)) := Summable.of_norm_bounded
    (summable_mul_of_summable_norm (f:=fun i => ‖R i‖) (g:=fun i => ‖R i‖) (summable_norm_iff.mpr (summable_norm_iff.mpr h)) (summable_norm_iff.mpr
      (summable_norm_iff.mpr h))) fun i => abs_real_inner_le_norm .. 
  let f := ∑' i, R i
  have ht v : (∑' i,inner ℝ v (R i)) = inner ℝ v f := ((innerSL ℝ v).map_tsum h).symm
  have hy : (∑' i : ℕ × ℕ, inner ℝ (R i.1) (R i.2)) = ‖f‖^2 := by
    rw [hm.tsum_prod]
    change (∑' i,∑' j,inner ℝ (R i) (R j))=‖f‖^2; simp_rw [ht]
    rw [show (∑' i,inner ℝ (R i) f)=∑' i,inner ℝ f (R i) from tsum_congr (fun i => real_inner_comm _ _),ht,real_inner_self_eq_norm_sq]
  exact hy ▸ hm.hasSum.div_const 2

lemma selvedge (R : PathData G) (a : Clip) (p : Cell f) (v d : ℕ) (U : Config G f) (m : BudgetPoint)
    {σ C Λ : ℝ} (h : R.Bounds a σ C Λ) : HasSum
    (fun i : ℕ × ℕ => drain R a p i.1 i.2 v d m.threshold U) (cuff R a m d v U p) := by
  let F i := R.ellTerms p i U; let r := shortenTerm R v d U p; let t := m.threshold
  have he : Summable F := (R.ell_dominated h p).summable U
  have ht : Summable r := by
    apply (summable_norm_iff.mpr he).of_norm_bounded
    intro i; unfold r shortenTerm; split
    · exact le_rfl
    rw [norm_zero]; exact norm_nonneg _
  by_cases h1 : PathData.kept a m.threshold p.1 U
  · have hk : cuff R a m d v U p = (‖∑' i,F i‖^2/2)-(‖∑' i,r i‖^2/2) := by
      unfold cuff PathData.baseTerm crown trunk; rw [if_pos h1,if_pos h1]; unfold shorten PathData.ell F r; abel
    rw [hk]; apply HasSum.congr_fun ((inners F he).sub (inners r ht))
    intro i
    by_cases hf : strip R p.2 v d i.1 <;> by_cases hg : strip R p.2 v d i.2 <;>
      dsimp only [strip] at hf hg <;> simp [drain, strip, h1,hf,hg,F,r,shortenTerm]
  simp only [cuff,PathData.baseTerm,crown,trunk,h1,drain,false_and,if_false,add_zero,zero_add,sub_self]; exact hasSum_zero

lemma favorite {α v : Type*} [Fintype α] (f : α × v → ℝ) {g : α → ℝ} (h : ∀ i, HasSum (fun j => f (i,j)) (g i)) :
    HasSum f (∑ i,g i) := by
  have he : Summable f := Summable.of_norm ((summable_prod_of_nonneg (f:=fun i => ‖f i‖) (fun i => norm_nonneg _)).mpr
    ⟨fun i => summable_norm_iff.mpr (h i).summable,(hasSum_fintype _).summable⟩)
  apply he.hasSum_iff.mpr
  rw [he.tsum_prod]; simp_rw [show ∀ i, _ from fun i => (h i).tsum_eq]; rw [tsum_fintype]

def veil_cuff (R : PathData G) (q : Clip) (m : BudgetPoint) (i d : ℕ) (U : Config G f) :=
    ∑ s : Signed, ∑ p, cuff R q m d i (pull s 0 U) p

lemma spool (R : PathData G) (a : Clip) (m : BudgetPoint) (i d : ℕ) (U : Config G f)
    {σ C Λ : ℝ} (h : R.Bounds a σ C Λ) : HasSum
    (fun p : Buttons f => chiffon R a p i d m.threshold U) (veil_cuff R a m i d U) := by
  unfold veil_cuff; refine favorite (α:=Signed) _ (fun s => ?_)
  rw [Fintype.sum_prod_type,sum_comm]; refine favorite (α:=PlaqAxes) _ (fun j => favorite (α:=Site f) _ (fun t => ?_))
  exact selvedge R a (t,j) i d (pull s 0 U) m h

-- candid exponents for restoration.





end YM.AnalyticNext.ConnectedActivity.Cab
