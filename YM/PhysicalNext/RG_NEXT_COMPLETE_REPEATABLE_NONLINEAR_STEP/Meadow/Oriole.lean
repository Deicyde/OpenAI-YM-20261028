import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Camp
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Rank
/-! # First bounded shell bills on retained (complementary to ALL rolls
 granted). Organic variable H cities across scales. Covariant S average secured.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
lemma ascetic (χ : Chi) (h : ∀ i U,R.activities.E i U=0) (i:ℕ) (y: Config G c): stream H χ y (Brim.icon H i)=0:= by
  rw [Brim.lily]; unfold March.leaflet Pond.likely Stained.fringe
  have he i U : R.activities.regularOccurrence R.p i U=0 := by simp only [Activities.regularOccurrence,masked,Set.indicator, h]; split<;> rfl
  have hx (F:Tree.Forest S.ratio) (Y:Coat T F) J z : Polar.floating Y o.a R W X.table z J X.halo (Brim.head i)=0 := by
    unfold Polar.floating Brim.head; rw [prod_singleton]; change Real.exp (-(R.activities.regularOccurrence _ i _) * _) -1= _; rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
  have hv (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y W o.a (Brim.head i) R X.table X.halo=0 := by
    unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hx,mul_zero,integral_zero,sum_const_zero]
    rfl
  change _ * ∑ x: Reserve S, (∫ z, Shield.shelter _ _ _ (Brim.head i) _ _ _ ∂ _) = _; simp only [hv,integral_zero,sum_const_zero,mul_zero]

section high
variable (X' : Match.Alliance I H 1 0) (hz:X'.units=Equiv.refl _) (hp:R.path=R'.path) (hV:I.supportP=H.supportP) (he : I.shapeW=H.shapeW)
   (p' : BudgetPoint) (hP:p'.threshold= Pressure.temp p) (ht:p'.B=radiusB p)

-- selected independent of Kin coupling labels when used along career
-- ∀β finite. Shapes on I *BEFORE* H orientation

def keep (I : Cash W p a L₀ X o U T R') (i: Magazine I): Prop:= i.elim (fun i=>i∉Set.range (booths I)) (fun i=> B< arc T.down i)
def tower (γ : ℝ) (i:Magazine I): Config G c→ℝ:= if Meadow.keep I i then opus I X' χ γ i else 0

def Budget {G : Gauge} {c:Side} {A:Type} (P : BudgetPoint) (X : A→RegularAddress c) (f : A→ Config G c→ℝ) (k:ℝ):= ∃ w: A→ ℝ, Quotes.early P X w k ∧ ∀ i,P.Regular (X i).support (f i) ∧ P.supBounds (X i).site (X i).support (f i) (w i)
include hp hz hV
lemma censored {i : I.fragrances} (h : ¬ Beam.lit H (X'.furrow i)) (γ : ℝ) : Meadow.tower X' (χ:=χ) γ (.inl i)=0 := by
  unfold Meadow.tower; split
  next he =>
    have ht V: stream H χ V (X'.furrow i)=0:= by
      by_contra hv; have hy:= Meadow.remnants _ h V hv; exact he ((holdings X' hp.symm hz hV _).2 hy)
    ext U; change (-1:ℝ)* stream H χ U _= _; rw [ht,mul_zero]; rfl
  rfl
omit hp hz hV
-- path budget sharp. use Put ∆ always.
include ht
lemma tone (δ b : ℝ) {k v u : ℝ} (γ:ℝ) (h : T.down.Bounds T.low k v u) (he : WilsonStartup.Decent T.low p') (hs: preExponent p'/p'.B≤ k/4) (hb : Real.exp (-(k/4)*p'.B)*Song.octaveNeed G p' T.low k v u R.beta γ ≤ b) (hP : Meadow.Budget p' (Beam.dashboard I) (fun i:I.fragrances=> Meadow.tower X' (χ:=χ) γ (.inl i)) δ):
    Meadow.Budget p' (Beam.contents I p') (Meadow.tower X' (χ:=χ) γ) (δ+b) := by
  obtain ⟨f,hF,hV⟩:= hP; obtain ⟨k',hK,hP⟩:= Meadow.lent (c:=c) p' _ _ _ γ h he hs
  have hz z:0≤k' z:=(hP z).2.1; let z i:= if B < arc T.down i then k' i else 0
  let K: Magazine I→ℝ:= Sum.elim f z; have hv i : 0 ≤ z i:= by unfold z; split; exact hz _; exact le_rfl
  refine ⟨K,fun x=>Cost.sum (hF x) (show SumBudget _ b from ?_),?_⟩
  · rw [ht] at hb
    have ht:= Meadow.arch_tail (strings T.down p') p' (arc T.down (c:=c)) hK (k:=B) (by have h:= h.width; positivity) hz x
    refine budget_loosen (budget_mono ht (fun i=> ?_) (fun i=> ?_)) hb
    · split; next h=> exact mul_nonneg (hv _) (Real.exp_nonneg _)
      exact le_rfl
    ·
      by_cases he: B< arc T.down i
      · dsimp only [Beam.contents,K]; simp_rw [Sum.elim_inr,z,if_pos he,if_pos he.le]; exact le_rfl
      dsimp only [Beam.contents,K,Sum.elim]; unfold z; rw [if_neg he]; split
      next h=> rw [zero_mul]; split_ifs <;> first | exact mul_nonneg (hz _) (Real.exp_nonneg _)| simp
      exact le_rfl
  intro i; rcases i with i|i
  · exact hV i
  unfold Meadow.tower; split; next h=> rw [show K (.inr i)=_ from (if_pos h : z i=k' i)]; exact hP i
  next h=> rw [show K (.inr i)=_ from (if_neg h : z i=0)]; exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p') (X:=(strings T.down p' i).support) (o:=(strings T.down p' i).site) 0)⟩
end high
end YM.PhysicalNext.Repeat.Meadow
