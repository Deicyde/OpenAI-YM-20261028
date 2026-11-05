import YM.Next.UV_STRESS.Granular
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Oriole
import YM.ProjectorNext.EQUATION_CAMPAIGN.Class
import YM.Push.FINITE_DETECTION.Equivariance
/-! # Towers for real and seedless budgets met AFTER canonical recalibrations
    Use pointwise vouchers (emit exact Π heights from Ξ). Does not transform masks yet.
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
variable (X' : Match.Alliance I H 1 0) (hz:X'.units=Equiv.refl _) (hp:R.path=R'.path)
  (ha:R'.activities.reg=R.activities.reg) (hk:R'.activities.forced=R.activities.forced)
   (p' : BudgetPoint) (hP:p'.threshold=Pressure.temp p) (ht:p'.B=radiusB p) (γ:ℝ)
lemma emptyFree {ι:Type} (P:ι→RegularAddress c) (p:BudgetPoint) {u: ι→ Config G c→ℝ} {t:ℝ} (h : Meadow.Budget p P u t) (v:ι→ Config G c→ℝ) (he : ∀ i,u i=v i ∨ v i=0) : Meadow.Budget p P v t:= by
  obtain ⟨f,hf,hP⟩:= h; refine ⟨f,hf,?_⟩; intro i; rcases he i with hi|hi
  · rw [← hi]; exact hP i
  rw [hi]; refine ⟨CouplingShape.reg_const _,?_⟩; exact VerifiedReset.sup_le (CouplingShape.sup_const _) ((abs_zero).trans_le (hP i|>.2.1))
variable {C' d v Y A b r B' q x n' e : ℝ} {k n : ℕ} (N:Captain H j C' d v Y A b r B' q k χ)
include X' hp ha hk hz p' hP ht N
lemma vintageB (hw:p'.order≤j) (hv:p'.power ≤ n) (hr:preExponent p'≤e) (hQ: Ac.Hit (Captain.reachability (H:=H)) (radiusB p) (fun z=> if tired H z then N.markΦ z n else 0) e n') :
    let D i:=if tired I i then Song.sequence I X' χ i else 0
    Meadow.Budget p' (Beam.dashboard I) D n' := by
  intro D
  let f i:= if tired I i then N.markΦ (X'.furrow i) n else 0
  have h i : p'.Regular (Beam.dashboard I i).support (D i) ∧ p'.supBounds (Beam.dashboard I i).site (Beam.dashboard I i).support (D i) (f i):= by
    unfold D f; split
    · have hk:= N.gloryBudget (X'.furrow i) p' hP hw
      rw [Beam.see, reconnects I X' i]; have Hz:= CouplingShape.sup_scale (-1) (hk.2.2 n hv _ (show _ from ((Beam.see I i).trans (reconnects I X' _)) ▸ (Beam.dashboard I i).anchor)); rw [abs_neg,abs_one,one_mul] at Hz
      exact ⟨CouplingShape.reg_scale _ hk.2.1,Hz⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p') (X:=(Beam.dashboard I i).support) (o:=(Beam.dashboard I i).site) 0)⟩
  refine ⟨f,fun x=> ?_,h⟩
  have hv := budget_pull X'.furrow X'.furrow.injective (hQ x); refine budget_mono hv (fun i=> ?_) (fun i=>?_)
  · split; next h'=> exact mul_nonneg (h i|>.2.1) (Real.exp_nonneg _)
    exact le_rfl
  dsimp only; split
  next he =>
    let K:= X'.furrow i; have hu : Captain.reachability K=(Beam.dashboard I i).support:= Eq.symm ((Beam.see ..).trans (reconnects I X' i)); rw [if_pos (show x∈Captain.reachability K from he ▸ (show _ from hu.symm ▸ (Beam.dashboard I i).anchor))]; have hh : f i=(if tired H K then N.markΦ K n else 0) := by unfold f; rw [stilled X' hz (hp:=hp.symm) (hα:=ha) (hA:=hk)]
    rw [← hu,ht, ← hh]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _))) (h i|>.2.1)
  exact hv.1 i
omit hP ht N p'
include γ
lemma suppressed (he:∀ i U,R.activities.E i U=0) (i:I.fragrances) : (if tired I i then Song.sequence I X' χ i else 0)= tower X' (χ:=χ) γ (.inl i) ∨ tower X' (χ:=χ) γ (.inl i)=0 := by
  have hh: I.supportP=H.supportP:= Match.same_area hp.symm ha hk
  by_cases h:tired I i
  · unfold Meadow.tower; rw [if_pos h]; split
    · exact Or.inl rfl
    exact Or.inr rfl
  by_cases hv: Beam.lit H (X'.furrow i)
  · rcases hv with hu|⟨k,ht'⟩; exact False.elim (h ((stilled X' hz (hp:=hp.symm) (hα:=ha) (hA:=hk) i).2 hu))
    right; unfold tower; split; next hh=>
      ext U; change (-1:ℝ)* stream H χ U (X'.furrow i)= (0:ℝ); rw [← ht', ascetic χ he k U, mul_zero]
    rfl
  exact Or.inr (censored X' hz hp hh hv γ)
omit γ
section real
variable (δ w θ : ℝ) (hL: Collection.Local (Beam.marquee I p') p' (Height.serve I X' χ (Beam.lit I)) δ w)
include p' hL γ
lemma realB : Meadow.Budget p' (Beam.marquee I p').reg (choir (fun i=> if Meadow.keep I i ∧ (∃ z, i=Sum.inl z) then opus I X' χ γ i else 0) ∘pennant I) δ:= by
  obtain ⟨f,h,hF⟩:= hL.cheap; refine emptyFree _ p' (u:=fun i=>(Height.serve I X' χ (Beam.lit I)|>.logRead i)) ⟨f,hF,fun i=> ⟨hL.smooth i,h i⟩⟩ _ fun i=> ?_
  let e (v):= if Meadow.keep I v∧ (∃ z,v=Sum.inl z) then opus I X' χ γ v else 0
  let u:= pennant I i; by_cases Ht: Meadow.keep I u.2 ∧ ∃ z,u.2=.inl z
  · have hz₀:=Ht
    obtain ⟨y,hy⟩:= Ht.2; have Ht : Meadow.keep I (.inl y):=hy ▸ Ht.1
    by_cases hp' : Beam.lit I y
    · rw [(Height.bolted I _ χ (Beam.lit I) γ i).1,if_pos (show Height.chosen _ _ _ from (by
        change Height.chosen _ _ u.2; rw [hy]; exact hp'))]
      left; change Rim c • (opus I X' χ γ u.2 ∘ u.1.view)=Rim c • (e u.2 ∘ u.1.view); unfold e; rw [if_pos hz₀]
    right
    have hv:¬Beam.lit H (X'.furrow y):= fun h=> hp' (by
      rcases h with h| ⟨q,h⟩; · exact Or.inl ((stilled X' hz (hp:=hp.symm) (hα:=ha) (hA:=hk) y).2 h)
      exact Or.inr ⟨q,X'.furrow.injective ((Beam.mimics I X' hz q).trans h)⟩)
    have he : e u.2=0:= by unfold e; rw [if_pos hz₀,hy, ← (if_pos Ht : tower X' γ (.inl y) (χ:=χ) = opus I X' χ γ (.inl y))]; exact censored X' hz hp (Match.same_area hp.symm ha hk) hv γ
    change Rim c • (e u.2 ∘ u.1.view)=0; rw [he]; ext; simp
  right; change Rim c • (e u.2 ∘ u.1.view)=0; unfold e; rw [if_neg Ht]; ext; simp
end real
end YM.PhysicalNext.Repeat.Meadow
