import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Merry
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Mohair
/-! # Poly product reliability charge. Fixed period summit after choosing Δ tolerance. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open AnalyticBridge VerifiedReset Quotes Extra.Iteration
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {Pt : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G Pt} {o : Target.Order G W} {R I : RG.Rep G f} {P : Facing R I}
    {p μ C v M d r D K' : ℝ} {i : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} (Ξ : Utopia H i v d r D χ)
variable (A : ℝ) (he : 0≤A) (h : StampPrice T o p d v χ i A)
local notation "u" => coin Ξ
include h he Ξ
lemma bolus : ∃ K : ℝ, 0 ≤ K ∧ ∃ s:ℝ, 0<s∧∀ (I : RG.Rep G f) (a b : ℕ→ℝ) (t:ℝ), Equalized Q.table R I a b t→ t ≤ s →
    ∃ f : Head S → ℝ, SumBudget f (K*t) ∧ ∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K→X.x=p→X.manifest→X.χ=χ→∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (z:Air _ G) (U : E→ Config G c) (V:E→ Directions G _) (Z:E→ Air _ G) (x:E), Mode U x i v→ Clutch X z o.a R.beta d x i U V Z→ ∀ (k : Head S) (l:Finset ℕ), Healthy (Pressure.temp X.x) (H.supportP k) X.V →
        let f' (R' : RG.Rep G _) w:= wraps T X R.beta o.a W Q.table w Q.halo R' l z U V Z k
        Brush i (f k) 1 (f' I (low R I)-f' R 1) x:= by
  obtain ⟨k,hk,h⟩:= theatres Ξ A he h; obtain ⟨s,hs,Hs⟩:= h; obtain ⟨g,hg,h⟩:= feather Ξ
  obtain ⟨w,hw,hX⟩:= lint S χ p o.a (mul_pos o.large H.laws.data.room.fiery) i d
  let B:=∑' i,u i; have ht : SumBudget (u) B:= ⟨coin_pos Ξ,retail Ξ,le_rfl⟩; have hB:0 ≤ B:= tsum_nonneg (coin_pos Ξ)
  let n:ℝ:=Fintype.card (Stores S); have hn:0≤ n:=Nat.cast_nonneg _
  refine ⟨n*k+(w+(g*(1+B)+0)),by positivity,min s 1,lt_min hs zero_lt_one,?_⟩; intro I a b t hp ht'
  let A : Head S→ℝ := Sum.elim (fun _=>k*t) (Sum.elim (fun i=>w*b i) (Sum.elim (fun k=>g*(films c f a k+t*u (logKey S k))) fun _=>0))
  have hΩ := hp.fund_pos
  refine ⟨A,?_,?_⟩
  · let e : LogIndex c f ↪ Head S:= (Embedding.inl.trans Embedding.inr).trans Embedding.inr
    have hz:=budget_scale hg (budget_plus (filmed (c:=c) (f:=f) hp.ae) (budget_scale hΩ (budget_pull e e.injective ht)))
    have hx : SumBudget (fun _ : Stores S=> k*t) (n*(k*t)) := Cost.finite _ (mul_nonneg hk hΩ)
    have hy : SumBudget A (n*(k*t)+(w*t+(g*(t+t*B)+0))) := Cost.sum hx (Cost.sum (budget_scale (zero_le_one.trans hw) hp.aw) (Cost.sum hz (by simp [SumBudget,A]))) -- namespace
    exact budget_loosen hy (le_of_eq (by ring))
  intro F X hx hK hM hχ E _ _ _ z U V Z x hU hv p' l ht'₀ f'
  let V' := X.input (worldZ X R.beta z); let q i y:=X.enforce (2*o.a) (V y) (X.plaza (forcedFoot S.ratio 0 X.B R i)); let r' := low R I
  rcases p' with p'|k|k|k
  · exact Hs I a b t hp (ht'.trans (min_le_left ..)) _ X hx hK hM hχ E z U V Z x hU hv p' l ht'₀
  · let v:= I.activities.K k V' -R.activities.K k V'
    have hv' : |v| ≤ b k := by unfold v; rw [abs_sub_comm]; exact hp.soft _ _
    have hh:= hX F X hχ hK E R.beta z U V Z x hv (X.plaza (forcedFoot S.ratio 0 X.B R k))
    refine ((hh.smul v).climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
    · exact (mul_le_mul_of_nonneg_right hv' (zero_le_one.trans hw)).trans_eq (mul_comm ..)
    change I.activities.K k V'* X.enforce _ (V i) (X.plaza (forcedFoot S.ratio 0 X.B I k))- R.activities.K k V' * q k i= v*q k i; rw [← pointed hp.toFacing]; unfold q v; ring
  · exact h I a b t hp (ht'.trans (min_le_right ..)) X hx hK hM hχ E z U V Z x hU hv k l ht'₀
  apply Brush.zi _ (le_refl 0) zero_le_one; refine Eventually.of_forall fun j=>?_
  change Polar.sprinkle _ o.a I _ _ V' _ k- Polar.sprinkle _ o.a R W _ V' _ _ = _; rw [alarmWhistle o.a W hp.toFacing, sub_self]
end YM.PhysicalNext.Repeat.Alabaster
