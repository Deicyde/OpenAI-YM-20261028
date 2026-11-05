import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Borel
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Intake

/-!
Local multiplier absolute payments incl integrated price under the actual
covariance of the full formula, no artificial ambient-volume power. Jet
payments are integrals of the PRE-MASK differentiated sheets, not a claim of
interchanging differentiation and integration over decisions or under a fixed
Gaussian when it should change with V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian SourceBounds Next.Foundations Push.Local Marginal Leaf Kernel MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {x α : ℝ}
    {q : Chi} {Z : ChartRatio G} {d η K u v M C C' E : ℝ} {k : S.Choices} {V : Config G c} {l : ℕ}

lemma Board.flat (B : Board T q Z l x α d M C C' η K u v) (F : Forest S.ratio) (k : S.Choices) : (Native.kinetic T F k x).PosDef := by
  rw [← Native.ground_gram T F k x B.branch]; apply Matrix.PosDef.submatrix _ (Native.lineEquiv ..).injective
  let O : Stores S := ⟨∅,∅,∅⟩
  have he₀ : O.flags = RG.flags (temp x) (1 : Config G c) := by
    ext s; have h := Next.Foundations.one_healthy (G:=G) (Finset.univ : Support c) (temp x) (temp_nonneg x)
    have := Finset.disjoint_left.mp h (Finset.mem_univ s); simpa [O] using this
  exact (((B.ample 1 k O F (Allocation.hard ..)).2 he₀).1).2.2.2.1
lemma Board.fog (B : Board T q Z l x α d M C C' η K u v) (F : Forest S.ratio) (k : S.Choices) (h : A.flags=RG.flags (temp x) V) : (fog A F T x V k).PosDef ∧ (Rows.gram T x V k (shots S x) A F).PosDef := by
  have he := ((B.ample _ k _ F (Allocation.hard ..)).2 h).1.2.2.2
  exact ⟨he.2.1,he.1⟩

lemma with_outer {I τ X : Type} [Fintype I] [Fintype τ] [DecidableEq I] [DecidableEq τ] [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (e : I ↪ τ) {C : Gaussian.Table τ} (h : C.PosDef)
    {v a : ℝ} (hv : 0<v) {f : X → Vec τ → ℝ} (hm : Measurable (uncurry f)) (hf : ∀ y x, ‖f y x‖ ≤ allowance (C.submatrix e e) v a (project e x)) :
    (∀ y, Integrable (f y) (cloud C)) ∧ Integrable (uncurry f) (ν.prod (cloud C)) ∧ (∫ y, (∫ x, ‖f y x‖ ∂cloud C) ∂ν) ≤ a*refund I v/Gaussian.dome I := by
  have hi y := purchase e h hv (f y) (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (hf y)
  have hg := ((consume e h hv a).1.comp_snd ν).mono' hm.aestronglyMeasurable (ae_of_all _ fun x => hf x.1 x.2)
  refine ⟨fun y => (hi y).1,hg,?_⟩
  apply (integral_mono hg.norm.integral_prod_left (integrable_const _) (fun y => (hi y).2)).trans_eq
  simp

namespace Leaf
variable {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {L : Leaf G A x F I J ρ} {R : Rep G f} {δ w : ℝ} {m ℓ : ℕ → ℝ} {s o b : Finset ℕ}
    {h : LinkArray G (Frozen A x F) → Prices G (Active A x F) → Kernel G c I J ρ}

/-- Actual sector datum with correct V flags (not re-sorting by a new
active table!). Even the literally discontinuous mask conventions can use
this value estimate. Measurable sheets automatic for `paper`, `Seen.literal`.
-/
lemma integrated_value (B₀ : Board T q Z l x α d M C C' η K u v) (he : ∀ Y z, L.Binds T k R.beta q d Y z V (h Y z))
    (ha : A.flags=RG.flags (temp x) V) (hp : Power T x R.beta k A V q d F E) (auth : Authored R δ w m ℓ) (hR : Reads L R s o b) (hS : Seen (uncurry h)) :
    let Mx Y z := (h Y z).multiplier S L.location R q Z d (lights s R (field T F A V k q d R.beta Y z)) o V
    let ν := piHaar G (Frozen A x F); let μ := cloud (fog A F T x V k)
    let a := ticket G I J K (spare Z R.beta) η s o m ℓ
    (∀ y, Integrable (Mx y) μ) ∧ Integrable (uncurry Mx) (ν.prod μ) ∧ (∫ Y, (∫ z, ‖Mx Y z‖ ∂μ) ∂ν) ≤ a*refund (I × G.ColorIndex) (η/4)/Gaussian.dome (I × G.ColorIndex) := by
  intro f ν μ a
  have hη := B₀.gap
  apply with_outer _ L.active (B₀.fog F k ha).1 (by positivity)
    (hS.selected hR q (Y:=Prod.fst) (z:=Prod.snd) (fun i => he i.1 i.2) B₀.ratio B₀.guard.pos B₀.room auth.valid V)
  intro Y z
  have hv := he Y z
  have hi := kernelPrices.margins T F x k A V L B₀.branch (fun O W ht => ((B₀.ample W k O F (Allocation.hard ..)).2 ht).1) ha hv
  have H := true_value hi hv hp B₀.ratio B₀.matrix B₀.gap B₀.guard.pos B₀.room auth hR
  rw [hv.cov, hv.draw] at H; exact H

variable {p : BudgetPoint} {y : Site c} {B μ : ℝ}
set_option maxHeartbeats 500000 in
lemma integrated_jet (B₀ : Board T q Z l x α d M C C' η K u v) (he : ∀ Y z, L.Binds T k R.beta q d Y z V (h Y z))
    (ha : A.flags=RG.flags (temp x) V) (hp : Power T x R.beta k A V q d F E) (auth : Authored R δ w m ℓ) (hR : Reads L R s o b) (hl : l≤R.p.order)
    (ht : R.p.threshold = fiery G x S.patch.L) (hS : Seen (uncurry h)) (hf : ∀ Y z, ContinuousAt ((h Y z).stage (coupling R.beta) ∘ increment V) 0)
    (hh : ∀ Y z, let H := h Y z; (∀ i, ‖H.stage (coupling R.beta) V i‖ ≤ 2*d) →
      Steady S L.location H R o V ∧ Incoming H R.p.threshold l (p.dirBound y) V B μ) (hB : 0≤B) (hμ : 0≤μ)
    (i : List (Directions G c)) (hi : i.length ≤ l) (hD : ∀ z∈i,p.dirBound y z) :
    let U Y z := (h Y z).multiplier S L.location R q Z d (lights s R (field T F A V k q d R.beta Y z)) o
    let ν := piHaar G (Frozen A x F); let M' := cloud (fog A F T x V k)
    let f Y z := leftDerivs (U Y z) i V
    let a := ticket G I J K (spare Z R.beta) η s o m ℓ * overhead S L.location ρ p y R Z l x d M C C' η K E B μ s m
    (∀ Y z, Chart l (U Y z) V) ∧ Measurable (uncurry f) ∧ (∀ y, Integrable (f y) M') ∧ Integrable (uncurry f) (ν.prod M') ∧
      (∫ Y, (∫ z, ‖f Y z‖ ∂M') ∂ν) ≤ a * refund (I × G.ColorIndex) (η/4) / Gaussian.dome (I × G.ColorIndex) := by
  intro U ν M' f a
  have h' Y z := paid_jet B₀ (Allocation.hard ..) (he Y z) ha hp auth hR hl ht (hf Y z) (hh Y z) hB hμ
  let U' := uncurry U
  have hV (p) : Chart l (U' p) V := (h' p.1 p.2).1
  have hm (W) : Measurable fun p => U' p W := hS.selected hR q (Y:=Prod.fst) (z:=Prod.snd) (fun i => he i.1 i.2) B₀.ratio B₀.guard.pos B₀.room auth.valid W
  have hv : Measurable (uncurry f) := jet_param hm i (fun x => (hV x).of_le (Nat.cast_le.mpr hi))
  have hη := B₀.gap
  exact ⟨fun Y z => (h' Y z).1,hv,with_outer _ L.active (B₀.fog F k ha).1 (by positivity) hv (fun Y z => (h' Y z).2 i hi hD)⟩
end Leaf
end YM.AnalyticBridge.MarginalMultiplier3b1d
