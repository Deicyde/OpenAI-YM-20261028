import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Receiving
/-!
# True inherited-label family pricing (no suppression of regular Taylor residue in place)

Reserve same- and cross-stage bills for ANY subfamily even past purchases. Local, all modes,
IN the RG budget support law without dropping masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Buckram
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {x s v : ℝ}
variable (R : Rep G f)

abbrev Marks (R : Rep G f) (τ : ℕ→ℝ) (c : ℝ) := ∀ z : Site f, SumBudget
    (fun i=> if (R.activities.reg i).site=z then R.p.mass (R.activities.reg i).support (τ i) else 0) c

-- no closure under permutations required; complete sym versions will be priced on the output. Not yet an EBound of the erased recipe (it has no acknowledged sym here).
structure Disburse (p : ℕ→Prop) (s : ℝ) : Prop where
    receipts : ∃ τ : ℕ→ℝ, (∀ i,p i → R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i)) ∧
      Marks R (fun i=> if p i then τ i else 0) s
namespace Marks
variable {R} {τ v' : ℕ→ℝ}
lemma mono (h : Marks R τ x) (he : ∀ i,0≤v' i) (hp : v' ≤ τ) : Marks R v' x := fun i=>
  budget_mono (h i) (fun j=> by split; exact mul_nonneg (Real.exp_nonneg _) (he _); exact le_rfl) (fun i=> by split; exact mul_le_mul_of_nonneg_left (hp i) (Real.exp_nonneg _); exact le_rfl)
lemma scale (h : Marks R τ x) (hv : 0 ≤ v) : Marks R (fun i=> v*τ i) (v*x) := by
  intro i; convert budget_scale hv (h i) using 1; ext j; dsimp only [BudgetPoint.mass]; split <;> ring
lemma mate (h : Marks R τ x) : 0 ≤ x := budget_nonneg (h 0)
lemma nonneg (h : Marks R τ x) (i) : 0 ≤ τ i := nonneg_of_mul_nonneg_right
    (show 0≤ Real.exp _ * τ i from
    (by simpa only [if_true] using! (h (R.activities.reg i).site).1 i)) (Real.exp_pos _)
lemma within (h : Marks R τ x) (i) : τ i ≤ x := (R.p.loMass _ _ (h.nonneg i)).trans (by simpa only [if_true] using budget_single (h (R.activities.reg i).site) i)
end Marks
namespace Disburse
variable {R} {p : ℕ→Prop} (h : Disburse R p s) {P : Teller G} {S : StepData c f} {T : Tube G S}
include h
lemma common (ht : Intake P T x R) : ∃ τ : ℕ→ℝ, (∀ i,R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i)) ∧
    Marks R τ (incomingE G S.patch.L x) ∧ Marks R (fun i=> if p i then τ i else 0) s := by
  obtain ⟨τ,hτ,hS⟩:= h.receipts
  obtain ⟨v,hV,hM⟩:= ht.cap.labels.boundE
  let f i:= if p i then min (τ i) (v i) else v i
  have he i : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (f i) := by
    unfold f; split
    next hp => rcases min_choice (τ i) (v i) with hv|hv
               · rw [hv]; exact hτ i hp
               rw [hv]; exact hV i
    exact hV _
  refine ⟨f,he,Marks.mono hM (fun i=> (he i).1) (fun i=> ?_), (show Marks _ _ s from Marks.mono hS (by intro i; split; exact (he i).1; exact le_rfl) (fun i=> ?_))⟩
  · unfold f; split; exact min_le_right ..; exact le_rfl
  · dsimp only [f]; split; next hi=> exact min_le_left ..
    exact le_rfl
lemma nonneg : 0≤s := Marks.mate h.receipts.choose_spec.2
omit h
lemma all (ht : Activities.EBound R.activities R.p s) : Disburse R (fun _=> True) s := by
  obtain ⟨b,h,h'⟩:= ht; exact ⟨b,fun i _=> h i,by simp; exact h'⟩
end Disburse

open Raw
-- inflation λ≥1 uses this sale directly, governed ONLY by anchored bill on marked slots
lemma sails_blend (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0 < ε) (ha : 0≤a) (hr: 4*ε<P.top.supportExponent) : ∃ n : ℕ,∀ L:Side,n ≤ L.val → ∀ (t : ℝ), -(1/2:ℝ) < t → ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L → Intake P T x R →
      ∀ v : ℕ→ℝ, Marks R v (betaF G x L ^ (-(1/2:ℝ))) →
        Sales (radiusB x) a ε (regularFoot S.ratio l (radiusB x) R) v (regularExtra R) ((betaF G x L)^t) := by
  obtain ⟨n,hn⟩:= Fees.exponent (l+5) he ha (show 2*ε<P.top.supportExponent-2*ε by linarith)
  refine ⟨n,fun L hL u hv => ?_⟩
  let J (x : ℝ) := extentCost (l+5) (radiusB x)
  let x₀ x:=betaF G x L ^ (-(1/2):ℝ)
  let bill (x d : ℝ) := Footprint.payment (L.val^4) (J x) 0 ε 1 d a (preCost (l+5))
  have hk {r : ℝ} {z : ℝ → ℝ} (h : Rate G L r z) : Rate G L r (fun x => bill x (z x)) := by
    have hh : Rate G L 0 (fun x : ℝ => (J x:ℝ)) := by simpa [extentCost,J] using
      (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
    simpa only [zero_add,bill] using! Rate.payment (Rate.const 1) h hh (L.val^4) 0 ε a _
  filter_upwards [hk (z:=x₀) Rate.power u hv, Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent by linarith)] with x hx hh
  intro c f S T R hP hR b hM
  let p:=S.ratio; let B:=radiusB x
  have hP' : p.count=L := hP
  let Y i := (R.activities.reg i).support
  have hY : Anchored (fun i => (R.activities.reg i).site) b (regularExtra R) (P.top.supportExponent) (x₀ x) := by
    rw [hR.exponent]; intro x'; convert hM x' using 1; ext i; simp only [BudgetPoint.mass,regularExtra]; rw [mul_comm]
  have hm := Sales.anchored_sale (z := b) (l:=l+5) (M := R.p.B) p (fun i => (R.activities.reg i).site) (Y := Y)
    (fun i => (R.activities.reg i).anchor) hY hM.nonneg
    (X:=regularFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
    (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
    (fun i => ⟨hM.nonneg _,by simp⟩)
  apply hm.raise; rw [hP']; exact (le_abs_self _).trans hx
end YM.ConnectedActivityE6.Buckram
