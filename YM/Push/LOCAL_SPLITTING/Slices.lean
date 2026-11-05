import YM.Push.LOCAL_SPLITTING.Funding
import YM.Push.LOCAL_SPLITTING.Layers
import YM.Push.LOCAL_SPLITTING.Padding


/-!
# Direct one-block decomposition with a (noncontractive) layer bill

Conditional only on properties of the vacuum history, operands and alphabet
at the actual step (consumer on History below), not a postulated component
expansion here.

Exact telescoping kernels, split at current source anchor.

Local supports at each radius with all coefficients/prices explicit before
the side; the SUM runs to that side and is NOT controlled as it tends to
infinity.

This illustrates both applicability of the covariant split to the
actual Wilson blocking kernel and what is not covered by bare kernel
calculus for a uniform source step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G} {T : SectionData F}
variable (S : StepData c f) (β : ℝ) (R : Rep G c) (o : Site c) (D : Config G f → ℝ) (N : Config G f → ℂ)

def complement (i : ℕ) := gap S β D N o i - masked R.p.threshold (layer o i) (gap S β D N o i)

variable (F) in
def raw (L : Nonempty (Reserve R.activities)) : Raw F c where
  seed := 0
  bulk := gap S β D N o
  forced := (slots L (layer o)).pack R.p.threshold (complement S β R o D N)

variable (A T) in
def slices (L : Nonempty (Reserve R.activities)) : Coefficient F c :=
  (raw F S β R o D N L).build o (layer o) A T R (slots L (fun i => joint T o (layer o i)))

-- Estimates. For applications to the raw bound variable J=kernel.penalty * β.
def layerBound (G : Gauge) (J : ℝ) (B : BudgetPoint) (a : ℝ) (i : ℕ) := 2 * fieldPrice G J B i * a
def layerMass (A : Hol G) (T : SectionData F) (J : ℝ) (B : BudgetPoint) (w a : ℝ) (i : ℕ) := Real.exp (B.supportExponent*((count i + atomTiles T:ℕ):ℝ)) * (atomPrice A F w * layerBound G J B a i)
def layerMerge (A : Hol G) (T : SectionData F) (J : ℝ) (B : BudgetPoint) (w v a : ℝ) (i : ℕ) := layerMass A T J B w a i * Real.exp (((count i+T.stencil.card:ℕ):ℝ)*v)
def layerTotal (A : Hol G) (T : SectionData F) (c : Side) (J : ℝ) (B : BudgetPoint) (w v κ a : ℝ) :=
  let m := ∑ i∈Finset.range (c.val+1), layerMerge A T J B w v a i
  (∑ i∈Finset.range (c.val+1),layerMass A T J B w a i) + (m/κ + m/κ)

def charged (c : Side) (e : ℕ → ℝ) (i : ℕ) := if i≤c.val then e i else 0

private theorem sumBudget_charge {C g : ℕ → ℝ} (h : ∀ i, 0 ≤ g i) (he : ∀ i, g i ≤ charged c C i) : SumBudget g (∑ i∈Finset.range (c.val+1), C i) := by
  let s := Finset.range (c.val+1)
  have hn i (hi : i∉s) : g i = 0 := le_antisymm ((he i).trans_eq (if_neg (by simpa [s] using hi))) (h _)
  rw [SumBudget,tsum_eq_sum hn]; exact ⟨h,summable_of_ne_finset_zero hn,Finset.sum_le_sum fun i hi => (he i).trans_eq (if_pos (by simpa [s] using hi))⟩

private theorem rawPrices (T : SectionData F) (A : Hol G) (o : Site c) (B : BudgetPoint) (J w v a : ℝ) (h : T.Sound A)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hv : 0 ≤ v) (i : ℕ) :
    let e := charged c (layerBound G J B a) i
    Raw.rawMass A T o (layer o i) B w e ≤ charged c (layerMass A T J B w a) i ∧
    Raw.rawMerge A T o (layer o i) B w v e ≤ charged c (layerMerge A T J B w v a) i ∧
    mergePrice B v (layer o i) (if i≤c.val then 2*a else 0) ≤ charged c (layerMerge A T J B w v a) i := by
  have hp := fieldPrice_ge G J B i; have he := atomPrice_ge_one A F hw; have he' := mul_nonneg (zero_le_one.trans he) (mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans hp)) ha)
  let Y := joint T o (layer o i)
  let m := count i+atomTiles T
  let j := count i+T.stencil.card
  have hm : coverNumber B.B Y ≤ m := (Corona.meets_sum (layer_origin o i) (show o∈T.footprint o from Finset.mem_image.mpr ⟨0,h.anchored,by simp⟩) _).trans
      (Nat.add_le_add (layer_tiles o ..) (atomTiles_price ..))
  have hcard : Y.card ≤ j := (Finset.card_union_le ..).trans (Nat.add_le_add (layer_size o i) Finset.card_image_le)
  dsimp only [charged]; split
  · have H : Raw.rawMass A T o (layer o i) B w (layerBound G J B a i) ≤ layerMass A T J B w a i := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hm) B.exponent_pos.le)) he'
    refine ⟨H,mul_le_mul H ((sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hv))) (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (mul_nonneg (Real.exp_pos _).le he'),?_⟩
    apply mul_le_mul _ ((sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((layer_size o i).trans (Nat.le_add_right ..))) hv))) (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (mul_nonneg (Real.exp_pos _).le he')
    apply mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((layer_tiles o B i).trans (Nat.le_add_right ..))) B.exponent_pos.le)) _ (by positivity) (Real.exp_pos _).le
    exact le_trans (by unfold layerBound; nlinarith : 2*a ≤ layerBound G J B a i) (le_mul_of_one_le_left (mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans hp)) ha) he)
  simp [mergePrice,Raw.rawMass,Raw.rawMerge,BudgetPoint.mass]

variable {D N R}

theorem complement_ok (h : Good S D N) (i : ℕ) : Attaches R.p.threshold (layer o i) (complement S β R o D N i) :=
  let he := gap_regular S β o h R.p i
  ⟨fun _ _ h ha => congr_arg₂ (· - ·) (he.sites _ _ h) (uses_mask _ he.sites _ _ h ha),fun _ _ => congr_arg₂ (· - ·) (he.symmetry _ _) (invariant_mask he.symmetry _ _ _ _),he.borel.sub (masked_measurable _ _ _ he.borel),fun _ hu => sub_eq_zero.mpr (masked_eq _ _ _ _ hu).symm⟩


private theorem paid (L : Nonempty (Reserve R.activities)) (h : Good S D N) {σ C Λ δ w v κ a : ℝ}
    (hl : R.Lawful σ C Λ δ v) (hv : 0 ≤ v) (hκ : 0 < κ) (ht : Readable A T R.p c w) (ha : ∀ U, ‖N U‖ ≤ a*D U) :
    (raw F S β R o D N L).Format o (layer o) R ∧ (raw F S β R o D N L).Income o (layer o) A T R w v κ (layerTotal A T c (β*S.kernel.penalty) R.p w v κ a) := by
  let J := β*S.kernel.penalty; let p := layerBound G J R.p a
  let s := Finset.range (c.val+1)
  have hg i := (gap_bill S β o h R.p ha i).1
  have h₁ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 1)) (h.positive _)
  have hx i := rawPrices T A o R.p J w v a ht.sound ht.nonneg h₁ hv i
  have he i := mul_nonneg (zero_le_one.trans (atomPrice_ge_one A F ht.nonneg)) (hg i).1
  have h1 := sumBudget_charge (C:=layerMass A T J R.p w a) (fun i => mul_nonneg (Real.exp_pos _).le (he i)) (fun i => (hx i).1)
  have h2 := sumBudget_charge (C:=layerMerge A T J R.p w v a) (fun i => mergePrice_nonneg _ _ hv (he i)) (fun i => (hx i).2.1)
  refine ⟨⟨layer_origin o, gap_regular S β o h R.p,(slots L (layer o)).forceFormat hl.labels.forced (layer_origin o) (complement_ok S β o h)⟩,
    ∑ i∈s,layerMass A T J R.p w a i,(∑ i∈s,layerMerge A T J R.p w v a i)/κ, (∑ i∈s,layerMerge A T J R.p w v a i)/κ,
    (tsum_nonneg h1.1).trans h1.2.2, div_nonneg ((tsum_nonneg h2.1).trans h2.2.2) hκ.le,div_nonneg ((tsum_nonneg h2.1).trans h2.2.2) hκ.le, le_rfl,⟨charged c p, fun i => hg i, h1,(by rwa [mul_div_cancel₀ _ hκ.ne'])⟩,?_⟩
  let e := charged c (fun _ => 2*a)
  have hp i : 0 ≤ e i := by dsimp only [e,charged]; split <;> positivity
  rw [mul_div_cancel₀ _ hκ.ne']; refine (slots L (layer o)).forceCost hl.labels.boundK (sumBudget_charge (fun i => mergePrice_nonneg _ _ hv (hp i)) (fun i => (hx i).2.2)) hp fun i U => ?_
  unfold complement; rw [Pi.sub_apply]; by_cases hU : Healthy R.p.threshold (layer o i) U
  · rw [masked_eq _ _ _ _ hU,sub_self,norm_zero]; exact hp _
  rw [masked_ne _ _ _ _ hU,sub_zero]; exact (gap_bill S β o h R.p ha i).2 _




end YM.Push.Local.Kernel
