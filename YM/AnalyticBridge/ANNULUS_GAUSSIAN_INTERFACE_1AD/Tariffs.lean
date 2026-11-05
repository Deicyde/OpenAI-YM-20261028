import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.LogFunding
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Offers

/-!
# Zeroth order ancillary prices for compulsory payment

Explicit post-L coefficient for shire. Allows also transition from
true tag masses to densities against uniform tag reference ONLY at the
charged locations; other/optional tag likelihood estimates exposed
separately. Before using reference outside too must either earn its
factor, or show uniform non-activation etc. No beta-drift inferences.
Observe all volume charges below are per typed seed.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset Scales YM.SectorNext.Vacuum.Panel
open scoped YM.Next.SectorChange.Completion
variable {G : Gauge} {c f : Side} {S : StepData c f}

def footprint (D : ℕ) : ℝ := 4*(2*(D:ℝ)+1)^4
lemma footprint_pos (D) : 0 < footprint D := by have he := Nat.cast_nonneg (α:=ℝ) D; unfold footprint; positivity
lemma plot_rel (O : Stores S) (D : ℕ) (x : ℝ) :
    (plotBill O D (radiusB x):ℝ) = footprint D * b x^4 * O.shares := by unfold plotBill footprint b; push_cast; ring

def linkRate (L : Side) (D : ℕ) := (Fintype.card Axis:ℝ)* (L.val:ℝ)^4 * footprint D

def windowRate (G : Gauge) (L : Side) (D : ℕ) (u v : ℝ) :=
  linkRate L (D+1)* ((Fintype.card G.ColorIndex:ℝ)*amount u v)

def iceRate (Z : ChartRatio G) (L : Side) :=
  linkRate L 11 * logCash Z

lemma links_cost {D x} (O : Stores S) (h : 1 ≤ radiusB x) :
    ((everyLink S O (D*radiusB x)).card:ℝ) ≤ linkRate S.patch.L (D+1) * b x ^4 * O.shares := by
  have he := Nat.cast_le (α:=ℝ).mpr (counts_torus O D _ h).2.1; push_cast at he
  rw [plot_rel] at he; unfold linkRate; exact he.trans_eq (by ring)
lemma ice_cost {x} (F : Forest S.ratio) (O A : Stores S) (h : 1 ≤ radiusB x) :
    ((driftwood A O x F).card:ℝ) ≤ linkRate S.patch.L 11 * b x^4 * O.shares := by
  have he := Nat.cast_le (α:=ℝ).mpr (frozen_count A O _ F h); push_cast at he
  rw [plot_rel] at he; unfold linkRate; exact he.trans_eq (by ring)

lemma logs_sufficient (T : Tube G S) (V : Config G c) (k : S.Choices) (A O : Stores S) (F : Forest S.ratio)
    (Z : ChartRatio G) (R : Rep G f) {D x u v}
    (h : 1 ≤ radiusB x) (he : 0 < u) (hv : u ≤ v)
    (hQ : Numeric (witnessGram T V x k A F) u v) (hQ' : Numeric (witnessGram T 1 x k (noHoles S) F) u v)
    (hs : 0<Z.scale) (hL : 1<y G S.patch.L x) (hB : R.beta∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x)) :
    (∑ i∈everyLink S O (D*radiusB x),couple T V x k A F v i)+grab x A F R Z (driftwood A O x F) ≤
      (coin G S.patch.L (windowRate G S.patch.L D u v + iceRate Z S.patch.L) 4 x)*O.shares := by
  let N:=everyLink S O (D*radiusB x); let E:=driftwood A O x F
  let U : ℝ := Fintype.card G.ColorIndex * amount u v
  have hu : 0≤U := mul_nonneg (Nat.cast_nonneg _) (amount_nonneg ..)
  have hm : (∑ i∈N, couple T V x k A F v i) ≤ N.card*U := by
    apply (sum_le_sum (g:=fun _ => U) (fun i (_:i∈N) => (le_abs_self _).trans (couple_amount T V x k A F hQ hQ' he hv i))).trans_eq
    simp
  have hb (i : ℕ) : 0 ≤ linkRate S.patch.L i := by unfold linkRate; have := footprint_pos i; positivity
  let c:= linkRate S.patch.L (D+1)* (b x)^4 * O.shares
  let f':= linkRate S.patch.L 11 * (b x)^4 * O.shares
  let r:=1+Real.log (y G S.patch.L x)
  have h₀ : 1≤r := by unfold r; linarith [Real.log_nonneg hL.le]
  have ht : N.card*U ≤ c*U*r := by
    have h2 : 0 ≤ c*U := by unfold c; have := hb (D+1); positivity
    calc
      _ ≤ c*U := mul_le_mul_of_nonneg_right (links_cost O h) hu
      _ ≤ _ := le_mul_of_one_le_right h2 h₀
  have hh : grab x A F R Z E ≤ f'*(logCash Z*r) := by
    have hs':=price_spare Z hs hL.le hB; unfold grab
    rw [neg_mul,← mul_neg]
    apply le_trans (b:=(E.card:ℝ)*(logCash Z*r)) (mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hs') (Nat.cast_nonneg _))
    refine mul_le_mul_of_nonneg_right (ice_cost F O A h) (mul_nonneg (logCash_nonneg _) (by linarith))
  refine (add_le_add (hm.trans ht) hh).trans_eq ?_
  unfold U c f' r coin windowRate iceRate; ring

/-- Cardinality factor changing local tag probability weights to
densities against discrete uniform probability. -/
def mint (S : StepData c f) (N : Support c) (M : Finset (Bond c)) :=
  (Fintype.card S.patch.FrameTag:ℝ)^N.card * (Fintype.card S.patch.Points:ℝ)^M.card

-- handles card=0 via a k (domain where this law is used)
lemma tag_quantum (k : S.Choices) :
    (1:ℝ) ≤ Fintype.card S.patch.FrameTag ∧ (1:ℝ) ≤ Fintype.card S.patch.Points := by
  have he : Nonempty S.patch.FrameTag := ⟨k.1 0⟩
  have ht : Nonempty S.patch.Points := ⟨k.2 (0,(0:Axis))⟩
  exact ⟨by exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α:=S.patch.FrameTag))), by exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α:=S.patch.Points)))⟩
lemma mint_pos (k : S.Choices) (N : Support c) (M : Finset (Bond c)) : 0 < mint S N M := by
  obtain ⟨hf,hb⟩:=tag_quantum k; unfold mint; positivity


def mintRate (Λ : Patch) (D : ℕ) :=
  footprint D * Real.log (Fintype.card Λ.FrameTag)+footprint (D+1) * Fintype.card Axis * Real.log (Fintype.card Λ.Points)

lemma minted (k : S.Choices) (O : Stores S) {D : ℕ} {x : ℝ} (h : 1≤radiusB x) (hβ : 1 ≤ y G S.patch.L x) :
    let N := O.dome (D*radiusB x)
    Real.log (mint S N (nearNoise N)) ≤ coin G S.patch.L (mintRate S.patch D) 4 x * O.shares := by
  intro N
  have ht := Nat.cast_le (α:=ℝ).mpr (counts_torus O D _ h).1; push_cast at ht
  have hc := Nat.cast_le (α:=ℝ).mpr (dome_count O D (radiusB x))
  rw [plot_rel] at ht hc
  obtain ⟨hf,hp⟩:=tag_quantum k
  rw [mint, Real.log_mul (by positivity) (by positivity), Real.log_pow,Real.log_pow]
  have H1:=Real.log_nonneg hf; have H2:=Real.log_nonneg hp
  have H3:=Real.log_nonneg hβ
  have he := add_le_add (mul_le_mul_of_nonneg_right hc H1) (mul_le_mul_of_nonneg_right ht H2)
  have hh : 0 ≤ mintRate S.patch D * b x^4 * O.shares := by
    unfold mintRate; have := footprint_pos D; have := footprint_pos (D+1); positivity
  refine he.trans ?_
  calc
    _ = mintRate S.patch D * b x^4 * O.shares := by unfold mintRate; ring
    _ ≤ mintRate S.patch D*b x^4*O.shares*(1+Real.log (y G S.patch.L x)) := le_mul_of_one_le_right hh (by linarith)
    _ = _ := by unfold coin; ring

/-- Cost order. In particular not a parameter choice depending
on the particular Tube or period. Caller may increase for other
prices at this stage (after L, before choosing the x delay). -/
def rollRate (P : Patch) (Z : ChartRatio G) (D : ℕ) (u v : ℝ) :=
  windowRate G P.L D u v + iceRate Z P.L + mintRate P (D+100)
lemma roll_cover (T : Tube G S) (V : Config G c) (k : S.Choices) (A O : Stores S) (F : Forest S.ratio)
    (Z : ChartRatio G) (R : Rep G f) {D x u v C}
    (h : 1 ≤ radiusB x) (he : 0 < u) (hv : u ≤ v)
    (hQ : Numeric (witnessGram T V x k A F) u v) (hQ' : Numeric (witnessGram T 1 x k (noHoles S) F) u v)
    (hs : 0<Z.scale) (hL : 1<y G S.patch.L x) (hB : R.beta∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x))
    (hC : rollRate S.patch Z D u v ≤ C) :
    let N := O.dome ((D+100)*radiusB x)
    (∑ i∈everyLink S O (D*radiusB x),couple T V x k A F v i)+grab x A F R Z (driftwood A O x F)+
        Real.log (mint S N (nearNoise N)) ≤ coin G S.patch.L C 4 x * O.shares := by
  intro N
  apply (add_le_add (logs_sufficient T V k A O F Z R h he hv hQ hQ' hs hL hB)
    (minted k O (D:=D+100) h hL.le)).trans
  unfold coin rollRate at *
  have hl := Real.log_nonneg hL.le
  set w := 1+Real.log (y G S.patch.L x)
  have he : 0≤ (b x)^4*w*O.shares := by unfold w; positivity
  have hv := mul_le_mul_of_nonneg_right hC he
  linarith only [hv]

end YM.AnalyticBridge.Annulus1AD
