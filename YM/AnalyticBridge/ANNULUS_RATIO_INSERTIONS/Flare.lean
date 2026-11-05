import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Luggage
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Prereq
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Prices


/-!
# Real local factors (at fixed V) and remaining sockets

Count both endpoints for these prices.

Also cost of local tag conversion
including all reference alternatives irrespective of values.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Dress
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix Bloch
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Packet ownership of full color block data. Use either endpoint
in determining if the factor is needed (retaining both); do not put
two copies in even if both ends in the halo. -/
def qLogs (O : Stores S) (R : ℕ) := (Finset.univ : Finset (Bond f)).filter fun i =>
  S.ratio.parent i.1∈O.dome R ∨ S.ratio.parent (i.1+Lattice.step i.2)∈O.dome R

lemma qLogs_card (O : Stores S) (R l B : ℕ) (h : R+1 ≤ l*B) :
    (qLogs O R).card ≤ vans S.patch.L l * (B+1)^4 * O.shares := by
  apply berth O (l*B) _ _ le_rfl
  intro i he; rcases (Finset.mem_filter.mp he).2 with hi|hi
  · exact Corona.halo_mono (by omega) (fun _ h => h) hi
  obtain ⟨y,hy,ht⟩ := halo_spec.mp hi
  refine halo_spec.mpr ⟨y,hy,?_⟩
  have hi := Work.E03.parent_step S i.1 i.2
  rw [separation_comm] at hi
  exact (separation_triangle _ (S.ratio.parent (i.1+Lattice.step i.2)) _).trans ((Nat.add_le_add ht hi).trans h)

/-- L should be paired local log diagonal difference (-1/2*(A
minus Aflat) trace) if using E's representation. Keep *all*
link positions in representing L including identity-completed
ones (can put zero only where appropriate, prove the split / fits).
Here we admit any values with individual bounds; no assumption of
cancellation in the sum. No assumption that L expanded gives entire
log determinant. -/
def insertLog (O : Stores S) (R : ℕ) (L : Bond f → ℝ) := ∑ i ∈ qLogs O R, L i

lemma log_price (O : Stores S) (R l B : ℕ) (h : R+1 ≤ l*B) (L : Bond f → ℝ) {K : ℝ}
    (hp : 0 ≤ K) (he : ∀ i∈qLogs O R, L i ≤ K) : insertLog O R L ≤ K * (vans S.patch.L l:ℝ)*
      ((B:ℝ)+1)^4*O.shares := by
  have hi := Nat.cast_le (α:=ℝ).mpr (qLogs_card O R l B h)
  push_cast at hi
  calc
    _ ≤ ∑ _i∈qLogs O R,K := Finset.sum_le_sum he
    _ ≤ K * _ * _ * _ := by simp only [Finset.sum_const,nsmul_eq_mul]; linarith only [mul_le_mul_of_nonneg_left hi hp]

/-- Cost of moving to physical tag probability convention (E's uniform
reference BEFORE eligibility), or 1 on the actual-mass convention already
used in dyed. One cost per physical tag; do not integrate tags separately
on each transformed copy. Retain all actual masses, even at locations E
intends to set to one analytically later. -/
def tagConv (O : Stores S) (uniform : Bool) (R : ℕ) := if uniform then
    (Fintype.card S.patch.FrameTag:ℝ)^(O.dome R).card *
      (Fintype.card S.patch.Points:ℝ)^(qBonds O R).card else 1

def tagCurrency (P : Patch) (l : ℕ) := Real.log (Fintype.card P.FrameTag)*elbow l+Real.log (Fintype.card P.Points)*(Fintype.card Axis)*elbow l

lemma alphabet_pos (P : Patch) : 1 ≤ (Fintype.card P.FrameTag:ℝ) ∧ 1 ≤ (Fintype.card P.Points:ℝ) := by
  haveI : Nonempty P.Points := ⟨P.center⟩
  constructor <;> exact_mod_cast Fintype.card_pos



lemma pos_conv (O : Stores S) (uniform : Bool) (R : ℕ) : 0 < tagConv O uniform R := by
  obtain ⟨h1,h2⟩ := alphabet_pos S.patch
  unfold tagConv; split <;> positivity

lemma nonneg_currency (P : Patch) (l : ℕ) : 0 ≤ tagCurrency P l := by
  obtain ⟨h1,h2⟩ := alphabet_pos P
  exact add_nonneg (mul_nonneg (Real.log_nonneg h1) (Nat.cast_nonneg _)) (mul_nonneg (mul_nonneg
    (Real.log_nonneg h2) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

lemma qBonds_card (O : Stores S) (R l B : ℕ) (h : R+1 ≤ l*B) :
    (qBonds O R).card ≤ Fintype.card Axis*(elbow l*(B+1)^4*O.shares) := by
  let W := O.dome (l*B)
  have hi : qBonds O R ⊆ W ×ˢ (Finset.univ : Finset Axis) := by
    intro i hi
    refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
    have hx := (Finset.mem_filter.mp hi).2
    rw [Finset.disjoint_left] at hx
    push Not at hx
    obtain ⟨y,hy,ht⟩ := hx
    unfold pinPos at ht; simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl
    · exact Corona.halo_mono (by omega) (fun _ hi => hi) hy
    obtain ⟨x,hx,hb⟩ := halo_spec.mp hy
    refine halo_spec.mpr ⟨x,hx,?_⟩
    have hm : separation (i.1+Lattice.step i.2) i.1 ≤ 1 := (separation_comm ..).trans_le (Work.E01.sep_step_le ..)
    exact (separation_triangle x _ _).trans ((Nat.add_le_add hb hm).trans h)
  have hh := Finset.card_le_card hi
  rw [Finset.card_product,Finset.card_univ,mul_comm] at hh
  exact hh.trans (by unfold W; gcongr; exact elbow_room O _ _ _ le_rfl)

lemma conv_bound (O : Stores S) (uniform : Bool) (R l B : ℕ) (h : R+1 ≤ l*B) :
    tagConv O uniform R ≤ Real.exp (tagCurrency S.patch l * ((B:ℝ)+1)^4 * O.shares) := by
  obtain ⟨h1,h2⟩ := alphabet_pos S.patch
  let T := ((B:ℝ)+1)^4*(O.shares:ℝ)
  have hT : 0≤T := mul_nonneg (by positivity) (Nat.cast_nonneg _)
  unfold tagConv
  split
  · rw [← Real.exp_log (mul_pos (pow_pos (zero_lt_one.trans_le h1) _) (pow_pos (zero_lt_one.trans_le h2) _)),
      Real.log_mul (pow_pos (zero_lt_one.trans_le h1) _).ne' (pow_pos (zero_lt_one.trans_le h2) _).ne',Real.log_pow,Real.log_pow]
    have hi := Nat.cast_le (α:=ℝ).mpr (qBonds_card O R l B h)
    have hx := Nat.cast_le (α:=ℝ).mpr (elbow_room O R l B (by omega))
    push_cast at hi hx
    apply Real.exp_monotone; unfold tagCurrency; linarith only [mul_le_mul_of_nonneg_right hi (Real.log_nonneg h2), mul_le_mul_of_nonneg_right hx (Real.log_nonneg h1)]
  exact Real.one_le_exp (mul_nonneg (mul_nonneg (nonneg_currency ..) (by positivity)) (Nat.cast_nonneg _))

variable (O A : Stores S) (x W : ℝ) (V : Config G c) (k : S.Choices) (p : Rep G f)
  (U : Config G f) (q : Chi)

/-- All the enrolled mask, partition, tag factors for this interface,
but notice these do not include E activity, uncut base tails, the K
weights themselves, or external (unpaid) tag ratios in later uses.
Do not infer that these are the entire multiplier. b is the incoming list.
-/
def due (uniform : Bool) (R : ℕ) (b : Finset ℕ) := tagConv O uniform R * insist O A x W V k U q R *
    examine p.activities p.p b U O R
lemma due_bound (uniform : Bool) (R : ℕ) (b : Finset ℕ) (hm : S.patch.Branches S.kernel G) :
    ‖due O A x W V k p U q uniform R b‖ ≤ tagConv O uniform R := by
  obtain ⟨hh,ht⟩ : insist O A x W V k U q R ∈ Set.Icc (0:ℝ) 1 := multi_range A x W V k U q hm _ _ _
  obtain ⟨h1,h2⟩ := examine_range p.activities p.p b U O R
  unfold due; rw [Real.norm_of_nonneg (by have := pos_conv O uniform R; positivity),mul_assoc]
  apply mul_le_of_le_one_right (pos_conv ..).le ((mul_le_mul ht h2 h1 zero_le_one).trans (by norm_num))
lemma due_prereq (uniform : Bool) {R : ℕ} (b : Finset ℕ) (hi : due O A x W V k p U q uniform R b ≠ 0)
    {D : ℕ} (hl : (D+5)*radiusB x ≤ R) (hw : 0<W) (hp : 0 < fiery G x S.patch.L) (h : S.patch.Branches S.kernel G) :
    Wide O A D x W U k V := insists O A x W V k U q hl hw hp h (right_ne_zero_of_mul (left_ne_zero_of_mul hi))
lemma due_meas (uniform : Bool) (R : ℕ) (b : Finset ℕ) (h : S.patch.Branches S.kernel G) :
    Measurable (fun U : Config G f => due O A x W V k p U q uniform R b) := by
  exact (measurable_const.mul (multi_meas A x W V k q h (O.dome R) (qBonds O R) (qFaces O R))).mul
    (stamp_meas p.activities p.p b _)








end YM.AnalyticBridge.AnnulusRatioInsertions.Dress
