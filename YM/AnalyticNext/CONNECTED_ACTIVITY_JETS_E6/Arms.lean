import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Combo
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Logs
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tax

/-!
# Arm alphabet

Continuous path receipts; no minimizer over labels. Use LETTERS closed
loops retaining root (at all-link blocks). Traces over dots after multiplying
colors. Summing each graded inventory recovers Pulse.logs at each grade.
Prices on the actual matrices from Shutter later. Inverse shells
identity on sleeping coordinates also on loops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f : Side} {S : StepData c f} {B u m : ℕ}
variable {G : Gauge} {η r Q : ℝ}

namespace Itinerary
variable (D : Window (along (G:=G) S) B) (A : Mat f G)

/-- No `Fintype` total logs on an implicit choice list. Use sums/import
labels at fixed grade order. Keep intermediate sector in lookup. -/
def checkIn (P : ℝ → ℕ → Mat f G) {n : ℕ} (i : Bond f) (l : Itinerary f n) (j : G.ColorIndex) :=
    ∫ t in (0:ℝ)..1, if arrive i l=i then combo i l (P t) j j else 0

def stamp (P : ℝ → ℕ → Mat f G) {n : ℕ} (i : Bond f) (l : Itinerary f n) := ∑ j, checkIn P i l j

lemma opens (S : StepData c f) (n : ℕ) (i : Bond f) (j : G.ColorIndex) (P : ℝ → ℕ → Mat f G)
    (hp : ∀ k<n, ContinuousOn (fun s => P s k) (Set.uIcc (0:ℝ) 1)) :
    (∫ t in (0:ℝ)..1, Itinerary.product n (P t) (i,j) (i,j)) = ∑ l : Itinerary f n, checkIn P i l j := by
  simp_rw [multiply S i]
  refine intervalIntegral.integral_finsetSum (fun l _ => ?_)
  refine ContinuousOn.intervalIntegrable ?_
  by_cases he : arrive i l=i
  · simp_rw [if_pos he]; exact continuousOn_pi.mp (continuousOn_pi.mp (combo_continuous i l P _ hp) j) j
  simp_rw [if_neg he]; exact continuousOn_const

variable {P : ℝ → ℕ → Mat f G} {l : ℕ → ℝ} {b : ℕ}

lemma sum_cost {n : ℕ} (i : Bond f) (p : Itinerary f n) (hl : ∀ i<n, 0 ≤ l i)
    (hC : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ k<n, Thin (along S) (along S) (P x k) b)
    (hX : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ k<n, ∀ i j, |P x k i j| ≤ l k) :
    |stamp P i p| ≤ if Armed S b i p then (Fintype.card G.ColorIndex:ℝ)^ (n+1)* tally (n:=n) l else 0 := by
  let c := Fintype.card G.ColorIndex
  unfold stamp; apply (Finset.abs_sum_le_sum_abs ..).trans
  have he : ∀ t ∈ Set.uIoc (0:ℝ) 1, t∈Set.Icc (0:ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one]; exact fun _ h => Set.Ioc_subset_Icc_self h
  split
  next hm =>
    have hn := count_pos l hl
    let C : ℝ := c^n*tally (n:=n) l
    have hw : 0≤C := by unfold C; positivity
    refine le_trans (Finset.sum_le_sum (g:=fun _ => C) (fun j _ => ?_)) ?_
    · have ht x (hh : x∈Set.uIoc (0:ℝ) 1) : ‖(if arrive i p=i then combo i p (P x) j j else 0)‖ ≤ C := by
        rw [Real.norm_eq_abs]; split
        next he' =>
          have hz := pricingEntries S (P x) l i p (hX _ (he _ hh)) hl j j
          simpa only [C,c, Nat.cast_pow] using! hz
        next hh' => rwa [abs_zero]
      simpa only [checkIn,sub_zero,abs_one,mul_one,← Real.norm_eq_abs] using! intervalIntegral.norm_integral_le_of_norm_le_const ht
    rw [sum_const,nsmul_eq_mul, card_univ]; unfold C c; exact le_of_eq (by ring)
  next hn =>
    apply Finset.sum_nonpos; intro j hj
    apply le_trans (b:=(0:ℝ)*|1-1+1|) _ (by norm_num)
    have hh x (hx : x∈Set.uIoc (0:ℝ) 1) : ‖(if arrive i p=i then combo i p (P x) j j else 0)‖ ≤ 0 := by
      rw [filtered S b i p hn (P x) (hC x (he x hx))]; simp
    simpa only [checkIn,zero_mul,← Real.norm_eq_abs] using! intervalIntegral.norm_integral_le_of_norm_le_const hh

section arms

def aSeq (s : ℝ) : ℕ → Mat f G
  | 0 => A-1
  | 1 => D.pad (glide A s)
  | _+2 => -D.error (glide A s)
def sSeq (s : ℝ) : ℕ → Mat f G
  | 0 => D.flawed A
  | _+1 => -(s • D.flawed A)

lemma powers (n : ℕ) : Itinerary.product n (fun _ => A)=A^n := by induction n with
  | zero => rw [product,pow_zero]
  | succ n ih => rw [product,ih,pow_succ']
lemma product_a (s : ℝ) (n : ℕ) : Itinerary.product (n+2) (aSeq D A s)=intensity D A s n := by
  rw [product,product]; unfold intensity; congr 2
  exact powers _ n
lemma product_s (s : ℝ) (n : ℕ) : Itinerary.product (n+1) (sSeq D A s)=note (D.flawed A) s n := by
  rw [product]; unfold note; rw [show product n (fun k => sSeq D A s (k+1))=_ from powers (-(s • D.flawed A)) n]; rfl

/-- Includes all color in stamp. -/
def ArmA (p : Ledger f 3) := stamp (aSeq D A) p.2.1 p.2.2
def ArmS (p : Ledger f 1) := stamp (sSeq D A) p.2.1 p.2.2

lemma of_a {η r Q : ℝ} (h : Torch η r Q) (hg : Allow A (along S) m η r Q) (v : Bond f) (n : ℕ) :
    (∑ i : Itinerary f (n+3), ArmA D A ⟨n,v,i⟩) = ∑ j : G.ColorIndex,lact D A (v,j) (n+1) := by
  unfold ArmA stamp; rw [sum_comm]; apply sum_congr rfl; intro j _; symm
  unfold lact; simp_rw [← product_a]; apply opens S _ v
  intro i hi
  have hb := vibrate D A hg h
  match i with
  | 0 => exact continuousOn_const
  | 1 => exact hb
  | n+2 => exact ContinuousOn.neg (ContinuousOn.sub ((strung A).continuousOn.mul hb) continuousOn_const)

lemma of_s (v : Bond f) (n : ℕ) :
    (∑ i : Itinerary f (n+1), ArmS D A ⟨n,v,i⟩)=∑ j : G.ColorIndex,tick (D.flawed A) (v,j) n := by
  unfold ArmS stamp; rw [sum_comm]; apply sum_congr rfl; intro j _; symm
  unfold tick; simp_rw [← product_s]; apply opens S _ v
  intro i hi; cases i
  · exact continuousOn_const
  exact ContinuousOn.neg (continuousOn_id.smul continuousOn_const)
end arms
end Itinerary
end YM.ConnectedActivityE6.Pulse
