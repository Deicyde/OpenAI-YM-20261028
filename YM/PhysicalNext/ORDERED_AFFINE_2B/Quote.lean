import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.PhysicalNext.ORDERED_AFFINE_2B.Charts
import YM.UVNext.PRICED_KERNELS.Echo

/-!
# Reading normalized ordered E jets from real-coordinate prices

Higher ordered derivatives may use *lower* partial derivatives at
repeated slots. Thus `narrow` spends the mark exponent once before all
orders and `surcharge` buys their true logarithmic frame coefficients.
No co-moving flags or averaging over independent tag copies is part of
this comparison. Coordinate magnitudes may grow as t'⁻ʲ but retain every
power gain for normalized directions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open WardBin.Lies FreeResolvent FreeResolvent.Affine TestD Matrix
open AnalyticBridge.SectorAffine SelectedOrderedKernels
open Push.Uniform (bolt)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Side} {j k : ℕ}

/-- Fixed-slot costs with exponential mark at *each* external argument.
Slots `Pins` include ORIENTED link (common positive basis), and color;
`ordered` uses actual RG.leftDerivs, not ordinary log charts. M priced
at unit slots; reclaim appropriate t' powers via Quote.read.
-/
structure Quote (j : ℕ) (o : Site c) (d : ℝ) (M : ℕ → ℝ) (F : Config G c → ℝ) (V : Config G c) : Prop where
  smooth : Germ j F V
  nonneg i : i ≤ j → 0 ≤ M i
  pays i (w : Pins G c i) : i ≤ j → due (native c) Prod.fst d o w * |ordered F V w| ≤ M i

/-- Quote of a vector, per row (without using a volume-losing joint norm). -/
def BundleQuote {ι : Type} (j : ℕ) (a : ι → Site c) (d : ℝ) (M : ℕ → ℝ) (F : Config G c → ι → ℝ) (V : Config G c) :=
  ∀ i, Quote j (a i) d M (fun v => F v i) V

/-- Explicit t'-conversion factor at each order (before external fields).
`surcharge` = ∑ over ordered set partitions p of [color cardinality ^
p.length times product of per-link panel-log derivative norm of each
block] (`Weights.lean`, not cardinality of ALL coordinates on the torus).
Also at j=0. -/
def orderedCost (G : Gauge) (t M : ℝ) (j : ℕ) := surcharge G j * (t⁻¹ ^ j * M)
lemma ordered_nonneg (G : Gauge) {t M : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M) (j : ℕ) : 0 ≤ orderedCost G t M j :=
  mul_nonneg (surcharge_nn ..) (mul_nonneg (pow_nonneg (inv_nonneg.mpr ht) _) hM)

variable {d t γ C : ℝ} {o p : Site c} {F : Config G c → ℝ} {V : Config G c}
lemma submits (h : Offset.Point 0 p d k (scaled t F V) C) (hd : 0 < d) (ht : 0 < t) (hu : t ≤ 1) :
    Quote k p (narrow k d) (orderedCost G t C) F V := by
  have hg := chart_over_smooth ht.ne' h.smooth
  refine ⟨smooth_over.mp hg,fun j _ => ordered_nonneg G ht.le h.nonneg j,fun j w hj => ?_⟩
  apply frame_pay (N:=normSeminorm ℝ ℝ) w (smooth_of_le hg hj) (narrow_nn k hd.le) (narrow_use hd.le hj)
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) _) h.nonneg)
  intro q u
  let l := List.ofFn (pins G c ∘ u)
  have hi := q.length_le
  rw [chart_over_jet u ht.ne' (smooth_of_le h.smooth (hi.trans hj)),← price_locations]
  change (AnalyticBridge.SectorAffine.marks G c d).pay l p * |(t⁻¹ ^ q.length) * jet bolt (scaled t F V) l 0| ≤ t⁻¹ ^ j * C
  have hb := h.bound l (List.length_ofFn.trans_le (hi.trans hj))
  rw [abs_mul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) _),mul_left_comm]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr ht.le) _)).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (one_le_inv₀ ht |>.2 hu) hi) h.nonneg)

lemma submits_bundle {ι : Type} {a : ι → Site c} {F : Config G c → ι → ℝ}
    (h : Offset.Parcel 0 a d k (scaled t F V) C) (hd : 0 < d) (ht : 0 < t) (hu : t ≤ 1) :
    BundleQuote k a (narrow k d) (orderedCost G t C) F V :=
  fun i => submits (h i) hd ht hu

variable {M : ℕ → ℝ} {l : List (Directions G c)}
/-- Actual admissible external fields on the torus, τ centered at o,
no spacing/cardinality loss. Half the REMAINING mark exponent spent
on passing to polynomial directions uniformly over *all* periods.
-/
def runCost (G : Gauge) (d t : ℝ) (P k : ℕ) := fieldFee (d/2) P t (paramPrice G (d/2)) k
lemma Quote.read (h : Quote k p d M F V) (hd : 0 < d) (P : ℕ) (ht : 0 ≤ t)
    (hl : l.length ≤ k) (ha : Afford t P o l) :
    (Mark.radial (Directions G c) (native c) o P).pay l p * |leftDerivs F l V| ≤ runCost G d t P l.length * M l.length := by
  have hh := half_pos hd
  let A := l.get
  have hf := field_pay A (normSeminorm ℝ ℝ) (h.smooth.prod hl)
    (show ∀ w, due (native c) Prod.fst d p w * normSeminorm ℝ ℝ (ordered F V w) ≤ M l.length from
      fun w => h.pays l.length w hl)
    (show ∀ i, admitted (native c) Prod.fst o P t (A i) from fun i => ha _ (List.get_mem l i))
    hh (by linarith) ht (h.nonneg _ hl) (count_volume G c hh)
  dsimp only [A] at hf; rw [List.ofFn_get] at hf; exact hf

/-- With the t'-normalized Directions, coupling powers cancel exactly.
Thus these constants need not see the period *or the delay*. -/
def sumCost (G : Gauge) (d : ℝ) (P k : ℕ) := runCost G d 1 P k * surcharge G k
lemma power_price (G : Gauge) (P k : ℕ) {t d M : ℝ} (ht : 0<t) :
    runCost G d t P k * orderedCost G t M k = sumCost G d P k * M := by
  unfold sumCost runCost fieldFee orderedCost
  rw [one_mul,mul_pow,inv_pow]; field_simp
lemma Quote.authenticated (h : Quote k p d (orderedCost G t C) F V) (hd : 0<d) (ht : 0<t) (P : ℕ)
    (hl : l.length≤k) (ha : Afford t P o l) :
    (((1+(separation p o:ℝ))^P)^l.length)⁻¹ * |leftDerivs F l V| ≤ sumCost G d P l.length*C := by
  have he := h.read hd P ht.le hl ha
  rw [Mark.payment,power_price _ _ _ ht] at he; exact he



section matrix
variable {ι ρ : Type} [Fintype ι] [Fintype ρ] {a : ι → Site c} {b : ρ → Site c}
    {A : Config G c → Matrix ι ρ ℝ}
/-- D prices require also both row and column weighted sums. Consume RAW
coordinate rates (unscaled real chart); gain positive-order smallness
for tested t'-directions. -/
lemma matrix_submits (hd : 0<d) (hC : 0 ≤ C) (h : Polar 0 a b (A ∘ AnalyticBridge.SectorAffine.field V) k d C) :
    SelectedOrderedKernels.Book (native c) a b Prod.fst k (narrow k d) d (orderedCost G 1 C) A V := by
  have he : scaled 1 A V = A ∘ AnalyticBridge.SectorAffine.field V := by unfold scaled; simp [comp_def]
  have hh : Polar 0 a b (scaled 1 A V) k d C := he ▸ h
  unfold orderedCost; simp_rw [inv_one,one_pow,one_mul]
  refine lease (M:=fun _ => C) (chart_over_smooth one_ne_zero hh.smooth) (narrow_nn k hd.le)
    (narrow_use hd.le le_rfl) (fun j _ => hC) ?_
  intro j hj p w
  have hl := hh.bound (List.ofFn (pins G c ∘ w)) (List.length_ofFn.trans_le (p.length_le.trans hj))
  rw [chart_over_jet w one_ne_zero (smooth_of_le hh.smooth (p.length_le.trans hj)),inv_one,one_pow,one_smul]
  constructor <;> constructor <;> intro i
  · have hb := hl.row.rows i; rw [price_locations] at hb; exact hb
  have hb := hl.col.rows i; rw [price_locations] at hb; exact hb

lemma matrix_pays (h : SelectedOrderedKernels.Book (native c) a b Prod.fst k d γ (orderedCost G 1 C) A V)
    (hd : 0<d) (P : ℕ) (ht : 0≤t) (hl : l.length≤k) (ha : Afford t P o l) :
    Mark.Bill (Mark.radial (Directions G c) (native c) o P) (native c) a b l γ
      (t^l.length * sumCost G d P l.length*C) (leftDerivs A l V) := by
  have he := h.fields l hl (show ∀ B ∈ l, admitted _ _ o P t B from ha) (half_pos hd) (by linarith) ht
    (count_volume G c (half_pos hd))
  unfold sumCost runCost fieldFee orderedCost at *
  rw [mul_pow,inv_one,one_pow,one_mul] at he
  -- RHS arithmetic only
  refine he.mono le_rfl (le_of_eq ?_); ring
end matrix
end YM.PhysicalNext.OrderedAffine2B
