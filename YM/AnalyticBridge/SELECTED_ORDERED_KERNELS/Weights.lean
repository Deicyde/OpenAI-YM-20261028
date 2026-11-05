import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Slots
import YM.Push.FREE_RESOLVENT.Fees
import YM.Push.FREE_RESOLVENT.TensorPrice
import YM.Work.D03

/-!
# Endpoint and external-argument exponential budgets under conversion

Work with arbitrary seminorms of the output (e.g. an absolute exponential
row or column, even a point budget carrying an additional tag weight). To
regain weights to ALL external indices, *including repeats at one link in
a correction term*, reserve a multiple of the mark rate ONCE by maximum
order, not just a combinatorial prefactor. No extra pay per volume or block.
Does not convert a zero-order bound into higher-order bounds! Through the
order tested need ordinary derivative estimates on the SAME log chart germ.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior FreeResolvent Affine Mark TestD
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {j k : ℕ} {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Placement price at a probing anchor. -/
def due (D : Cost X) (a : Edge (Site n) → X) (d : ℝ) (x : X) (z : Pins G n j) :=
  (positions D (a ∘ edge) d).pay (List.ofFn z) x

lemma regather (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (c : Fin p.length → G.ColorIndex) (hc : ∏ b, coeff φ p z b (c b) ≠ 0)
    (D : Cost X) (a : Edge (Site n) → X) {d δ : ℝ} (x : X) (hδ : 0 ≤ δ) (hd : j*δ ≤ d) :
    due D a δ x z ≤ due D a d x (fun b => repaint p z b (c b)) := by
  simp only [due,Stars.pays,Stars.rays,repaint,Function.comp_apply,edge_hue]
  apply Real.exp_monotone
  rw [← p.sum_sigma_eq_sum (fun i => D.d x (a (edge (z i)))),Finset.mul_sum,Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have he := Finset.prod_ne_zero_iff.mp hc b (Finset.mem_univ _)
  simp_rw [coeff_support φ p z b (c b) he]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_assoc,mul_comm δ]
  -- use pseudometric nonnegativity
  gcongr
  · exact D.nonneg ..
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (p.partSize_le b)) hδ).trans hd

/-- Gauge/finite-order conversion surcharge when the edge coefficient at
order i of one panel log is bounded by m i. -/
def fare (G : Gauge) (j : ℕ) (m : ℕ → ℝ) := ∑ p : OrderedFinpartition j,
    (Fintype.card G.ColorIndex:ℝ)^p.length * ∏ b, m (p.partSize b)

def surcharge (G : Gauge) (j : ℕ) := fare G j (fun i => ‖iteratedFDeriv ℝ i (frame G j) 0‖)
lemma fare_nonneg (G : Gauge) (j : ℕ) (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) : 0 ≤ fare G j m := by
  unfold fare
  exact Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => hm _)
lemma surcharge_nn (G : Gauge) (j : ℕ) : 0 ≤ surcharge G j := fare_nonneg _ _ _ fun _ => norm_nonneg _

/-- Do not degrade the matrix rate γ in this conversion. The exponent on
*external marks* is shrunk to permit coalescence of derivative slots. -/
def narrow (k : ℕ) (d : ℝ) := d / (k+1:ℕ)
lemma narrow_pos (k : ℕ) {d : ℝ} (hd : 0 < d) : 0 < narrow k d := div_pos hd (by positivity)
lemma narrow_nn (k : ℕ) {d : ℝ} (hd : 0 ≤ d) : 0 ≤ narrow k d := div_nonneg hd (by positivity)
lemma narrow_le (k : ℕ) {d : ℝ} (hd : 0 ≤ d) : narrow k d ≤ d := div_le_self hd (by push_cast; linarith [show (0:ℝ)≤k by positivity])
lemma narrow_use {d : ℝ} (hd : 0 ≤ d) (h : j ≤ k) : j * narrow k d ≤ d := by
  refine (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (Nat.le_succ_of_le h)) (narrow_nn k hd)).trans ?_
  rw [mul_comm,narrow,div_mul_cancel₀ _ (by positivity)]

variable {a : Edge (Site n) → X} {D : Cost X} {x : X} {d δ γ M : ℝ} {m : ℕ → ℝ}

private lemma pay_sum {ι : Type*} [Fintype ι] (N : Seminorm ℝ E) (f : ι → E) (M : ι → ℝ) (z : Pins G n j)
    (h : ∀ i, due D a δ x z * N (f i) ≤ M i) : due D a δ x z * N (∑ i, f i) ≤ ∑ i, M i := by
  apply (mul_le_mul_of_nonneg_left (Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ f)
    (show 0 ≤ due D a δ x z from (pay_pos ..).le)).trans
  rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => h i

theorem partition_pay (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (N : Seminorm ℝ E) (L : Vec G n 1 [×p.length]→L[ℝ] E) (hδ : 0 ≤ δ) (hd : j*δ ≤ d) (hM : 0 ≤ M)
    (hφ : ∀ b e, ‖iteratedFDeriv ℝ (p.partSize b) (φ e) 0‖ ≤ m (p.partSize b))
    (H : ∀ w : Pins G n p.length, due D a d x w * N (L (ray G n ∘ w)) ≤ M) :
    due D a δ x z * N (L ((paint G n).symm ∘ term φ p (unitDir ∘ z))) ≤
      ((Fintype.card G.ColorIndex:ℝ)^p.length * ∏ b, m (p.partSize b)) * M := by
  let B := (∏ b, m (p.partSize b)) * M
  have hb : 0 ≤ B := mul_nonneg (Finset.prod_nonneg fun b _ => (norm_nonneg _).trans (hφ b (pivot p z b))) hM
  rw [palette,show ((Fintype.card G.ColorIndex:ℝ)^p.length * ∏ b, m (p.partSize b)) * M =
    ∑ _c : Fin p.length → G.ColorIndex, B from by simp [B,mul_assoc]]
  apply pay_sum N; intro c
  let r := ∏ b, coeff φ p z b (c b)
  change due _ _ _ _ _ * N (r • _) ≤ B
  by_cases he : r=0
  · rw [he,zero_smul,map_zero,mul_zero]; exact hb
  let w : Pins G n p.length := fun b => repaint p z b (c b)
  rw [map_smul_eq_mul,mul_left_comm]
  refine mul_le_mul ?_ ((mul_le_mul_of_nonneg_right (regather φ p z c he D a x hδ hd)
    (apply_nonneg N _)).trans (H w)) (mul_nonneg (pay_pos ..).le (apply_nonneg N _)) ?_
  · rw [Real.norm_eq_abs,Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun b _ => (coeff_bound φ p z b (c b)).trans (hφ b _)
  exact Finset.prod_nonneg fun b _ => (norm_nonneg _).trans (hφ b (pivot p z b))

variable {F H : Config G n → E} {V : Config G n}

theorem frame_pay (z : Pins G n j) (N : Seminorm ℝ E) (h : ContDiffAt ℝ j (over F V) 0) (hδ : 0 ≤ δ)
    (hd : j*δ ≤ d) (hM : 0 ≤ M) (hf : ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      due D a d x w * N (jet (ray G n) (over F V) (List.ofFn w) 0) ≤ M) :
    due D a δ x z * N (ordered F V z) ≤ surcharge G j * M := by
  rw [ordered,expand_over _ h,surcharge,fare,Finset.sum_mul]
  simp_rw [Stars.list_result] at hf
  exact pay_sum N _ _ _ fun p => partition_pay (m:=fun i => ‖iteratedFDeriv ℝ i (frame G j) 0‖) _ _ z N _ hδ hd hM (fun _ _ => le_rfl) (hf p)

section seminorms
variable {ι κ η : Type*} [Fintype η]

def reader (w : η → ℝ) (hw : ∀ e, 0 ≤ w e) (i : η → ι) (q : η → κ) : Seminorm ℝ (Matrix ι κ ℝ) where
  toFun A := ∑ t, w t * |A (i t) (q t)|
  map_zero' := by simp
  add_le' A B := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun t _ => (mul_le_mul_of_nonneg_left
      (abs_add_le ..) (hw t)).trans_eq (mul_add ..)
  neg' A := by simp
  smul' c A := by simp_rw [Matrix.smul_apply,smul_eq_mul,abs_mul,mul_left_comm _ |c|,Real.norm_eq_abs,Finset.mul_sum]
end seminorms

section physical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a₁ : ι → X} {b : κ → X} {F H : Config G n → Matrix ι κ ℝ}

/-- Fixed-slot Schur prices. -/
theorem frame_bill (z : Pins G n j) (h : ContDiffAt ℝ j (over F V) 0) (hδ : 0 ≤ δ)
    (hd : j*δ ≤ d) (hM : 0 ≤ M) (hf : ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn w) γ M (jet (ray G n) (over F V) (List.ofFn w) 0)) :
    Bill (positions D (a ∘ edge) δ) D a₁ b (List.ofFn z) γ (surcharge G j * M) (ordered F V z) := by
  constructor <;> constructor <;> intro i
  · exact frame_pay z (reader (fun j => D.weight γ (a₁ i) (b j)) (fun _ => D.weight_nn ..) (fun _ => i) id)
      h hδ hd hM (fun p w => (hf p w).row.rows i)
  exact frame_pay z (reader (fun j => D.weight γ (b i) (a₁ j)) (fun _ => D.weight_nn ..) id (fun _ => i))
    h hδ hd hM (fun p w => (hf p w).col.rows i)

/-- Entrywise version with an extra fixed tag mark at v, in BOTH matrix
anchor conventions. Useful between changes of width, or before summing
also over derivative arguments. Does not encode smoothness separately.
Can be used on an ordered derivative of a DIFFERENCE on the same germ. -/
structure Noticed {τ : Type*} (D : Cost X) (a : ι → X) (b : κ → X) (C : Mark τ X) (η γ : ℝ)
    (v : X) (l : List τ) (M : ℝ) (T : Matrix ι κ ℝ) : Prop where
  test (i : ι) (q : κ) : D.weight η (a i) v * C.pay l (a i) * (D.weight γ (a i) (b q) * |T i q|) ≤ M ∧
    D.weight η (b q) v * C.pay l (b q) * (D.weight γ (b q) (a i) * |T i q|) ≤ M

def marked {τ : Type*} (D : Cost X) (C : Mark τ X) (v : X) (η : ℝ) : Mark (Option τ) X :=
  ⟨fun t x => t.elim (D.weight η x v) (C.cents · x), fun t x => by
    cases t
    · exact D.weight_pos ..
    exact C.pos ..⟩

def markedSlots {τ : Type*} (l : List τ) : List (Option τ) := none :: l.map some
lemma marked_price {τ : Type*} (D : Cost X) (C : Mark τ X) (v : X) (η : ℝ) (l : List τ) (x : X) :
    (marked D C v η).pay (markedSlots l) x = D.weight η x v * C.pay l x := by
  change _ * _ = _ * _; congr 1
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons,pay,ih,pay]; rfl

variable {v : X} {η s P : ℝ}

lemma Noticed.financed {τ : Type*} {C : Mark τ X} {l : List τ} {T : Matrix ι κ ℝ}
    (h : Noticed D a₁ b C η γ v l M T) (hM : 0 ≤ M) (ha : D.Volume a₁ (γ-s) P) (hb : D.Volume b (γ-s) P) :
    Bill (marked D C v η) D a₁ b (markedSlots l) s (P*M) T := by
  apply Bill.of_entry hb ha hM <;> intro i j <;> rw [marked_price]
  · exact (h.test i j).1
  exact (h.test i j).2

lemma frame_point (z : Pins G n j) (h : ContDiffAt ℝ j (over F V) 0) (hδ : 0 ≤ δ)
    (hd : j*δ ≤ d) (hM : 0 ≤ M) (hf : ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      Noticed D a₁ b (positions D (a ∘ edge) d) η γ v (List.ofFn w) M (jet (ray G n) (over F V) (List.ofFn w) 0)) :
    Noticed D a₁ b (positions D (a ∘ edge) δ) η γ v (List.ofFn z) (surcharge G j * M) (ordered F V z) := by
  constructor; intro i q
  let N (x y : X) : Seminorm ℝ (Matrix ι κ ℝ) := reader (fun _ : Unit => D.weight η x v * D.weight γ x y)
    (fun _ => mul_nonneg (D.weight_nn ..) (D.weight_nn ..)) (fun _ => i) (fun _ => q)
  have he (x y : X) {j : ℕ} (z : Pins G n j) (δ : ℝ) T :
      D.weight η x v * (positions D (a ∘ edge) δ).pay (List.ofFn z) x * (D.weight γ x y * |T i q|) =
      due D a δ x z * N x y T := by
    have : N x y T = ∑ _u : Unit, (D.weight η x v * D.weight γ x y) * |T i q| := rfl
    simp only [this,Fintype.sum_unique,due]; ring
  constructor <;> rw [he] <;> apply frame_pay _ _ h hδ hd hM <;> intro p w <;> rw [← he]
  · exact ((hf p w).test i q).1
  exact ((hf p w).test i q).2

theorem frame_here {F H : Config G n → Matrix ι ι ℝ} (z : Pins G n j)
    (hH : ContDiffAt ℝ j (over H V) 0) (hF : ContDiffAt ℝ j (over F V) 0) (hδ : 0 ≤ δ)
    (hd : j*δ ≤ d) (hM : 0 ≤ M) (hf : ∀ p : OrderedFinpartition j, ∀ w : Pins G n p.length,
      Lever.Here (ray G n) D a₁ (a ∘ edge) d γ v (List.ofFn w) M (over H V) (over F V)) :
    Noticed D a₁ a₁ (positions D (a ∘ edge) δ) d γ v (List.ofFn z) (surcharge G j * M) (ordered (F-H) V z) := by
  apply frame_point z (show ContDiffAt ℝ j (over (F-H) V) 0 from hF.sub hH) hδ hd hM
  intro p w
  rw [show over (F-H) V = (fun y => over F V y-over H V y) from rfl,
    jet_sub (ray G n) _ (smooth_of_le hF (List.length_ofFn.trans_le p.length_le))
      (smooth_of_le hH (List.length_ofFn.trans_le p.length_le))]
  exact ⟨(hf p w).test⟩

end physical
end YM.SelectedOrderedKernels
