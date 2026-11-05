import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Weights
import YM.Push.FREE_RESOLVENT.Growth

/-!
# Actual ordered directions of polynomial growth at any base site

Require a volume receipt for *external* exponential marks, e.g. `volume`
for full physical links & colours on the output torus. No differentiation of
thresholds/flags, the supBounds ingredient is on a stated germ.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior FreeResolvent Affine Mark TestD
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {j k : ℕ} {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Cost X} {a : Edge (Site n) → X} {x o v : X} {d δ γ M s fee S : ℝ} {P : ℕ}
variable {F : Config G n → E} {V : Config G n}

def admitted (D : Cost X) (a : Edge (Site n) → X) (o : X) (P : ℕ) (fee : ℝ) (A : Directions G n) : Prop :=
  ∀ e : Edge (Site n), ‖A e‖ ≤ fee * hill D o P (a e)

def factors (B : Slab G n j) (w : Pins G n j) := ∏ i, (paint G n).symm (B i) (w i)

/-- Left derivative as *multilinear*, not a symmetric tensor. -/
theorem assembly (hf : Germ j F V) (B : Slab G n j) :
    leftDerivs F (List.ofFn B) V = ∑ w : Pins G n j, factors B w • ordered F V w := by
  have h i : B i = ∑ t : raw G n, (paint G n).symm (B i) t • unitDir t := by
    apply (paint G n).symm.injective
    ext w
    simp [unitDir,ray,Pi.single_apply]
  simp only [hf.takes B le_rfl, ordered, hf.takes _ (le_refl j)]
  nth_rw 1 [funext h]; rw [(mixed F j V).map_sum]
  exact Finset.sum_congr rfl fun w _ => (mixed F j V).map_smul_univ ..

def fieldFee (s : ℝ) (P : ℕ) (fee S : ℝ) (j : ℕ) := S^j * (fee*polynomial s P)^j
lemma fieldFee_nonneg (hs : 0 < s) (hS : 0 ≤ S) (hfee : 0 ≤ fee) : 0 ≤ fieldFee s P fee S j := by
  have he := zero_le_one.trans (poly_le P hs); unfold fieldFee; positivity

lemma factors_bound (x : X) (B : Slab G n j) (hB : ∀ i, admitted D a o P fee (B i))
    (hs : 0 < s) (hfee : 0 ≤ fee) (w : Pins G n j) :
    |factors B w| ≤ (hill D o P x)^j * (fee*polynomial s P)^j * due D a s x w := by
  rw [factors,Finset.abs_prod]
  let p := a ∘ (edge (G:=G) (n:=n))
  have hh i : |(paint G n).symm (B i) (w i)| ≤ hill D o P x * (fee*polynomial s P) * D.weight s x (p (w i)) := by
    refine (color_le (G:=G) _ _).trans ((hB i _).trans ?_)
    have H := (radial_move (D:=D) Unit o P hs).widen () x (p (w i))
    change (hill D o P x)⁻¹ ≤ polynomial _ _ * _ * (hill D o P (p (w i)))⁻¹ at H
    rw [← div_eq_mul_inv, le_div_iff₀ (hill_pos ..), inv_mul_eq_div, div_le_iff₀ (hill_pos ..)] at H
    exact (mul_le_mul_of_nonneg_left H hfee).trans_eq (by ring)
  refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hh i)).trans_eq ?_
  rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, mul_pow,
    due,Stars.pays,Stars.rays,Finset.mul_sum, Real.exp_sum]; rfl

theorem field_pay (B : Slab G n j) (N : Seminorm ℝ E)
    (hf : Germ j F V) (H : ∀ w : Pins G n j, due D a d x w * N (ordered F V w) ≤ M)
    (hB : ∀ i, admitted D a o P fee (B i)) (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hM : 0 ≤ M)
    (hv : D.Volume (a ∘ edge (G:=G)) s S) :
    (radial (Directions G n) D o P).pay (List.ofFn B) x * N (leftDerivs F (List.ofFn B) V) ≤ fieldFee s P fee S j * M := by
  let g (d) (w : Pins G n j) := due D a d x w
  have hg d w : 0 ≤ g d w := (pay_pos ..).le
  have he w : g s w ≤ g (-s) w * g d w := by
    simp only [g,due,Stars.pays,← Real.exp_add,← add_mul]
    apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by linarith) (Stars.rays_nn ..)
  have hsum : ∑ w, g (-s) w ≤ S^j := by
    simp only [g,due,Stars.pays,Stars.rays,Finset.mul_sum, Real.exp_sum]
    change ∑ w : Pins G n j, (∏ i, D.weight (-s) x (a (edge (w i)))) ≤ _
    rw [← Fintype.prod_sum (fun _ : Fin j => fun t : raw G n => D.weight (-s) x (a (edge t))),
      Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => D.weight_nn ..) (hv.bound x) j
  rw [payment,List.length_ofFn,assembly hf]
  let C := hill D o P x ^ j
  let A := (fee * polynomial s P)^j
  have hc : 0 < C := pow_pos (hill_pos ..) _
  have ha : 0 ≤ A := pow_nonneg (mul_nonneg hfee (zero_le_one.trans (poly_le _ hs))) _
  apply (mul_le_mul_of_nonneg_left (Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _) (inv_nonneg.mpr hc.le)).trans
  rw [Finset.mul_sum]; simp_rw [map_smul_eq_mul,Real.norm_eq_abs]
  calc
    _ ≤ ∑ w : Pins G n j, g (-s) w * (A*M) := Finset.sum_le_sum fun w _ => calc
      C⁻¹ * (|factors B w| * N (ordered F V w)) ≤ C⁻¹ * ((C*A*g s w) * N (ordered F V w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (factors_bound _ _ hB hs hfee _) (apply_nonneg N _)) (inv_nonneg.mpr hc.le)
      _ = A*(g s w * N (ordered F V w)) := by field_simp
      _ ≤ A*((g (-s) w * g d w) * N (ordered F V w)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (he w) (apply_nonneg N _)) ha
      _ ≤ _ := by rw [mul_assoc (g ..),mul_left_comm]; gcongr ?_ * (A * ?_); exacts [hg _ _, H w]
    _ ≤ _ := by rw [← Finset.sum_mul,fieldFee,mul_assoc]; exact mul_le_mul_of_nonneg_right hsum (mul_nonneg ha hM)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a₁ : ι → X} {b : κ → X} {F H : Config G n → Matrix ι κ ℝ}

lemma field_budget (B : Slab G n j) (hf : Germ j F V)
    (H : ∀ w : Pins G n j, Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn w) γ M (ordered F V w))
    (hB : ∀ i, admitted D a o P fee (B i)) (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hM : 0 ≤ M)
    (hv : D.Volume (a ∘ edge (G:=G)) s S) :
    Bill (radial _ D o P) D a₁ b (List.ofFn B) γ (fieldFee s P fee S j * M) (leftDerivs F (List.ofFn B) V) := by
  constructor <;> constructor <;> intro i
  · exact field_pay B (reader _ (fun q => D.weight_nn γ (a₁ i) (b q)) (fun _ => i) id) hf
      (fun w => (H w).row.rows i) hB hs hd hfee hM hv
  exact field_pay B (reader _ (fun q => D.weight_nn γ (b i) (a₁ q)) id (fun _ => i)) hf
    (fun w => (H w).col.rows i) hB hs hd hfee hM hv

theorem field_bill (l : List (Directions G n)) (hf : Germ l.length F V)
    (H : ∀ w : Pins G n l.length, Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn w) γ M (ordered F V w))
    (hB : ∀ B ∈ l, admitted D a o P fee B) (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hM : 0 ≤ M)
    (hv : D.Volume (a ∘ edge (G:=G)) s S) :
    Bill (radial _ D o P) D a₁ b l γ (fieldFee s P fee S l.length * M) (leftDerivs F l V) := by
  simpa only [List.ofFn_get] using field_budget l.get hf H (fun i => hB _ (List.get_mem l i)) hs hd hfee hM hv

variable {η Q γ' : ℝ}

lemma field_noticed (B : Slab G n j) (hf : Germ j F V)
    (H : ∀ w : Pins G n j, Noticed D a₁ b (positions D (a ∘ edge) d) η γ v (List.ofFn w) M (ordered F V w))
    (hB : ∀ i, admitted D a o P fee (B i)) (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hM : 0 ≤ M)
    (hv : D.Volume (a ∘ edge (G:=G)) s S) :
    Noticed D a₁ b (radial _ D o P) η γ v (List.ofFn B) (fieldFee s P fee S j * M) (leftDerivs F (List.ofFn B) V) := by
  constructor; intro i q
  let N (x y : X) : Seminorm ℝ (Matrix ι κ ℝ) := reader (fun _ : Unit => D.weight η x v * D.weight γ x y)
    (fun _ => mul_nonneg (D.weight_nn ..) (D.weight_nn ..)) (fun _ => i) (fun _ => q)
  have he x y (u : ℝ) T : D.weight η x v * u * (D.weight γ x y * |T i q|) = u * N x y T := by
    have : N x y T = ∑ _w : Unit, (D.weight η x v * D.weight γ x y) * |T i q| := rfl
    simp only [this,Fintype.sum_unique]; ring
  constructor
  · rw [he]; apply field_pay B _ hf (fun w => by rw [due, ← he]; exact ((H w).test i q).1) hB hs hd hfee hM hv
  rw [he]; apply field_pay B _ hf (fun w => by rw [due, ← he]; exact ((H w).test i q).2) hB hs hd hfee hM hv

/-- Lie version of tag-sensitive Schur estimates ALSO for genuine
BudgetPoint-style directions. Keeping the tag weight at each endpoint
outside the row/column sums. -/
theorem field_tagged (l : List (Directions G n)) (hf : Germ l.length F V)
    (H : ∀ w : Pins G n l.length, Noticed D a₁ b (positions D (a ∘ edge) d) η γ v (List.ofFn w) M (ordered F V w))
    (hB : ∀ B ∈ l, admitted D a o P fee B) (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hM : 0 ≤ M)
    (hS : 0 ≤ S) (hv : D.Volume (a ∘ edge (G:=G)) s S)
    (ha : D.Volume a₁ (γ-γ') Q) (hb : D.Volume b (γ-γ') Q) :
    Bill (marked D (radial _ D o P) v η) D a₁ b (markedSlots l) γ' (Q*(fieldFee s P fee S l.length * M))
      (leftDerivs F l V) := by
  have ht := field_noticed l.get hf H (fun i => hB _ (List.get_mem l i)) hs hd hfee hM hv
  rw [List.ofFn_get] at ht
  exact ht.financed (mul_nonneg (fieldFee_nonneg hs hS hfee) hM) ha hb
end YM.SelectedOrderedKernels
