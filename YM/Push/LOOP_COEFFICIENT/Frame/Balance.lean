import YM.Push.LOOP_COEFFICIENT.Frame.Deposit



set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H] {s : Scope E} {k : ℕ} {m m' : E → ℝ} {A B C K : ℝ} {f : (Fin k → E) → F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Imprint.move (h : Imprint s m f A) (hC : 1≤C) (hm : ∀ i, m i ≤ C*m' i) : Imprint s m' f (A*C) := ⟨by have := h.nonneg; positivity,fun w hw => (h.plain w hw).trans (le_mul_of_one_le_right h.nonneg hC),fun w j hw => (h.uneven w j hw).trans ((mul_le_mul_of_nonneg_left (hm _) h.nonneg).trans_eq (mul_assoc ..).symm)⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Imprint.neg (h : Imprint s m f A) : Imprint s m (fun w => -f w) A := ⟨h.nonneg,fun w hw => (norm_neg _).trans_le (h.plain w hw),fun w j hw => (norm_neg _).trans_le (h.uneven w j hw)⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Imprint.sub {g : (Fin k → E) → F} (h : Imprint s m f A) (h' : Imprint s m g B) : Imprint s m (fun w => f w - g w) (A+B) := by simpa only [sub_eq_add_neg] using h.add h'.neg
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma Imprint.linear (L : F →L[ℝ] H) (h : Imprint s m f A) : Imprint s m (L ∘ f) (‖L‖*A) := ⟨by have := h.nonneg; positivity,fun w hw => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.plain w hw) (norm_nonneg _)),fun w j hw => (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.uneven w j hw) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)⟩
variable {a : ι → ℝ} (ha : ∀ i,0≤a i) (hSum : ∑ i,a i=1) {m : ι → E → ℝ} (hm : ∀ i x, 1≤m i x) (hB : 1≤B) (hK : 0≤K) (hcost : ∀ x, Frames.weighted a (fun i => m i x) ≤ B)
include ha hSum hB hK hcost
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma Imprint.blend (f : ι → (Fin k → E) → F) (h : ∀ i, Imprint s (m i) (f i) K) : Imprint s (fun _ => 1) (fun w => weighted a (fun i => f i w)) (K*B) := (Imprint.mean a ha hSum hK h (fun _ => le_rfl)).move hB (by simpa)
include hm
variable (L : F →L[ℝ] F) (hL : ∀ x, L (L x)=L x)
include hL
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma balance_cost (f : ι → (Fin k → E) → F) (b : (Fin k → E) → F) (hb : ∀ i,Imprint s (m i) (fun w => f i w - L (b w)) K) (h : Imprint s (fun _ => 1) (fun w => L (weighted a (fun i => f i w))) A) (i : ι) : Imprint s (m i) (f i) ((A + ‖L‖*(K*B)) + K) := by
  let e i w := f i w - L (b w)
  have he := Imprint.blend ha hSum hB hK hcost e hb |>.linear L
  have hx (w) : L (weighted a (fun i => f i w)) - L (weighted a (fun i => e i w)) = L (b w) := by simp only [e,weighted,smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hSum,one_smul,map_sub,hL,sub_sub_cancel]
  have hh := h.sub he
  change Imprint s (fun _ => 1) (fun w => L _ - L (weighted a (fun i => e i w))) _ at hh
  exact (funext (fun w => show L (weighted a (fun i => f i w)) - L (weighted a (fun i => e i w)) + e i w = f i w by rw [hx]; unfold e; abel)) ▸ ((hh.majorize (hm i)).add (hb i))
end YM.Push.Loops.Frames
