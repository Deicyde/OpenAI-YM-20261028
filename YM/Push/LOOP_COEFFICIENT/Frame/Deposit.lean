import YM.Push.LOOP_COEFFICIENT.Frame.Imprint

/-!
# Weighted averaging of heterogeneous imprints and implicit expansion prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Filter Set YM.Branch
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
  {k n : ℕ} {s : Scope E} {m m' : E → ℝ} {A B D : ℝ} {x : E}
lemma Legacy.nonneg {f : E → F} (h : Legacy s m f x k A) : 0 ≤ A := (h.levels _ le_rfl).nonneg
lemma Legacy.mono {f : E → F} (h : Legacy s m f x k A) (hm : ∀ i,0≤m i) (hb : A≤B) : Legacy s m f x k B := ⟨fun i hi => (h.levels i hi).top hm hb⟩
lemma Legacy.majorize {f : E → F} (h : Legacy s m f x k A) (hm : ∀ i, m i ≤ m' i) : Legacy s m' f x k A := ⟨fun i hi => (h.levels i hi).majorize hm⟩
lemma Legacy.prod {f : E → F} {g : E → H} (h : Legacy s m f x k A) (h' : Legacy s m g x k A) (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) : Legacy s m (fun y => (f y,g y)) x k A := ⟨fun i hi => (h.levels i hi).prod (h'.levels i hi) hf hg⟩

def weighted {ι X : Type} [Fintype ι] [AddCommMonoid X] [Module ℝ X] (a : ι → ℝ) (v : ι → X) := ∑ i,a i • v i
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma Imprint.mean {f : ι → (Fin k → E) → F} {d : ι → E → ℝ} (a : ι → ℝ) (ha : ∀ i,0≤a i) (ht : ∑ i,a i=1) (hA : 0≤A) (h : ∀ i,Imprint s (d i) (f i) A) (hm : ∀ x,weighted a (fun i => d i x) ≤ m x) : Imprint s m (fun w => weighted a (fun i => f i w)) A := by
  have he (u : ι → F) (v : ι → ℝ) (h : ∀ i, ‖u i‖ ≤ A*v i) : ‖weighted a u‖ ≤ A*(weighted a v) := (norm_sum_le ..).trans (by
    simp only [norm_smul,Real.norm_of_nonneg (ha _),Frames.weighted,smul_eq_mul,Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => (mul_le_mul_of_nonneg_left (h i) (ha i)).trans_eq (mul_left_comm ..))
  have ht' : weighted a (fun _ => (1:ℝ)) = 1 := by simpa [Frames.weighted] using ht
  exact ⟨hA,fun w hw => by simpa only [ht',mul_one] using! he _ _ (fun i => (h i |>.plain w hw).trans (show A ≤ A*1 by simp)),fun w j hw => (he _ _ (fun i => (h i).uneven w j hw)).trans (mul_le_mul_of_nonneg_left (hm _) hA)⟩
lemma iterated_weighted (a : ι → ℝ) (f : ι → E → F) (hf : ∀ i, ContDiffAt ℝ ω (f i) x) (w : Fin k → E) : iteratedFDeriv ℝ k (fun x => weighted a (fun i => f i x)) x w = weighted a (fun i => iteratedFDeriv ℝ k (f i) x w) := by
  rw [show (fun x => weighted a (fun i => f i x)) = ∑ i,a i • f i from funext fun x => by simp [Frames.weighted,Finset.sum_apply], iteratedFDeriv_sum_apply (f:=fun i => a i • f i) (fun i _ => ((hf i).const_smul (a i)).of_le le_top),_root_.sum_apply]; exact Finset.sum_congr rfl fun i _ => by rw [iteratedFDeriv_const_smul_apply ((hf i).of_le le_top),_root_.smul_apply]
lemma Legacy.mean {f : ι → E → F} {d : ι → E → ℝ} (a : ι → ℝ) (ha : ∀ i,0≤a i) (ht : ∑ i,a i=1) (hA : 0≤A) (hf : ∀ i, ContDiffAt ℝ ω (f i) x) (h : ∀ i,Legacy s (d i) (f i) x k A) (hm : ∀ x,weighted a (fun i => d i x) ≤ m x) : Legacy s m (fun y => weighted a (fun i => f i y)) x k A := by
  constructor; intro i hi; unfold Engrave; rw [show ⇑(iteratedFDeriv ℝ i _ x) = _ from funext (iterated_weighted (k:=i) a f hf)]
  exact Imprint.mean a ha ht hA (fun j => (h j).levels i hi) hm
lemma weighted_diff (a : ι → ℝ) (f : ι → E → F) (hf : ∀ i,ContDiffAt ℝ ω (f i) x) : ContDiffAt ℝ ω (fun y => weighted a (fun i => f i y)) x := ContDiffAt.sum fun i _ => (hf i).const_smul _





end YM.Push.Loops.Frames
