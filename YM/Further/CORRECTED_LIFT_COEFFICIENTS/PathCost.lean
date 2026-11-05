import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Growth

/-!
# Position costs in the E(kpc) perturbation 

One ODE chart on fixed-size polynomial profiles (cf. FOUNDATIONS LinkBounds);
now charge all D_t order operator tensors in the unscaled slots.
Polynomial powers intentionally not optimized. No Cauchy over whole lattice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.PathCost
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops
open Push.Uniform Work Push.Corrected Push.CutoffProjectors Growth Fund
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {d : ℕ}

private abbrev Typewriter (G : Gauge) (d : ℕ) :=
    (i : Fin (d-1)) → Tensor.T (ℝ × ℝ) G.Color (i.val+1)
private def key (X : Typewriter G d) (s : ℝ) := ∑ i, Tensor.diagonal (X i) (1,s)


















lemma borrow (r s : ℕ) (h : r ≤ s) : box r ⊆ box s := fun _ hx => box_test.mpr
    ⟨fun i => le_trans (neg_le_neg (Nat.cast_le.mpr h)) ((box_test.mp hx).1 i),fun i => ((box_test.mp hx).2 i).trans (Nat.cast_le.mpr h)⟩
lemma extra {r : ℕ} {x : Cover} (h : x∈box r) (a : Lattice.Step) : x+a.vec∈box (r+1) := by
  have ht k : -(1:ℤ) ≤ (a.vec:Cover) k ∧ (a.vec:Cover) k ≤ 1 := by simp only [Step.vec]; split <;>
    simp only [Pi.neg_apply,step_apply] <;> split <;> norm_num
  obtain ⟨hh,hH⟩ := box_test.mp h
  rw [box_test]; constructor <;> intro i <;> rw [Pi.add_apply] <;> have := ht i <;> specialize hh i <;> specialize hH i <;> omega
lemma passages (r : ℕ) (w : Walk) {x : Cover} (h : x∈box r) : ∀ y∈ visits x w, y∈box (r+w.length) := by
  induction w generalizing r x with
  | nil => simpa [visits] using h
  | cons a l ih =>
    intro y hy; rcases List.mem_cons.mp hy with e|e
    · subst y; exact borrow _ _ (by omega) h
    exact (show r+1+l.length=r+(a::l).length by simp; omega) ▸ ih (r+1) (extra h a) y e
lemma limit (r : ℕ) (w : Walk) {x : Cover} (h : x∈box r) : stop x w∈box (r+w.length) := by
  apply passages r w h; clear h; induction w generalizing x <;> simp_all [visits,stop]

-- polynomial transverse chart in Snap





end YM.Further.CorrectedLift.PathCost
