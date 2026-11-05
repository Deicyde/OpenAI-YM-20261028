import YM.Next.FLUCTUATIONS.Defs
import YM.Work.E03
import YM.Work.F03.Metric

/-!
# The full linear cancellation on the torus

E (5717--30). Flat here means full and real. Use *the same*
S,T,V channel for all three operators. In particular the extra gradient
in `probe` (fixed-root evaluation of predictor) is killed using Roll.n.
Doesn't assume closed cochains as input, or exclude harmonic modes;
`Roll.m` is applied even on arbitrary two-layer data.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Matrix Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n c f : Side} {S : StepData c f}

lemma xLin_component (A : Clip) (P : PathData G) (B : Bed) {σ C Λ}
    (h : P.Bounds A σ C Λ) (hl : Attached B P) (a : LogField G n) (i : Twin n) (k : G.ColorIndex) :
    xLin A P a i k = ((B.full A n * d 1 n) *ᵥ parts G 1 a k) (mesh i) := by
  rw [← mulVec_mulVec]
  rcases i with ⟨i,j|j⟩
  · symm
    change (∑ j : Body 2 n, (Real.sqrt A.direct *
      (1 : Matrix (Body 2 n) (Body 2 n) ℝ) (i.1, plaquette i.2) j) *
        (d 1 n *ᵥ parts G 1 a k) j) = _
    simp_rw [mul_assoc]; rw [← Finset.mul_sum]
    change Real.sqrt A.direct * ((1 : Matrix (Body 2 n) (Body 2 n) ℝ) *ᵥ (d 1 n *ᵥ _)) _ = _
    rw [one_mulVec]; rfl
  exact Work.F03.ellLine_mulVec B h hl i a k

private lemma adjoint_scalar (x : ℝ) : (scalar G x).adjoint = scalar G x := by
  simp [scalar]

section functional
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  (A : Matrix α β ℝ) (p : γ ≃ α) (q : δ ≃ β)

private lemma component_sum {m : Type*} [Fintype m] (u : m → G.Color) (k) :
    (∑ i, u i) k = ∑ i, u i k := by
  let f : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj k)
    (WithLp.linearEquiv 2 ℝ _).toLinearMap
  exact map_sum f _ _

omit [Fintype α] [Fintype γ] in
lemma scalar_zip (w : δ → G.Color) (i : γ) (k : G.ColorIndex) :
    zip (fun i j => scalar G (A (p i) (q j))) w i k = (A *ᵥ fun j => w (q.symm j) k) (p i) := by
  unfold zip
  rw [component_sum, mulVec, dotProduct, ← q.sum_comp]; simp [scalar]

omit [Fintype β] [Fintype δ] in
lemma scalar_unzip (w : γ → G.Color) (j : δ) (k : G.ColorIndex) :
    unzip (fun i j => scalar G (A (p i) (q j))) w j k = (A.transpose *ᵥ fun i => w (p.symm i) k) (q j) := by
  unfold unzip
  simp_rw [adjoint_scalar]; exact scalar_zip A.transpose q p w j k

lemma scalar_unzip_zip (w : δ → G.Color) (j : δ) (k : G.ColorIndex) :
    let F := fun (i : γ) (j : δ) => scalar G (A (p i) (q j))
    unzip F (zip F w) j k = ((A.transpose*A) *ᵥ fun j => w (q.symm j) k) (q j) := by
  dsimp only
  rw [scalar_unzip A p q]; simp_rw [scalar_zip A p q, Equiv.apply_symm_apply]; rw [mulVec_mulVec]
end functional

lemma roll_d (T : Tube G S) {H H' : Bed} (ht : Towers.Roll S H H' T.R T.high T.low)
    (w : Twin c → G.Color) (j : Twin c) :
    w j - (unzip (flatF T) (zip (flatF T) w) j + unzip (flatI T) (zip (flatI T) w) j +
      unzip (flatN T) (zip (flatN T) w) j) = 0 := by
  let s := Work.E03.meshEquiv c
  let t := Work.E03.meshEquiv f
  let e := Work.E03.poleEquiv c
  ext k
  change w j k - (unzip (flatF T) (zip (flatF T) w) j k + unzip (flatI T) (zip (flatI T) w) j k + unzip (flatN T) (zip (flatN T) w) j k) = 0
  have hf := scalar_unzip_zip (installed S.ratio T.R.mf) t s w j k
  have hb := scalar_unzip_zip (T.R.mn.acts c) e s w j k
  have hz := scalar_unzip_zip (T.R.o.acts c) (Equiv.refl _) s w j k
  let v := fun i => w (s.symm i) k
  rw [show unzip (flatF T) (zip (flatF T) w) j k = (((installed S.ratio T.R.mf).transpose * installed S.ratio T.R.mf) *ᵥ v) (s j) from hf,
    show unzip (flatI T) (zip (flatI T) w) j k = (((T.R.mn.acts c).transpose * T.R.mn.acts c) *ᵥ v) (s j) from hb,
    show unzip (flatN T) (zip (flatN T) w) j k = (((T.R.o.acts c).transpose * T.R.o.acts c) *ᵥ v) (s j) from hz]
  have he := congr_fun (congr_arg (· *ᵥ v) ht.m) (s j)
  simp only [Matrix.add_mulVec, Pi.add_apply, Matrix.one_mulVec, v, Equiv.symm_apply_apply] at he
  exact sub_eq_zero.mpr he.symm

lemma roll_l (T : Tube G S) {H H' : Bed} (ht : Towers.Roll S H H' T.R T.high T.low)
    {σ C Λ η D Λ' : ℝ} -- only path alignment and bounds used for ell
    (hp : T.up.Bounds T.high σ C Λ) (hq : T.down.Bounds T.low η D Λ')
    (hf : Attached H T.up) (hc : Attached H' T.down)
    (a : LogField G f) (b : LogField G c) (j : Twin c) :
    unzip (flatF T) (xLin T.high T.up a) j + unzip (flatI T) (zLin S a b) j -
      xLin T.low T.down b j = 0 := by
  let r := Real.sqrt S.kernel.penalty
  let s := Work.E03.meshEquiv c
  let t := Work.E03.meshEquiv f
  let e := Work.E03.poleEquiv c
  let A := installed S.ratio T.R.mf
  let N := T.R.mn.acts c
  let B := H.full T.high f*d 1 f
  let Y := H'.full T.low c*d 1 c
  have hn : r • N.transpose = Y := ht.n
  have hr : A.transpose*B - (r • N.transpose)*probe S = 0 := by
    have hh : A.transpose*B = (r • N.transpose)*mean S := by
      have h := ht.orthogonal
      change A.transpose*B + N.transpose * (-r • mean S) = 0 at h
      simpa only [smul_mul, neg_smul, Matrix.mul_neg, Matrix.mul_smul, ← sub_eq_add_neg, sub_eq_zero] using h
    rw [probe, Matrix.mul_add, hh, hn]
    simp only [Y, Matrix.mul_assoc, ← Matrix.mul_assoc (d 1 c) (d 0 c), Exterior.closed 0,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_self]
  ext k
  let u := parts G 1 a k
  let v := parts G 1 b k
  have hf' : (fun i => xLin T.high T.up a (t.symm i) k) = B *ᵥ u := by
    funext i
    rw [xLin_component T.high T.up H hp hf]
    change (B *ᵥ u) (t (t.symm i)) = _; rw [Equiv.apply_symm_apply]
  have hz' : (fun i => zLin S a b (e.symm i) k) = r • (v - probe S *ᵥ u) := by
    funext i
    unfold zLin
    change r * (b (e (e.symm i)) k - (probe S *ᵥ u) (e (e.symm i))) = _
    rw [Equiv.apply_symm_apply]; rfl
  have hl : A.transpose *ᵥ (B *ᵥ u) + N.transpose *ᵥ (r • (v - probe S *ᵥ u)) = Y *ᵥ v := by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, Matrix.mulVec_sub, mulVec_mulVec, mulVec_mulVec,
      sub_eq_zero.mp hr, hn]; abel
  have h1 := scalar_unzip A t s (xLin T.high T.up a) j k
  have h2 := scalar_unzip N e s (zLin S a b) j k
  rw [hf'] at h1; rw [hz'] at h2
  change (unzip (flatF T) _ j k + unzip (flatI T) _ j k) - xLin T.low T.down b j k = 0
  rw [xLin_component T.low T.down H' hq hc]
  apply sub_eq_zero.mpr
  rw [show unzip (flatF T) _ j k = (A.transpose *ᵥ _) (s j) from h1,
    show unzip (flatI T) _ j k = (N.transpose *ᵥ _) (s j) from h2]
  exact congr_fun hl (s j)

end YM.Next.Fluctuations
