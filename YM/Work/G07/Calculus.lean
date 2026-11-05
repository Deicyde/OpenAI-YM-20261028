import YM.Gauge.Chart
import YM.RG.Masks


/-!
# Ordered derivatives for the proof of G07

Small algebra of globally smooth functions of links (as seen by increments),
truncated order bounds `c * r ^ length` on any direction and base-point
test sets. `r` can e.g. be the threshold, to charge link variations, or 1,
to charge products of curvature factors, where each factor already pays a
threshold at all the tested orders. Finitary, no uniformity in the maximum
order. No symmetry of mixed derivatives used here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G07
open RG Lattice Wilson
open scoped ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {k m : ℕ}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Config G n → E}

theorem at_zero_increment (U : Config G n) : increment U 0 = U := by
  funext e; simp [increment]

/-- Truncate how many ordered derivatives we're keeping. All are globally
smooth when read in increments around any configuration. -/
def LeftSmooth (k : ℕ) (f : Config G n → E) : Prop :=
  ∀ l : List (Directions G n), l.length ≤ k → ∀ U : Config G n,
    ContDiff ℝ ∞ (fun v => leftDerivs f l (increment U v))

theorem LeftSmooth.truncate (hf : LeftSmooth k f) (h : m ≤ k) : LeftSmooth m f :=
  fun l hl U => hf l (hl.trans h) U

theorem LeftSmooth.has (hf : LeftSmooth k f) {l} (hl : List.length l ≤ k)
    (U : Config G n) (A : Directions G n) :
    HasDerivAt (fun t : ℝ => leftDerivs f l (increment U (t • A)))
      (leftDerivs f (A::l) U) 0 := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => leftDerivs f l (increment U (t • A))) :=
    (hf l hl U).comp (show ContDiff ℝ ∞ (fun t : ℝ => t • A) from contDiff_id.smul contDiff_const)
  exact ((hs.differentiable (by simp)) 0).hasDerivAt

theorem left_append (f : Config G n → E) (l l' : List (Directions G n)) :
    leftDerivs f (l ++ l') = leftDerivs (leftDerivs f l') l := by
  induction l with
  | nil => rfl
  | cons A l ih => funext U; simp only [List.cons_append, leftDerivs, ih]

theorem LeftSmooth.inner_derivative (hf : LeftSmooth (k+1) f) (A : Directions G n) :
    LeftSmooth k (leftDerivs f [A]) := by
  intro l hl U
  simp only [← left_append]; apply hf
  simpa only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right]

theorem left_add (hf : LeftSmooth k f) (hg : LeftSmooth k g) {l}
    (hl : List.length l ≤ k) :
    leftDerivs (fun U => f U + g U) l = fun U => leftDerivs f l U + leftDerivs g l U := by
  induction l with
  | nil => rfl
  | cons A l ih =>
    have hm : l.length ≤ k := (by simp at hl; omega)
    funext U
    change deriv (fun t : ℝ => leftDerivs _ l (increment U (t • A))) 0 = _
    simp only [ih hm]; exact ((hf.has hm U A).add (hg.has hm U A)).deriv

theorem LeftSmooth.add (hf : LeftSmooth k f) (hg : LeftSmooth k g) :
    LeftSmooth k fun U => f U + g U := by
  intro l hl U
  simp only [left_add hf hg hl]; exact (hf _ hl U).add (hg _ hl U)

theorem left_linear (hf : LeftSmooth k f) (L : E →L[ℝ] F) {l}
    (hl : List.length l ≤ k) :
    leftDerivs (fun U => L (f U)) l = fun U => L (leftDerivs f l U) := by
  induction l with
  | nil => rfl
  | cons A l ih =>
    have hm : l.length ≤ k := (by simp at hl; omega)
    funext U
    change deriv (fun t : ℝ => leftDerivs _ l (increment U (t • A))) 0 = _
    simp only [ih hm]; exact (L.hasFDerivAt.comp_hasDerivAt 0 (hf.has hm U A)).deriv

theorem LeftSmooth.postcomp (hf : LeftSmooth k f) (L : E →L[ℝ] F) :
    LeftSmooth k fun U => L (f U) := by
  intro l hl U
  simp only [left_linear hf L hl]; exact L.contDiff.comp (hf _ hl U)

section product
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {x y : Config G n → R}

theorem left_first_mul (hx : LeftSmooth k x) (hy : LeftSmooth k y) (A : Directions G n) :
    leftDerivs (fun U => x U * y U) [A] =
      fun U => leftDerivs x [A] U * y U + x U * leftDerivs y [A] U := by
  funext U
  have he := ((hx.has (l:=[]) (Nat.zero_le _) U A).mul (hy.has (l:=[]) (Nat.zero_le _) U A)).deriv
  change deriv (fun t : ℝ => x (increment U (t • A)) * y (increment U (t • A))) 0 =
    leftDerivs x [A] U * y (increment U ((0:ℝ) • A)) +
    x (increment U ((0:ℝ) • A)) * leftDerivs y [A] U at he
  rw [zero_smul, at_zero_increment] at he; exact he

theorem LeftSmooth.mul (hx : LeftSmooth k x) (hy : LeftSmooth k y) :
    LeftSmooth k fun U => x U * y U := by
  induction k generalizing x y with
  | zero =>
    intro l hl U
    simp only [Nat.le_zero, List.length_eq_zero_iff] at hl
    subst l; exact (hx [] (Nat.zero_le _) U).mul (hy [] (Nat.zero_le _) U)
  | succ k ih =>
    intro l hl
    induction l using List.reverseRecOn with
    | nil => intro U; exact (hx [] hl U).mul (hy [] hl U)
    | append_singleton l A _ =>
      simp only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right] at hl
      intro U
      simp only [left_append, left_first_mul hx hy A]
      have ha := ih (hx.inner_derivative A) (hy.truncate k.le_succ)
      have hb := ih (hx.truncate k.le_succ) (hy.inner_derivative A)
      exact ha.add hb l hl U
end product

/-- Bound the l-th ordered derivatives tested with D on Z. -/
structure LeftBound (k : ℕ) (D : Directions G n → Prop) (Z : Config G n → Prop)
    (r c : ℝ) (f : Config G n → E) : Prop where
  smooth : LeftSmooth k f
  nonneg : 0 ≤ c
  bound (l : List (Directions G n)) : l.length ≤ k → (∀ i∈l, D i) →
    ∀ U, Z U → ‖leftDerivs f l U‖ ≤ c * r ^ l.length

variable {D : Directions G n → Prop} {Z : Config G n → Prop} {c c' r : ℝ}

theorem LeftBound.truncate (hf : LeftBound k D Z r c f) (h : m ≤ k) :
    LeftBound m D Z r c f :=
  ⟨hf.smooth.truncate h, hf.nonneg, fun l hl => hf.bound l (hl.trans h)⟩

theorem LeftBound.inner_derivative (hf : LeftBound (k+1) D Z r c f) (hr : 0 ≤ r)
    {A : Directions G n} (hA : D A) : LeftBound k D Z r (c*r) (leftDerivs f [A]) := by
  refine ⟨hf.smooth.inner_derivative A, mul_nonneg hf.nonneg hr, ?_⟩
  intro l hl hD U hU
  rw [← left_append]
  apply (hf.bound (l++[A]) (by simpa)
    (fun i hi => by
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hh|rfl
      · exact hD _ hh
      · exact hA) U hU).trans_eq
  simp only [List.length_append, List.length_singleton, pow_succ]
  ring

theorem LeftBound.add (hf : LeftBound k D Z r c f) (hg : LeftBound k D Z r c' g) :
    LeftBound k D Z r (c+c') fun U => f U + g U := by
  refine ⟨hf.smooth.add hg.smooth, add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro l hl hD U hU
  simp only [left_add hf.smooth hg.smooth hl, add_mul]
  exact (norm_add_le ..).trans <| add_le_add (hf.bound _ hl hD U hU) (hg.bound _ hl hD U hU)

theorem LeftBound.postcomp (hf : LeftBound k D Z r c f) (L : E →L[ℝ] F) :
    LeftBound k D Z r (‖L‖*c) fun U => L (f U) := by
  refine ⟨hf.smooth.postcomp L, mul_nonneg (norm_nonneg _) hf.nonneg, ?_⟩
  intro l hl hD U hU
  simp only [left_linear hf.smooth L hl, mul_assoc]
  exact (L.le_opNorm _).trans <| mul_le_mul_of_nonneg_left (hf.bound _ hl hD U hU)
    (norm_nonneg _)

theorem left_const (x : E) (l : List (Directions G n)) (U : Config G n) :
    leftDerivs (fun (_ : Config G n) => x) l U = if l = [] then x else 0 := by
  classical
  induction l generalizing U with
  | nil => simp [leftDerivs]
  | cons A l ih => simp [leftDerivs, ih, deriv_const]

theorem LeftBound.const (hr : 0 ≤ r) (x : E) :
    LeftBound k D Z r ‖x‖ fun _ => x := by
  refine ⟨fun l _ U => ?_, norm_nonneg _, ?_⟩
  · simp only [left_const]; exact contDiff_const
  · intro l _ _ U _; cases l with
    | nil => simp [left_const]
    | cons A l =>
      simp only [left_const, reduceCtorEq, ↓reduceIte, norm_zero]
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

/-- A coarse Leibniz budget, no factorials. -/
theorem LeftBound.mul {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {x y : Config G n → R}
    (hx : LeftBound k D Z r c x) (hy : LeftBound k D Z r c' y) (hr : 0 ≤ r) :
    LeftBound k D Z r (2^k*c*c') fun U => x U * y U := by
  have start {m : ℕ} {x y : Config G n → R} {c c' : ℝ}
      (h1 : LeftBound m D Z r c x) (h2 : LeftBound m D Z r c' y) (U : Config G n) (hU : Z U) :
      ‖x U * y U‖ ≤ 2^m*c*c' := by
    have he : ‖x U‖ ≤ c := by simpa [leftDerivs] using h1.bound [] (by simp) (by simp) U hU
    have hh : ‖y U‖ ≤ c' := by simpa [leftDerivs] using h2.bound [] (by simp) (by simp) U hU
    have hpow : (1:ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
    apply (norm_mul_le ..).trans <| (mul_le_mul he hh (norm_nonneg _) h1.nonneg).trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg h1.nonneg h2.nonneg) hpow
  induction k generalizing x y c c' with
  | zero =>
    refine ⟨hx.smooth.mul hy.smooth, mul_nonneg (mul_nonneg (by positivity) hx.nonneg) hy.nonneg, ?_⟩
    intro l hl _ U hU
    simp only [Nat.le_zero, List.length_eq_zero_iff] at hl
    subst l; simpa only [leftDerivs, List.length_nil, pow_zero, mul_one] using
      (show ‖x U * y U‖ ≤ 2^0*c*c' from start hx hy U hU)
  | succ k ih =>
    refine ⟨hx.smooth.mul hy.smooth, mul_nonneg (mul_nonneg (by positivity) hx.nonneg) hy.nonneg, ?_⟩
    intro l hl hD
    induction l using List.reverseRecOn with
    | nil =>
      intro U hU; simpa only [leftDerivs, List.length_nil, pow_zero, mul_one] using
        (show ‖x U * y U‖ ≤ 2^(k+1)*c*c' from start hx hy U hU)
    | append_singleton l A _ =>
      simp only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right] at hl
      intro U hU
      have ha := ih (hx.inner_derivative hr (hD A (by simp))) (hy.truncate k.le_succ)
      have hb := ih (hx.truncate k.le_succ) (hy.inner_derivative hr (hD A (by simp)))
      simp only [left_append, left_first_mul hx.smooth hy.smooth A]
      exact le_trans ((ha.add hb).bound l hl (fun i hi => hD _ (List.mem_append_left _ hi)) U hU)
        (le_of_eq (by simp only [List.length_append, List.length_singleton, pow_succ]; ring))

end YM.Work.G07
