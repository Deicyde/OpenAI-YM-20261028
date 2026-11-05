import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.Push.STATIONARY_UNIFORM.Count


/-!
# From symbolic Hessian gap & summability to actual counting/sup resolvents

An alternative to going through Fourier. Even works with irregular
(nontranslation invariant) trees. Use full-site distances on genuine four-dimensional
finite torus with bounded site/T multiplicities. Dimension, gauge group,
spectrum not baked into constants except as they pay these prerequisites.
No projecting away the harmonic input. Edge case no free indices included.

Widened distance proof: only test coercivity, not Hermitianity, after
exponential weighting. Use φ changing slowly in a single leg's native
distance, for norm of the tilted inverse pay a little gap. Rate in this
bound is not claimed adequate for the LOOP/tilted summability station in the
scheduling ledger. This is for local field-implicit estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical

variable {n : Side} {ι : Type} [Fintype ι] {l : ι → Site n} {K : ℕ}
variable {S T : Matrix ι ι ℝ} {a r C M : ℝ}

/-- unweighted coercivity in TRUE counting. don't misread as a uniform
lower bound in Euclidean pairs of matrix of dimension unrelated to period. -/
def Charge (S : Matrix ι ι ℝ) (m : ℝ) := ∀ v : Positions ι, m * (∑ i, v i^2) ≤ v ⬝ᵥ (S *ᵥ v)

lemma Charge.positive (h : Charge S M) (he : S.IsHermitian) (hm : 0 < M) : S.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨he, fun {x} hx => ?_⟩
  have hp : ∃ i, 0 < x i ^2 := by
    by_contra! h0; apply hx; funext i; apply (sq_eq_zero_iff.mp ((h0 i).antisymm (sq_nonneg _)))
  rw [star_trivial]
  obtain ⟨i,hi⟩ := hp
  exact lt_of_lt_of_le (mul_pos hm (hi.trans_le (Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i)))) (h _)

def Sealed (l : ι → Site n) (a : ℝ) (S : Matrix ι ι ℝ) (C : ℝ) : Prop := ∀ i j, |S i j| ≤ C*Decay a (l i) (l j)

section Rows
lemma Sealed.row (h : Sealed l a S C) (ha : 0<a) (hC : 0≤C) (hk : Multiplicity l K) (i) :
    (∑ j, |S i j|) ≤ C * ((K:ℝ)*countCost a) := by
  apply (Finset.sum_le_sum (f:=fun j => |S i j|) (fun j _ => h i j)).trans
  rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hk.count l ha _) hC
omit [Fintype ι] in
lemma Sealed.tran (h : Sealed l a S C) : Sealed l a S.transpose C := fun i j => by rw [decay_comm]; exact h j i

lemma Sealed.weighted (h : Sealed l a S C) (hC : 0≤C) (hk : Multiplicity l K) {r : ℝ} (ha : r<a) (i) :
    (∑ j, |S i j| * Real.exp (r * separation (l i) (l j))) ≤ C * ((K:ℝ)*countCost (a-r)) := by
  let R := Matrix.of fun i j => S i j * Real.exp (r * separation (l i) (l j))
  have hr i j : |R i j| = |S i j| * Real.exp (r * separation (l i) (l j)) := by rw [show R i j=S i j * Real.exp (r * separation (l i) (l j)) from rfl,abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hf : Sealed l (a-r) R C := fun i j => by
    rw [hr]; apply (mul_le_mul_of_nonneg_right (h i j) (Real.exp_pos _).le).trans_eq
    unfold Decay; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [← hr]; exact hf.row (sub_pos.mpr ha) hC hk i

lemma rows_test (hn : ∀ i, (∑ j, |S i j|) ≤ C) (hc : 0 ≤ C) (v : Positions ι) : ‖(S *ᵥ v)‖ ≤ C*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ C*‖v‖)).mpr; intro i
  rw [Real.norm_eq_abs]; apply le_trans (Finset.abs_sum_le_sum_abs (fun j => S i j*v j) _)
  calc
    _ ≤ ∑ j, |S i j| * ‖v‖ := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hn _) (norm_nonneg _)

lemma quadratic_test (hn : ∀ i, (∑ j, |S i j|) ≤ C) (hj : ∀ j, (∑ i, |S i j|) ≤ C) (v : Positions ι) :
    |v ⬝ᵥ (S *ᵥ v)| ≤ C*(∑ i,v i^2) := by
  let F i j := |S i j| * v i ^ 2 + |S i j| * v j ^ 2
  have he i j : |v i * (S i j*v j)| ≤ F i j / 2 := by
    rw [abs_mul,abs_mul]
    unfold F; rw [← sq_abs (v i),← sq_abs (v j)]
    nlinarith only [mul_nonneg (abs_nonneg (S i j)) (sq_nonneg (|v i| - |v j|))]
  have h₁ : (∑ i, ∑ j, |S i j| * v i ^ 2) ≤ C*(∑ i,v i^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hn i) (sq_nonneg _)
  have h₂ : (∑ i, ∑ j, |S i j| * v j ^ 2) ≤ C*(∑ i,v i^2) := by
    rw [Finset.sum_comm, Finset.mul_sum]; apply Finset.sum_le_sum; intro j _; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hj j) (sq_nonneg _)
  conv_lhs => simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  calc
    _ ≤ ∑ i, ∑ j, F i j / 2 := Finset.sum_le_sum fun i _ => le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => he i j))
    _ ≤ _ := by simp_rw [← Finset.sum_div,F,Finset.sum_add_distrib]; linarith

/-- Composes with absolute kernel bounds, no selfadjointness assumption here. -/
lemma Charge.transfer (hS : Charge S M) (ha : 0<a) (hC : 0≤C) (h : Sealed l a (S-T) C) (hk : Multiplicity l K) :
    Charge T (M-C*((K:ℝ)*countCost a)) := by
  intro v
  have he := quadratic_test (S:=S-T) (h.row ha hC hk) (fun j => h.tran.row ha hC hk j) v
  have hh := (abs_le.mp he).2
  rw [Matrix.sub_mulVec, dotProduct_sub] at hh
  linarith [hS v]
end Rows

namespace Charge

variable [DecidableEq ι]
lemma energy_inverse (h : Charge S M) (hM : 0 < M) (hS : IsUnit S.det) (v : Positions ι) :
    (∑ i, ((S⁻¹ *ᵥ v) i)^2) ≤ M⁻¹^2 * ∑ i, v i^2 := by
  let w := S⁻¹ *ᵥ v
  let r : ℝ := ∑ i,w i^2
  let s : ℝ := ∑ i,v i^2
  have hr : 0 ≤ r := by unfold r; positivity
  have hs : 0 ≤ s := by unfold s; positivity
  have ht : S *ᵥ w=v := by rw [show w=_ from rfl, Matrix.mulVec_mulVec,S.mul_nonsing_inv hS, one_mulVec]
  have he := h w; rw [ht] at he; change M*r ≤ _ at he
  have hy : (w ⬝ᵥ v)^2 ≤ r*s := Finset.sum_mul_sq_le_sq_mul_sq _ w v
  change r ≤ _*s
  rcases eq_or_lt_of_le hr with hr|hr
  · rw [← hr]; positivity
  have hx := (pow_le_pow_left₀ (mul_nonneg hM.le hr.le) he 2).trans hy
  rw [inv_pow,mul_comm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]; nlinarith
end Charge

section tilted

def tilt (a : ℝ) (l : ι → Site n) (x : Site n) (S : Matrix ι ι ℝ) := Matrix.of fun i j =>
    Real.exp (a*((separation x (l i):ℝ)-(separation x (l j):ℝ))) * S i j

private lemma modulus (x t : ℝ) (h : |x|≤t) : |1-Real.exp x| ≤ t*Real.exp t := by
  have ht := (abs_le.mp h).1; have hh := (abs_le.mp h).2
  have hm := Real.exp_pos t
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) hm.le
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at he
  apply abs_le.mpr; constructor
  · linarith [Real.exp_monotone hh]
  have hu : 1 ≤ Real.exp t := Real.one_le_exp ((abs_nonneg x).trans h)
  have hy := le_trans (Real.add_one_le_exp (-t)) (Real.exp_monotone ht)
  nlinarith [(abs_nonneg x).trans h]

omit [Fintype ι] in
lemma Sealed.tilt (h : Sealed l a S C) (ha : 0<a) (hr : 0<r) (hC : 0 ≤ C) (ht : r ≤ a/4) (x : Site n) :
    Sealed l (a/2) (S - Uniform.tilt r l x S) (C*r*(4/a)) := by
  intro i j
  let d : ℝ := separation (l i) (l j); let v : ℝ := separation x (l i); let w : ℝ := separation x (l j)
  have hd : 0 ≤ d := by unfold d; positivity
  have hv : v ≤ w+d := by
    unfold v w d; rw [separation_comm (l i)]; exact_mod_cast separation_triangle x (l j) (l i)
  have hw : w ≤ v+d := by unfold w v d; exact_mod_cast separation_triangle x (l i) (l j)
  have he := modulus (r*(v-w)) (r*d) (by rw [abs_mul,abs_of_pos hr]; gcongr; rw [abs_le]; constructor <;> linarith)
  have hu : d ≤ 4/a * Real.exp ((a/4)*d) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith [Real.add_one_le_exp ((a/4)*d)]
  have hq := Real.exp_monotone (mul_le_mul_of_nonneg_right ht hd)
  have hz : (S - Uniform.tilt r l x S) i j = (1-Real.exp (r*(v-w))) * S i j := by unfold Uniform.tilt; simp only [Matrix.sub_apply, Matrix.of_apply,v,w]; ring
  rw [hz,abs_mul]; apply (mul_le_mul he (h i j) (abs_nonneg _) (by positivity)).trans
  calc
    _ ≤ (r*(4/a * Real.exp ((a/4)*d)) * Real.exp ((a/4)*d)) * (C*Real.exp (-a*d)) := mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hu hr.le) hq (by positivity) (by positivity)) (mul_nonneg hC (Real.exp_pos _).le)
    _ = C*r*(4/a)*((Real.exp ((a/4)*d)*Real.exp ((a/4)*d))*Real.exp (-a*d)) := by ring
    _ = _ := by unfold Decay; rw [← Real.exp_add, ← Real.exp_add]; congr 2; unfold d; ring

/-- Useful exponential rate in inverse coordinates. -/
def tiltWidth (K : ℕ) (M a C : ℝ) := min (a/4) (M/(2*(1+(C*(4/a))*((K:ℝ)*countCost (a/2)))))

lemma tiltWidth_pos (K : ℕ) (hM : 0<M) (ha : 0<a) (hC : 0 ≤ C) : 0<tiltWidth K M a C :=
  lt_min (by positivity) (div_pos hM (by have he := count_pos (half_pos ha); positivity))

lemma tiltedCharge (h : Sealed l a S C) (hM : 0<M) (ha : 0<a) (hp : Charge S M) (hC : 0≤C)
    (hk : Multiplicity l K) (x : Site n) : Charge (tilt (tiltWidth K M a C) l x S) (M/2) := by
  let r := tiltWidth K M a C
  have hr : 0 < r := tiltWidth_pos K hM ha hC
  have he := hp.transfer (half_pos ha) (by positivity) (h.tilt ha hr hC (min_le_left ..) x) hk
  have hA : C * r *(4/a)* ((K:ℝ)*countCost (a/2)) ≤ M/2 := by
    let v := C*(4/a)*((K:ℝ)*countCost (a/2))
    have hh : 0≤v := by have hy := count_pos (half_pos ha); unfold v; positivity
    have hi := (le_div_iff₀ (show 0<2*(1+v) by positivity)).mp (show r ≤ M/(2*(1+v)) from min_le_right ..)
    rw [show C*r*(4/a)*((K:ℝ)*countCost (a/2))=r*v by unfold v; ring]; linarith
  intro i; apply le_trans _ (he i)
  exact mul_le_mul_of_nonneg_right (by linarith only [hA]) (by positivity)

variable [DecidableEq ι]
lemma inverse_sealed (h : Sealed l a S C) (hM : 0<M) (ha : 0<a) (hp : Charge S M) (hC : 0≤C)
    (hk : Multiplicity l K) (hi : IsUnit S.det) : Sealed l (tiltWidth K M a C) S⁻¹ ((M/2)⁻¹) := by
  intro i j
  let r := tiltWidth K M a C; let m := M/2
  have hm : 0<m := half_pos hM
  let x := l j; let u (b : ι) := (S⁻¹) b j
  have hx : S *ᵥ u = Pi.single j 1 := by
    change S *ᵥ S⁻¹.col j = _
    rw [← mulVec_single_one, mulVec_mulVec, mul_nonsing_inv S hi, one_mulVec]
  let w (b : ι) := Real.exp (r*separation x (l b))
  let T := tilt r l x S
  let v (b : ι) := w b*u b
  have ht b d : T b d * v d=w b*(S b d * u d) := by
    dsimp only [T, tilt,Matrix.of_apply,v,w]
    rw [mul_sub, Real.exp_sub]; field_simp
  have hU : T *ᵥ v=Pi.single j 1 := by
    funext b
    simp only [mulVec,dotProduct, ht, ← Finset.mul_sum]; change w b * (S *ᵥ u) b = _
    rw [hx]; by_cases h : b=j
    · subst b; simp [w,x]
    simp [h]
  have hb := tiltedCharge h hM ha hp hC hk x v
  change m * _ ≤ dotProduct v (T *ᵥ v) at hb
  rw [hU, dotProduct] at hb
  have h1 : (∑ x, v x * (Pi.single (M:=fun _ => ℝ) j (1:ℝ) x : ℝ))=v j := by rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]; simp; intro b _ hb; simp [hb]
  rw [h1] at hb
  have hd b : m*(v b)^2 ≤ v j := le_trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun b _ => sq_nonneg (v b)) (Finset.mem_univ _)) hm.le) hb
  have hh : v j ≤ m⁻¹ := by
    apply le_of_not_gt; intro hs
    have hs' : 1 < v j * m := (div_lt_iff₀ hm).1 (by rwa [one_div])
    nlinarith [hd j, inv_pos.mpr hm]
  have hv : |v i| ≤ m⁻¹ := by
    apply (sq_le_sq₀ (abs_nonneg _) (inv_pos.mpr hm).le).mp
    rw [sq_abs]; apply le_of_mul_le_mul_left _ hm
    rw [pow_two (a:=m⁻¹),mul_inv_cancel_left₀ hm.ne']; exact (hd i).trans hh
  dsimp only [v] at hv; rw [abs_mul, abs_of_pos (show 0 < w i from Real.exp_pos _)] at hv
  change |u i| ≤ m⁻¹ * Decay r (l i) x
  rwa [decay_comm,Decay,neg_mul,Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (show 0 < w i from Real.exp_pos _),mul_comm]
end tilted
end YM.Push.Uniform
