import YM.Complex.Holder

/-!
# Normalized strip path for even column estimates

From B†B, no division on kernel. Does NOT assert B positive (this is
an insertion). `‖A‖` is Matrix.Norms.L2Operator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Holder
open MeasureTheory Filter Set Complex Matrix WithLp
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

abbrev U (ι : Type*) [Fintype ι] [DecidableEq ι] := unitaryGroup ι ℂ

@[simp] theorem united (u : U ι) : u.valᴴ * u.val=1 := u.property.1
@[simp] theorem united' (u : U ι) : u.val * u.valᴴ=1 := u.property.2

lemma unitary_safe (u : U ι) : ‖u.val‖ ≤ 1 :=
  Eq.trans (congr_arg (‖·‖) (mul_one u.val).symm) (CStarRing.norm_coe_unitary_mul u (1:M ι)) |>.trans_le contract_one
lemma unitary_safe' (u : U ι) : ‖u.valᴴ‖ ≤ 1 :=
  (Matrix.l2_opNorm_conjTranspose _).trans_le (unitary_safe u)

lemma controls (A : M ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  let b := EuclideanSpace.basisFun ι ℂ
  have he : A i j = inner ℂ (b i) (T (b j)) := by
    rw [show inner ℂ (b i) (T (b j)) = _ from EuclideanSpace.basisFun_inner ι ℂ (T (b j)) i]
    dsimp only [T,b]; rw [Matrix.ofLp_toEuclideanCLM]; simp
  rw [he]; have hv := norm_inner_le_norm (𝕜 := ℂ) (b i) (T (b j)); rw [b.norm_eq_one,one_mul] at hv
  exact hv.trans ((T.le_opNorm (b j)).trans_eq (by rw [OrthonormalBasis.norm_eq_one, mul_one];rfl))

abbrev D (s : ι → ℝ) : M ι := diagonal (Complex.ofReal ∘ s)

/-- Entire even at λ=0 by kernel convention. At time-zero ignores kernel. -/
def specPow (t : ℝ) (z : ℂ) := if t=0 then 0 else exp (↑(Real.log t)*z)

lemma spec_smooth (t : ℝ) : Differentiable ℂ (specPow t) := by
  by_cases h:t=0
  · change Differentiable ℂ fun x => specPow t x; simp only [specPow,h, ↓reduceIte]; exact differentiable_const 0
  change Differentiable ℂ fun x => specPow t x; simp only [specPow,h, ↓reduceIte]; fun_prop

lemma spec_norm {t : ℝ} (h : 0<t) (z : ℂ) : ‖specPow t z‖ = t^z.re := by simp [specPow,Complex.norm_exp,h.ne', Real.rpow_def_of_pos h]
lemma spec_norm0 {t : ℝ} (h : 0≤t) (z : ℂ) : ‖specPow t z‖ ≤ t^z.re := by
  rcases lt_or_eq_of_le h with h|h
  · rw [spec_norm h]
  have hp : 0≤t^z.re := Real.rpow_nonneg h.le _ -- h : 0=t
  rw [specPow,if_pos h.symm, norm_zero]; exact hp
lemma spec_nat {t : ℝ} (h : 0≤t) {p : ℕ} (hp : 0<p) : specPow t (p:ℂ)=(t^p : ℝ) := by
  rcases lt_or_eq_of_le h with h|h
  · unfold specPow; rw [if_neg h.ne']
    rw [← Real.rpow_natCast t p, Real.rpow_def_of_pos h,Complex.ofReal_exp,Complex.ofReal_mul]; simp
  simp [← h,specPow,hp.ne']

lemma diagonal_diff (s : ι → ℝ) : Differentiable ℂ (fun z => diagonal (fun i => specPow (s i) z)) :=
    ((Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable).comp ((differentiable_pi).2 fun i => spec_smooth (s i))

def weighted (A B : M ι) (v : ι → ℝ) (h : ∀ i, 0≤v i) (hs : ∑ i, v i ≤ 1)
    (a : ‖A‖≤1) (b : ‖B‖≤1) : Flex ι where
  walk z := A * diagonal (fun i => specPow (v i) z) * B
  ball z hz := by
    refine contract_mul (contract_mul a ?_) b
    rw [Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    exact fun i => (spec_norm0 (h i) z).trans (Real.rpow_le_one (h i)
      ((Finset.single_le_sum (fun i _ => h i) (Finset.mem_univ i)).trans hs) hz.1)
  border z hz C hC := by
    let Y := diagonal fun i => specPow (v i) z
    change ‖(A*Y*B*C).trace‖ ≤ 1
    rw [mul_assoc A Y,mul_assoc A (Y*B),Matrix.trace_mul_comm,mul_assoc Y,mul_assoc Y]
    let E := B*C*A
    have he : ‖E‖ ≤ 1 := contract_mul (contract_mul b hC) a
    simp only [trace, diag_apply, diagonal_mul, Y]
    apply (norm_sum_le _ _).trans; apply le_trans _ hs
    refine Finset.sum_le_sum fun i _ => ?_
    change ‖_ * E i i‖ ≤ _
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ((controls E i i).trans he)).trans
      (by simpa only [hz,Real.rpow_one] using spec_norm0 (h i) z)
  smooth := ((differentiable_const A).mul (diagonal_diff v)).mul (differentiable_const B)

theorem spectral_diag {A : M ι} (h : A.IsHermitian) : A=h.eigenvectorUnitary.val * D h.eigenvalues * h.eigenvectorUnitary.valᴴ := h.spectral_theorem

theorem spectral_power (Y : U ι) (s : ι → ℝ) (p : ℕ) : (Y.val*D s*Y.valᴴ)^p = Y.val*D (s^p)*Y.valᴴ := by
  induction p with
  | zero => simp only [pow_zero]; rw [show D (1:ι→ℝ)=1 by ext i j; by_cases h : i=j <;> simp [D,Matrix.diagonal,Matrix.one_apply,h],mul_one, united']
  | succ p ih =>
    rw [pow_succ,ih]
    calc
      _ = Y.val * (D (s^p) * (Y.valᴴ*Y.val) * D s) * Y.valᴴ := by simp only [mul_assoc]
      _ = _ := by
        rw [united,mul_one]
        rw [show D (s^p) * D s = D (s^(p+1)) by
          rw [D,D,diagonal_mul_diagonal]; congr 1; ext1; simp [pow_succ]]

theorem spectral_trace {A : M ι} (Y : U ι) (s : ι → ℝ) (h : A=Y.val*D s*Y.valᴴ) (p : ℕ) :
    (A^p).trace=↑(∑ i, (s i)^p) := by
  simp only [h,spectral_power,trace_mul_cycle, united, one_mul]
  simp [D]

private theorem sv (A : M ι) : ∃ (Y : U ι) (s : ι → ℝ), (∀ i, 0 ≤ s i) ∧ Aᴴ*A=Y.val*D (s^2)*Y.valᴴ := by
  let h := Matrix.posSemidef_conjTranspose_mul_self A
  let t := h.1.eigenvalues
  let s (i : ι) := Real.sqrt (t i)
  refine ⟨h.1.eigenvectorUnitary,s, fun i => Real.sqrt_nonneg _,?_⟩
  rw [show s^2=t by funext i; exact Real.sq_sqrt (h.eigenvalues_nonneg _)]; exact spectral_diag _

omit [Fintype ι] in
private lemma diag_star (v : ι → ℝ) : (D v)ᴴ=D v := by
  unfold D; rw [diagonal_conjTranspose]
  ext i j; by_cases h : i=j <;> simp [*,Matrix.diagonal]

private theorem imageForm (A : M ι) (Y : U ι) (s : ι → ℝ) (h : Aᴴ*A=Y.val*D (s^2)*Y.valᴴ) :
    ∃ P : M ι, ‖P‖ ≤ 1 ∧ A=P * D s * Y.valᴴ := by
  let J := D (fun i => (s i)⁻¹)
  let X := A * Y.val
  have hm : Xᴴ * X = D (s^2) := by
    unfold X; rw [Matrix.conjTranspose_mul]
    calc
      _ = Y.valᴴ*(Aᴴ*A)*Y.val := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc,united, mul_one]; rw [← mul_assoc,united,one_mul]
  let K : M ι := J * D s
  have hx (p : ℕ) (hp : 0 < p) : D (s^p) * K = D (s^p) := by
    unfold K J D
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hb : s i = 0 <;> simp [hb,hp.ne']
  have hP : X=X*K := by
    let t := X * (1-K)
    have he : tᴴ*t=0 := by
      unfold t
      rw [Matrix.conjTranspose_mul]
      calc
        _ = (1-K)ᴴ * (Xᴴ*X*(1-K)) := by simp only [mul_assoc]
        _ = _ := by rw [hm,mul_sub,hx _ (by omega),mul_one,sub_self,mul_zero]
    have hh : X*(1-K)=0 := norm_eq_zero.mp (by
      change ‖t‖=0
      rw [← mul_self_eq_zero]; rw [← t.l2_opNorm_conjTranspose_mul_self, he]; exact norm_zero)
    rwa [mul_sub,mul_one,sub_eq_zero] at hh
  refine ⟨X*J,?_,?_⟩
  · have he : (X*J)ᴴ*(X*J)=K := by
      rw [Matrix.conjTranspose_mul, ← mul_assoc _ X J, mul_assoc _ Xᴴ X, hm]
      unfold K J; rw [diag_star]
      rw [mul_assoc]; congr 1
      unfold D; rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; by_cases h : s i=0 <;> simp [h,pow_succ]
    have hk : ‖K‖ ≤ 1 := by
      unfold K J D
      rw [Matrix.diagonal_mul_diagonal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro i
      by_cases H : s i=0 <;> simp [H]
    have hj : ‖X*J‖ * ‖X*J‖ ≤ 1 := (Matrix.l2_opNorm_conjTranspose_mul_self _).symm.trans_le (by rw [he]; exact hk)
    nlinarith [norm_nonneg (X*J)]
  rw [mul_assoc X J (D s),← show X= X*(J * D s) from hP]
  unfold X; rw [mul_assoc, united', mul_one]

omit [DecidableEq ι] in
lemma share {v : ι → ℝ} (_ : ∀ i, 0 ≤ v i) : ∑ i, v i/(∑ j, v j) ≤ 1 := by
  rw [← Finset.sum_div]; by_cases he : (∑ j, v j)=0 <;> simp [he]

lemma pays {v g : ℝ} (_ : 0 ≤ v) (_ : 0 ≤ g) (hG : v≠0 → g≠0) (z : ℂ) :
    specPow v z=specPow g z*specPow (v/g) z := by
  by_cases h : v=0
  · simp [h,specPow]
  have he := hG h
  unfold specPow; rw [if_neg h,if_neg he,if_neg (div_ne_zero h he),← Complex.exp_add, Real.log_div h he]
  push_cast; ring_nf

lemma rolls {v : ℝ} (_ : 0 ≤ v) (z : ℂ) {p : ℕ} (hp : 0 < p) : specPow (v^p) z = specPow v (p*z) := by
  by_cases hh : v=0
  · simp [hh, hp.ne',specPow]
  rw [specPow, if_neg (pow_ne_zero _ hh), specPow,if_neg hh,Real.log_pow]
  push_cast; ring_nf

lemma slogan {x : ℝ} (h : 0 ≤ x) {y : ℝ} (he : y ≠ 0) : specPow x (y:ℂ)= ↑(x^y) := by
  by_cases hx : x=0
  · subst x; simp [specPow,Real.zero_rpow he]
  simp [specPow,hx,Real.rpow_def_of_pos (lt_of_le_of_ne h (Ne.symm hx)), Complex.ofReal_exp]

/-- Cost even Schatten powers at real parameters. Represent A on
an ENTIRE strip path of trace interpolation family. -/
theorem even_cost (A : M ι) (p : ℕ) (hp : 0 < p) :
    let t := (((p+p:ℕ):ℝ))⁻¹
    ∃ P : Flex ι, A= ((‖((Aᴴ*A)^p).trace‖^t:ℝ):ℂ) • P.walk (t:ℂ) := by
  intro t
  obtain ⟨Y,s,he,h⟩ := sv A
  obtain ⟨X,hc,hx⟩ := imageForm A Y s h
  let w (i : ι) := s i ^ (p+p)
  have hw (i) : 0 ≤ w i := pow_nonneg (he i) _
  let R := ∑ i, w i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hw i)
  have hz : ((Aᴴ*A)^p).trace=↑R := by
    rw [spectral_trace Y (s^2) h]
    congr 1; apply Finset.sum_congr rfl
    intro i _; simp [w,← pow_mul,two_mul]
  have ha : (0:ℝ)<t := inv_pos.mpr (Nat.cast_pos.mpr (by omega))
  let f (i) := w i/R
  let D' := diagonal (fun i => specPow (f i) (t:ℂ))
  let V := weighted X Y.valᴴ f (fun i => div_nonneg (hw _) hR) (share hw) hc (unitary_safe' Y)
  refine ⟨V,?_⟩
  rw [hz, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR,hx]
  change _= _ • (X*D'*Y.valᴴ)
  rw [show D s = (↑(R^t):ℂ) • D' by
    unfold D' D
    rw [← Matrix.diagonal_smul];congr 1; funext i
    change ((s i:ℝ):ℂ)= _ * _
    have hg (hh : w i≠0) : R≠0 := ne_of_gt ((lt_of_le_of_ne (hw i) hh.symm).trans_le
      (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)))
    rw [← slogan hR ha.ne',← show _ from pays (hw i) hR hg (t:ℂ)]
    unfold w; rw [rolls (he i) _ (by omega), show ((↑((p+p : ℕ)) : ℂ)*(t:ℂ))=1 by
      unfold t; push_cast; field_simp]
    simpa using spec_nat (t := s i) (p := 1) (he i) (by decide) |>.symm]
  simp only [mul_smul_comm,smul_mul_assoc]
end YM.Holder
