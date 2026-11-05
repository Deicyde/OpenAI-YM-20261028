import YM.Bid.Craft
import YM.Laurent.Art
import YM.Work.F07.MatrixRoot
import YM.Work.F07.Read



/-!
# Positive spectral margin implies root rows

Single scalar normalization, single narrower collar for the whole band.
We only have to read the rooted symbols on the real axis; the collar
is to pay for their Laurent coefficients. DFT verifies the identities
for all finite periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F07
open Filter Topology Lattice Laurent Matrix Bloch Holder Craft Bid
open scoped BigOperators ContDiff Matrix.Norms.L2Operator

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def matrixChart : (ι → ι → ℂ) ≃L[ℂ] M ι := (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv

lemma rowDeriv {Q : Row ι ι} {σ η A : ℝ} (hf : Q.strip η A) (hσ : 0 < σ) (hη : σ < η)
    {p : Momentum} (hp : p ∈ strip σ) : DifferentiableAt ℂ (Row.read Q) p := by
  let f : Momentum → ι → ι → ℂ := fun p i j => Q.read p i j
  have he : DifferentiableAt ℂ f p := differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
    (readDeriv (Q.constant_strip hf i j) hσ hη hp).1
  exact matrixChart.differentiableAt.comp (f := f) p he

lemma rootCollar (ι : Type) [Fintype ι] [DecidableEq ι] (v η A : ℝ) (hη : 0 < η) (hv : 0 < v)
    (ha : v ≤ A) : ∃ τ r : ℝ, 0 < τ ∧ τ < η ∧ r < 1 ∧ ∀ Q : Row ι ι,
    Q.strip η A → Funds Q v A → ∀ p ∈ strip τ, ‖binInput A (Q.read p)‖ ≤ r := by
  have hA := hv.trans_le ha
  let σ := η / 2
  have hσ : 0 < σ := by unfold σ; linarith
  have hs : σ < η := by unfold σ; linarith
  let L : (ι → ι → ℂ) →L[ℂ] M ι := matrixChart.toContinuousLinearMap
  let C := ‖L‖ + 1
  have hC : 0 < C := by unfold C; positivity
  let D := (η-σ)⁻¹ * A
  have hD : 0 < D := mul_pos (inv_pos.mpr (sub_pos.mpr hs)) hA
  let τ := min σ ((v/2)/(C*D))
  let r := 1 - A⁻¹*(v/2)
  have ht : τ ≤ σ := min_le_left ..
  have hτ : 0 < τ := lt_min hσ (by positivity)
  refine ⟨τ, r, hτ, lt_of_le_of_lt ht hs, ?_, ?_⟩
  · dsimp only [r]; have := mul_pos (inv_pos.mpr hA) (half_pos hv); linarith
  intro Q h H p hp
  let q : Momentum := fun i => (p i).re
  have hq : star q = q := by funext i; simp [q]
  have hb : ‖p - q‖ ≤ τ := by
    apply (pi_norm_le_iff_of_nonneg hτ.le).2
    intro i
    have he : p i - q i = ((p i).im:ℂ)*Complex.I := by apply Complex.ext <;> simp [q]
    simpa only [Pi.sub_apply, he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs] using (hp i).le
  have he := binInput_bound A (H q hq).1 (show Band (Q.read q) v A from (H q hq).2) hv ha
  let f := fun i j => Q.read p i j - Q.read q i j
  have hf : ‖f‖ ≤ D * τ := by
    have hx := (mul_pos hD hτ).le
    refine (pi_norm_le_iff_of_nonneg hx).2 fun i => (pi_norm_le_iff_of_nonneg hx).2 fun j => ?_
    have hps : p ∈ strip σ := fun i => lt_of_lt_of_le (hp i) ht
    exact (readDiff (Q.constant_strip h i j) hσ hs hps (realStrip σ hσ hq)).trans
      (mul_le_mul_of_nonneg_left hb hD.le)
  have hf' : ‖Q.read p - Q.read q‖ ≤ v/2 := calc
    _ = ‖L f‖ := rfl
    _ ≤ ‖L‖ * ‖f‖ := L.le_opNorm f
    _ ≤ C * (D * τ) := mul_le_mul (by unfold C; linarith) hf (norm_nonneg _) hC.le
    _ ≤ v/2 := by
      rw [← mul_assoc, mul_comm _ τ]
      exact (le_div_iff₀ (mul_pos hC hD)).mp (min_le_right ..)
  rw [show binInput A (Q.read p)=binInput A (Q.read q) + ((A⁻¹ : ℝ):ℂ) • (Q.read p-Q.read q) by
    unfold binInput; rw [smul_sub]; abel]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA)]
  unfold r
  linarith only [he, mul_le_mul_of_nonneg_left hf' (inv_pos.mpr hA).le]

lemma symbolVane {Q : Row ι ι} [Nonempty ι] {η τ A : ℝ} (h : Q.strip η A) (hp : 0 < τ) (ht : τ < η)
    (he : ∀ p ∈ strip τ, ‖binInput A (Q.read p)‖ < 1) (i j : ι) :
    Vane (fun p => binRoot A (Q.read p) i j) τ := by
  refine ⟨hp, fun p hq => ?_, fun p _ x => ?_⟩
  · have hh := (binRoot_deriv A (he p hq)).comp p (rowDeriv h hp ht hq)
    have hf : DifferentiableAt ℂ (fun p => matrixChart.symm (binRoot A (Q.read p))) p :=
      (matrixChart (ι := ι)).symm.differentiableAt.comp p hh
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hf i) j
  rw [Q.periods]

omit [Fintype ι] [DecidableEq ι] in
private lemma fiber_herm {n : Side} (F : Site n → M ι) (h : ∀ p, (F p).IsHermitian) :
    (fiber F).IsHermitian := by
  ext ⟨p,i⟩ ⟨q,j⟩
  by_cases H : p=q
  · subst q; simpa [fiber] using congr_fun (congr_fun (h p).eq i) j
  simp [fiber, H, Ne.symm H]

omit [DecidableEq ι] in
private lemma fiber_powtwo {n : Side} (F : Site n → M ι) :
    fiber (fun i => F i * F i) = fiber F * fiber F := by
  ext ⟨p,i⟩ ⟨q,j⟩
  by_cases h : p=q
  · subst q; simp [fiber, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  simp [h, fiber, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite]

/-- Push the real-axis identities through all periods in the track's DFT conventions. -/
lemma squarePeriods (Q P : Row ι ι) (hQ : Q.safe) (hP : P.safe)
    (h : ∀ p : Momentum, star p = p →
      IsHermitian (P.read p) ∧ P.read p * P.read p = Q.read p) : SqActs Q P := by
  intro n
  let X := approached (P.acts n)
  let R := rotations n ι
  let F := fun p : Site n => P.read (mon p)
  have he : X*R = R*fiber F := Bloch.circulant n P hP
  have hF : IsHermitian (fiber F) := fiber_herm _ fun p => (h _ (real_frequency p)).1
  let c := (n.val:ℂ)^4
  have hg : R * Rᴴ = c • 1 := rotations_gram n ι
  have ht : c • X = R*fiber F*Rᴴ := by rw [← he, Matrix.mul_assoc, hg, Matrix.mul_smul, Matrix.mul_one]
  have hx : Xᴴ = X := by
    have hb := congr_arg Matrix.conjTranspose ht
    rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hF.eq, ← Matrix.mul_assoc, ← ht, show star c = c by simp [c]] at hb
    exact smul_right_injective _ (pow_ne_zero _ (side_ne n)) hb
  have hy : (P.acts n).transpose = P.acts n := prom_inj (by rw [prom_adj]; exact hx)
  refine ⟨?_, hy⟩
  rw [hy]
  apply prom_inj; rw [prom_mul]; apply cancel_rotation n
  have hh : (fun p : Site n => Q.read (mon p)) = fun p => F p * F p :=
    funext fun p => (h _ (real_frequency p)).2.symm
  rw [Bloch.circulant n Q hQ, hh, fiber_powtwo]
  change R*(fiber F*fiber F) = X*X*R
  rw [Matrix.mul_assoc X, he, ← Matrix.mul_assoc X, he, Matrix.mul_assoc]

lemma makeRoot (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (A v η : ℝ)
    (hv : 0 < v) (hη : 0 < η) (ha : v ≤ A) : ∃ B e : ℝ, 0 < e ∧ ∀ Q : Row ι ι,
    Q.strip η A → Funds Q v A → ∃ P : Row ι ι, Funds P (Real.sqrt v) B ∧ P.strip e B ∧ SqActs Q P := by
  obtain ⟨τ,r,hτ,ht,hr,he⟩ := rootCollar ι v η A hη hv ha
  obtain ⟨k,hk⟩ := binSum_bound (ι:=ι) r hr
  let K := Real.sqrt A * k
  let e := τ/3
  have he' : 0 < e := by unfold e; linarith
  have he'' : e + e < τ := by unfold e; linarith
  let M0 := K*(2*((1+e)/e))^(Fintype.card Axis)
  let B := max M0 (Real.sqrt A)
  refine ⟨B, e, he', fun Q hQ hg => ?_⟩
  let f := fun (i j : ι) (p : Momentum) => binRoot A (Q.read p) i j
  have hV (i j) : Vane (f i j) τ := symbolVane hQ hτ ht (fun p h => (he Q hQ hg p h).trans_lt hr) i j
  have hK (i j) : ∀ p ∈ strip τ, ‖f i j p‖ ≤ K := by
    intro p hp
    apply (controls _ i j).trans (show ‖binRoot A (Q.read p)‖ ≤ K from ?_)
    rw [binRoot, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hk _ (he Q hQ hg p hp)) (Real.sqrt_nonneg _)
  let P : Row ι ι := fun i j x => (market (f i j) 0 x).re
  have hw (i j) : Width e M0 (market (f i j) 0) :=
    (hV i j).issues (hK i j) e e he'.le he' he''
  have hP : P.strip e B := fun i j => (widthRealPart (hw i j)).mono le_rfl (le_max_left ..)
  have hall (p : Momentum) (hp : star p = p) : P.read p = binRoot A (Q.read p) := by
    have hq : star (-p) = -p := by rw [star_neg, hp]
    have hR : Q.read (-p) = (Q.read p).map star := by
      simpa only [hp] using Q.conjugate p
    ext i j
    have h : star (f i j (-p)) = f i j p := by simp only [f,hR,binRoot_conj,map_apply,star_star]
    change Laurent.read _ p = f i j p
    rw [readRealPart (hw i j) he' hp,
      (hV i j).paints (hK i j) p (realStrip τ hτ hp),
      (hV i j).paints (hK i j) (-p) (realStrip τ hτ hq), h]
    ring
  have hb (p : Momentum) (hp : star p = p) :
      (P.read p).IsHermitian ∧ Band (P.read p) (Real.sqrt v) B ∧ P.read p * P.read p = Q.read p := by
    rw [hall p hp]
    exact binRoot_on_band (hg p hp).1 (hg p hp).2 hv (hv.trans_le ha) (le_max_right ..)
  exact ⟨P, fun p h => ⟨(hb p h).1,(hb p h).2.1⟩, hP,
    squarePeriods Q P (Row.rights η _ hQ hη.le) (Row.rights e _ hP he'.le) fun p h =>
      ⟨(hb p h).1,(hb p h).2.2⟩⟩
end

theorem answer : YM.Bid.F07 := by
  intro ι inst A v η hv hη
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    refine ⟨1,1,1,zero_lt_one,zero_lt_one,fun Q _ _ => ?_⟩
    refine ⟨Q, fun p _ => ⟨?_,?_⟩, fun i => isEmptyElim i, fun n => ⟨?_,?_⟩⟩
    · exact Subsingleton.elim _ _
    · intro x; simp [dotProduct]
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  | inr h =>
    -- harmless enlargement, even if given A is negative
    obtain ⟨B,e,he,H⟩ := makeRoot ι (max v A) v η hv hη (le_max_left ..)
    refine ⟨Real.sqrt v,B,e,Real.sqrt_pos.mpr hv,he,fun Q hQ hF => H Q ?_ ?_⟩
    · exact fun i j => (hQ i j).mono le_rfl (le_max_right ..)
    intro p hp
    refine ⟨(hF p hp).1, fun x => ⟨((hF p hp).2 x).1, ((hF p hp).2 x).2.trans ?_⟩⟩
    apply mul_le_mul_of_nonneg_right (le_max_right ..)
    rw [dotProduct, Complex.re_sum]; apply Finset.sum_nonneg
    intro i _
    simpa [Complex.mul_re, Complex.normSq_apply] using Complex.normSq_nonneg (x i)
end YM.Work.F07
