import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Combes-Thomas for the periodized real Gram matrices

Counting version (even principal restrictions of the *completed*
Gram). No Fourier multipliers, no regularization by a positive mass or
exponential-with-volume reference. Works from the same gap and Schur
prices on the given period. Rate uniform even if number of holes grows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Schur
open Function Filter Lattice RG Wilson Finset Pressure Precision Exterior Tree Matrix Gaussian Rows Wisps 
open scoped Topology BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable {c : Side} (p : V → Site c)
variable {σ ε M : ℝ}

private lemma budget_exp {a b s : ℝ} (ha : b ≤ s) (hb : -s ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ a) (hl : a ≤ 1) :
    |Real.exp (a*b)-1| ≤ a*Real.exp s := by
  have hu := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ s) (sub_nonneg.mpr hl) ht (by ring : (1-a)+a=1)
  simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at hu
  rw [abs_le]; constructor
  · have hv : Real.exp (-(a*s)) ≤ Real.exp (a*b) := by
      apply Real.exp_monotone
      nlinarith
    have hm : Real.exp (a*s) + Real.exp (-(a*s)) ≥ 2 := by
      have H := Real.add_one_le_exp (a*s); have H' := Real.add_one_le_exp (-(a*s)); linarith
    linarith
  have hv : Real.exp (a*b) ≤ Real.exp (a*s) := by gcongr
  linarith

/-- Choose weight exponent small. No selfadjointness of the
conjugated matrix is used; prices its real quadratic against the gap. -/
private def mass (v : ℝ) (i j : V) := rate v (separation (p i) (p j))
private def coffee (A : Gaussian.Table V) (v : ℝ) (i : V) := Matrix.of fun j k => mass p v j i * A j k * (mass p v k i)⁻¹

private lemma tilting (A : Gaussian.Table V) (h : Pours A p p σ M) (hs : 0≤σ) (i : V) {a : ℝ} (ha : 0≤a) (ht : a ≤ 1) :
    Pours (coffee p A (a*σ) i - A) p p 0 (a*M) := by
  have hcost (j k : V) : rate 0 (separation (p j) (p k)) * |(coffee p A (a*σ) i - A) j k| ≤
      a * (rate σ (separation (p j) (p k)) * |A j k|) := by
    let w (j k : V) : ℝ := separation (p j) (p k)
    have he (m n r : V) : w m n ≤ w m r + w r n := by unfold w; exact_mod_cast separation_triangle (p m) (p r) (p n)
    have hw : w k j=w j k := by unfold w; rw [separation_comm]
    have hl₁ := he j i k; have hl₂ := he k i j; rw [hw] at hl₂
    have hp : |Real.exp (a*(σ*(w j i-w k i)))-1| ≤ a*Real.exp (σ*w j k) := by
      apply budget_exp _ _ (mul_nonneg hs (by unfold w; positivity)) ha ht
      · nlinarith
      · nlinarith
    unfold coffee mass rate
    rw [Matrix.sub_apply, Matrix.of_apply, zero_mul,Real.exp_zero,one_mul, mul_right_comm _ (A j k), ← Real.exp_neg, ← Real.exp_add]
    change |Real.exp (a*σ*w j i+ -(a*σ*w k i))*A j k-A j k| ≤ a*(Real.exp (σ*w j k)*_)
    rw [show a*σ*w j i+ -(a*σ*w k i) = a*(σ*(w j i-w k i)) by ring,← sub_one_mul,abs_mul, ← mul_assoc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (abs_nonneg (A j k))
  constructor
  · exact mul_nonneg ha h.pos
  · intro j; apply (sum_le_sum (fun k _ => hcost j k)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h.row _) ha
  intro k; apply (sum_le_sum (fun j _ => hcost j k)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h.col _) ha

private lemma solved (A : Gaussian.Table V) (h : Gapped A ε) (hA : A.IsSymm) (he : 0 < ε) : A.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_iff_isSymm.mpr hA, fun x hx => ?_⟩
  simp only [star_trivial]; obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  exact (mul_pos he ((sq_pos_of_ne_zero hi).trans_le (single_le_sum (f:=fun i => x i ^2) (fun i _ => sq_nonneg _) (mem_univ i)))).trans_le (h x)

lemma inverse_tilt {σ M ε : ℝ} (he : 0 < ε) (hM : 0 ≤ M) (hs : 0 < σ) :
    ∃ v C : ℝ, 0<v ∧ v≤σ ∧ 0<C ∧
    ∀ {c : Side} {V : Type} [Fintype V] [DecidableEq V] (p : V → Site c) (A : Gaussian.Table V),
      Pours A p p σ M → Gapped A ε → A.IsSymm →
      ∀ i j : V, rate v (separation (p j) (p i)) * |A⁻¹ j i| ≤ C := by
  let a := min 1 ((ε/2)/(M+1))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hl : a*M ≤ ε/2 := calc
    _ ≤ a*(M+1) := by gcongr; exact le_add_of_nonneg_right (by positivity)
    _ ≤ _ := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  let v := a*σ
  have hv : 0<v := mul_pos ha hs
  let C := 2/ε
  have hc : 0<C := by unfold C; positivity
  refine ⟨v,C,hv,(mul_le_of_le_one_left hs.le (min_le_left ..)),hc,?_⟩
  intro c V _ _ p A h hx hA i j
  let L := coffee p A v i
  have hL := tilting p A h hs.le i ha.le (show a ≤ 1 from min_le_left ..)
  have H (x : Vec V) : (ε/2) * sumSq x ≤ x ⬝ᵥ (L *ᵥ x) := by
    have ht : |x ⬝ᵥ ((L-A) *ᵥ x)| ≤ (a*M)*(sumSq x+sumSq x)/2 := estimate hL _ _
    rw [sub_mulVec,dotProduct_sub] at ht
    have hw := (abs_le.mp ht).1; nlinarith only [hx x, hw, mul_le_mul_of_nonneg_right hl (sumSq_nn x)]
  let X := fun j => mass p v j i * A⁻¹ j i
  have hunit : A.PosDef := solved A hx hA he
  have hd : IsUnit A.det := (A.isUnit_iff_isUnit_det).1 hunit.isUnit
  have hrest : L *ᵥ X = Pi.single i 1 := by
    funext j
    change (∑ k, L j k * X k) = _
    have h1 (k : V) : L j k * X k = mass p v j i * (A j k * A⁻¹ k i) := by
      unfold L coffee X
      simp [mul_assoc,(rate_pos v (separation (p k) (p i))).ne',mass]
    simp_rw [h1]; rw [← mul_sum, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hd, Pi.single_apply]
    split
    next hj => subst j; simp [mass,rate]
    next hj => simp [Matrix.one_apply,hj]
  have hb := H X; rw [hrest, dotProduct] at hb
  have hw' : (X ⬝ᵥ Pi.single i 1) = X i := by simp [dotProduct,Pi.single_apply]
  rw [show (∑ x, X x * Pi.single i (M:=fun _=>ℝ) 1 x)=X i from hw'] at hb
  have hw k : (X k)^2 ≤ sumSq X := single_le_sum (f:=fun k => X k ^2) (fun k _ => sq_nonneg _) (mem_univ k)
  have hk : |X j| ≤ C := by
    have hs := mul_le_mul_of_nonneg_left (hw i) (by positivity : 0 ≤ ε/2)
    have hu := mul_le_mul_of_nonneg_left (hw j) (by positivity : 0 ≤ ε/2)
    have ht : X i ≤ C := by unfold C; rw [le_div_iff₀ he]; by_contra! t; nlinarith
    by_contra! hp
    have hm : (ε/2)*C=1 := by unfold C; field_simp
    have hn := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hp hc.le (by decide : (2:ℕ)≠0)) (by positivity : 0<ε/2)
    rw [sq_abs] at hn; nlinarith [ht]
  simpa only [X,mass,abs_mul,abs_of_nonneg (rate_pos ..).le] using hk
end YM.Next.SectorChange.Schur
