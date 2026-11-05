import YM.Primitives.SMALL_FIELD_EXTERIOR.Range

/-!
# Normalized covariance estimate with site weights

In a conjugated Hessian gap regime one can charge inverse weights at the
second test. Unweighted reads off a Poincaré constant from the *actual*
Hessian lower bound; the weight clause needs its own verification. No
ambient coordinate count in this estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V u f g : Points ι → ℝ} {w : ι → ℝ} {r m d : ℝ}

private lemma calculus (hV : ContinuousOn V (cube ι r)) (hf : Regular r 1 f) (hg : Regular r 1 g) {q p : ι → ℝ} :
    |∑ i, q i * p i * bracket r V (pc i f) (pc i g)| ≤ Dirichlet q r V f * Dirichlet p r V g := by
  let a i := |q i| * size r V (pc i f)
  let b i := |p i| * size r V (pc i g)
  have he : (∑ i,a i*b i)^2 ≤ (Dirichlet q r V f * Dirichlet p r V g)^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    rw [mul_pow,dirichlet_sq,dirichlet_sq]
    simpa only [a,b,mul_pow,sq_abs] using hh
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (le_of_abs_le (abs_le_of_sq_le_sq he (mul_nonneg (dirichlet_nn ..) (dirichlet_nn ..))))
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul,abs_mul]; apply (mul_le_mul_of_nonneg_left (cauchy hV (hf.tangent_continuous i) (hg.tangent_continuous i))
    (by positivity : 0 ≤ |q i| * |p i|)).trans_eq
  unfold a b; ring
lemma inverse_weights (hr : 0 ≤ r) (hu : Neumann r u) (hf : Regular r 1 f) (hV : Regular r 2 V) (hw : ∀ i, w i ≠ 0) :
    |bracket r V (elliptic V u) f| ≤ Dirichlet w r V u * Dirichlet w⁻¹ r V f := by
  rw [hu.energy hr hV hf]
  simpa only [Pi.inv_apply,mul_inv_cancel₀ (hw _),one_mul] using calculus hV.cOn (hu.reg) hf (q:=w) (p:=w⁻¹)
lemma same_weights (hr : 0 ≤ r) (hu : Neumann r u) (hf : Regular r 1 f) (hV : Regular r 2 V) (w : ι → ℝ) :
    |bracket r V (adjRow w V u) f| ≤ Dirichlet w r V u * Dirichlet w r V f := by
  have hc (i) : ContinuousOn (w i^2 • row V i u) (cube ι r) := ((hu.row1 hV i).smul _).cOn
  unfold adjRow; rw [bracket_sum hV.cOn _ (fun i _ => hc i) hf.cOn]
  simp_rw [bracket_smul, hu.by_row hr (hV.mono (k:=1) (by norm_num)) hf, pow_two]
  exact calculus hV.cOn hu.reg hf

/-- Gradient estimate for approximate inverse on the Neumann range, in the
WEIGHTED counting metric. Thus the weighting method affects responses, not
merely pointwise entries of an inverse Hessian. -/
theorem gradient_budget (hr : 0 < r) (hV : Regular r 2 V) (hB : Charged r V 0) (hm : 0 < m)
    (hw : ∀ i,w i ≠ 0) (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m)
    (hf : Regular r 1 f) (h : raw r V f=0) (hd : 0 < d) :
    ∃ u, Neumann r u ∧ size r V (f-elliptic V u) ≤ d ∧ Dirichlet w r V u ≤ Dirichlet w r V f / m + d := by
  obtain ⟨K,hK,hy⟩ := row_size hr hV hB w
  let S := K*(size r V f+d)
  have hs : 0 < S := mul_pos hK (by have := size_nn r V f; linarith)
  let a := Dirichlet w r V f
  let ε := min d (m*d^2/S)
  have he : 0 < ε := lt_min hd (by positivity)
  obtain ⟨u,hu,hc⟩ := range_zero hr hV hB hf.cOn h he
  let L := elliptic V u; let A := adjRow w V u
  have hL : ContinuousOn L (cube ι r) := (hu.elliptic1 hV).cOn
  have hA : ContinuousOn A (cube ι r) := (Regular.fsum (n:=1) _ (f:=fun i=>w i^2 • row V i u) fun i _ =>
    (hu.row1 hV i).smul _).cOn
  have hi : size r V (f-L) ≤ d := hc.trans (min_le_left ..)
  refine ⟨u,hu,hi,?_⟩
  have hp : size r V A ≤ S := (hy u hu).trans (mul_le_mul_of_nonneg_left
    ((deficit hV.cOn hL hf.cOn).trans (add_le_add (le_refl _) hi)) hK.le)
  have hw : |bracket r V A L - bracket r V A f| ≤ m*d^2 := by
    rw [abs_sub_comm, bracket_sym r V A L,bracket_sym r V A f,← bracket_sub hV.cOn hf.cOn hL hA]
    exact (cauchy hV.cOn (hf.cOn.sub hL) hA).trans ((mul_le_mul
      (show size r V (f-L) ≤ m*d^2/S from hc.trans (min_le_right ..)) hp
      (size_nn ..) (by positivity)).trans_eq (by field_simp))
  let b := Dirichlet w r V u
  have h₁ : m*b^2 ≤ bracket r V A L := weighed hr.le hu hV (by assumption) hh
  have h₂ : bracket r V A L-bracket r V A f ≤ m*d^2 := le_of_abs_le hw
  have h₃ : bracket r V A f ≤ b*a := le_of_abs_le (same_weights hr.le hu hf hV _)
  have ha : 0 ≤ a/m := div_nonneg (dirichlet_nn ..) hm.le
  have hz : m*(a/m)=a := by field_simp
  change b ≤ a/m+d
  apply le_of_not_gt
  intro hv
  have hhh : m*d < m*b-a := by linarith only [mul_lt_mul_of_pos_left hv hm,hz]
  have h' := mul_le_mul_of_nonneg_left hhh.le (show 0 ≤ b from dirichlet_nn ..)
  have h'' := mul_lt_mul_of_pos_left (show d < b by linarith only [ha,hv]) (mul_pos hm hd)
  linarith

private lemma kernel (hr : 0 < r) (hV : Regular r 2 V) (hB : Charged r V 0) (hm : 0 < m)
    (hw : ∀ i,w i ≠ 0) (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m)
    (hf : Regular r 1 f) (h : raw r V f=0) (hg : Regular r 1 g) :
    |bracket r V f g| ≤ Dirichlet w r V f/m*Dirichlet w⁻¹ r V g := by
  refine le_of_forall_pos_le_add fun ε he => ?_
  let C := Dirichlet w⁻¹ r V g
  let a := size r V g
  have hC : 0 ≤ C := dirichlet_nn ..
  have ht : 0 < C+a+1 := by have ha : 0 ≤ a := size_nn ..; linarith
  let d := ε/(C+a+1)
  have hd : 0 < d := div_pos he ht
  obtain ⟨u,hu,hp,hs⟩ := gradient_budget hr hV hB hm hw hh hf h hd
  let L := elliptic V u
  have hL : ContinuousOn L (cube ι r) := (hu.elliptic1 hV).cOn
  calc
    _ ≤ |bracket r V L g| + |bracket r V (f-L) g| := by rw [bracket_sub hV.cOn hf.cOn hL hg.cOn];
                                                         exact abs_add_le .. |>.trans' (Eq.le (by rw [add_sub_cancel]))
    _ ≤ (Dirichlet w r V f/m+d)*C+d*a := add_le_add ((inverse_weights hr.le hu hg hV hw).trans
      (mul_le_mul_of_nonneg_right hs hC)) ((cauchy hV.cOn (hf.cOn.sub hL) hg.cOn).trans (mul_le_mul_of_nonneg_right hp (size_nn ..)))
    _ ≤ _ := by
      have heq : d*(C+a+1)=ε := div_mul_cancel₀ _ ht.ne'
      change _ ≤ _/m*C+ε; linarith

def mean (r : ℝ) (V f : Points ι → ℝ) : ℝ := raw r V f / raw r V 1

def covariance (r : ℝ) (V f g : Points ι → ℝ) := mean r V (f*g)- mean r V f * mean r V g

def chargeNorm (w : ι → ℝ) (r : ℝ) (V f : Points ι → ℝ) := Real.sqrt (∑ i, w i ^ 2 * mean r V (pc i f ^ 2))

lemma chargeNorm_nn (w : ι → ℝ) (r : ℝ) (V f : Points ι → ℝ) : 0 ≤ chargeNorm w r V f := Real.sqrt_nonneg _
lemma chargeNorm_eq (hr : 0 < r) (hV : Regular r 2 V) (w : ι → ℝ) (f : Points ι → ℝ) :
    chargeNorm w r V f = Dirichlet w r V f / Real.sqrt (raw r V 1) := by
  have hz := raw_one_pos hr hV.cOn
  unfold chargeNorm mean; simp_rw [← mul_div_assoc,← Finset.sum_div,pow_two (pc _ _)]
  rw [show ∑ x : ι, w x^2*raw r V (pc x f*pc x f) = Dirichlet w r V f ^2 by simp_rw [dirichlet_sq,size_sq]; rfl,
    Real.sqrt_div (by positivity), Real.sqrt_sq (dirichlet_nn ..)]

/-- The variance/covariance estimate in normalized units. Hessian hypotheses
sufficient here are positive weighting gap and ordinary convexity of
the total potential (genuine strong-convex uses include the scalar margin).
Both f and g genuine, no scalar/tensor/Hessian domination input on their laws. -/
theorem normalized (hr : 0 < r) (hV : Regular r 2 V) (hB : Charged r V 0) (hm : 0 < m)
    (hw : ∀ i,w i ≠ 0) (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m)
    (hf : Regular r 1 f) (hg : Regular r 1 g) :
    |covariance r V f g| ≤ chargeNorm w r V f / m * chargeNorm w⁻¹ r V g := by
  let Z := raw r V 1; let a := mean r V f
  have hp : 0 < Z := raw_one_pos hr hV.cOn
  let c : Points ι → ℝ := fun _ => a; let L := f-c
  have hi : c=a • 1 := by ext; simp [c]
  have H : Regular r 1 L := hf.sub (Regular.coefficient a)
  have ha : a*Z=raw r V f := div_mul_cancel₀ _ hp.ne'
  have hc : ContinuousOn c (cube ι r) := continuousOn_const
  have hz : raw r V L=0 := by unfold L; rw [raw_sub hV.cOn hf.cOn hc, hi,raw_smul]; exact sub_eq_zero.mpr ha.symm
  have he : covariance r V f g= bracket r V L g / Z := by
    unfold L; rw [bracket_sub hV.cOn hf.cOn hc hg.cOn,hi,bracket_smul]; unfold bracket covariance
    rw [one_mul]; change _/Z-a*(_/Z)=_/Z; ring
  have hq i : size r V (pc i L)=size r V (pc i f) := size_congr V (fun x hx => by
    unfold L
    rw [pc_minus i (hf.diff one_ne_zero hx) (differentiableAt_const a), show pc i c x=0 from congr_fun (pc_const i a) x, sub_zero])
  have hT : Dirichlet w r V L=Dirichlet w r V f := by unfold Dirichlet; simp_rw [hq]
  have hk := kernel hr hV hB hm hw hh H hz hg
  rw [hT] at hk
  rw [chargeNorm_eq hr hV, chargeNorm_eq hr hV,he,abs_div, abs_of_nonneg hp.le]
  exact (div_le_div_of_nonneg_right hk hp.le).trans_eq (by
    change _ = (_/Real.sqrt Z /m)*(_/Real.sqrt Z); field_simp; rw [Real.sq_sqrt hp.le])

-- ordinary Hessian Poincaré gap

end YM.Primitives.SmallFieldExterior
