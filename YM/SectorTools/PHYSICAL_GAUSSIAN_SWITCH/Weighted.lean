import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace
import YM.Next.MULTISOURCE.Curves
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal



/-!
# Weighted extension: not spending a volume in changing normalizations

Summable tails of quadratic coefficients measured by a diagonal w with
trace cost (in particular can pay tails around a support, where those
estimates are warranted). Linear shift costs squared counting norm of its
source, via ordinary Laplace at a linear argument, even if it's not small.
No small *total* sum required; do require small `sup` for w relative to
p and the actual reference C. Uses `VACUUM_STABILITY.Gaussian.Laplace`
scoring on the exact map specifying the cloud in SectorChange. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.Weighted
open Function Filter Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open scoped Topology BigOperators ENNReal MatrixOrder
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I]
variable {A D B : Covar I} {w u h : Vec I} {K p W : ℝ}

def Upper (K : ℝ) (A : Covar I) := ∀ x : Vec I, quad A x ≤ K*(x ⬝ᵥ x)

section gaussian
-- use Laplace notation directly
open Multi.Vacuum.Gauss

lemma root_pow (hD : D.PosSemidef) : CFC.sqrt D * CFC.sqrt D = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
lemma root_symm (D : Covar I) : (CFC.sqrt D).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian

omit [DecidableEq I] in
lemma rows (A : Covar I) (x : Vec I) : mapRows A x=A *ᵥ x := rfl
omit [DecidableEq I] in
lemma squares_dot (x : Vec I) : squares x=x ⬝ᵥ x := by unfold squares dotProduct; simp [sq]

lemma root_cost (hD : D.PosSemidef) (hu : Upper K D) : adjBound (CFC.sqrt (A:=Covar I) D) K := by
  intro y; let E := CFC.sqrt D
  change squares (mapRows E.transpose y) ≤ _
  rw [squares_dot,squares_dot, rows, (root_symm D).eq]
  rw [← Matrix.dotProduct_transpose_mulVec E y (E *ᵥ y), (root_symm D).eq, mulVec_mulVec, root_pow hD]
  exact hu y
lemma root_paid (D : Covar I) : MeasurePreserving (mapRows (CFC.sqrt (A:=Covar I) D)) (standard I) (cloud D) :=
  ⟨acts_meas _, paid _⟩

lemma weighted_cloud (hD : D.PosSemidef) (h : Upper K D) (hK : 0 ≤ K) (w : Vec I) (hw : ∀ i,0 ≤ w i)
    (hy : ∀ i,K*w i ≤ 1/4) :
    Integrable (fun x => Real.exp (pay w x)) (cloud D) ∧ (∫ x, Real.exp (pay w x) ∂cloud D) ≤ Real.exp (2*K*∑ i,w i) := by
  let f := fun x => Real.exp (pay w x)
  have hf : Measurable f := by unfold f pay; fun_prop
  obtain ⟨hi,he⟩:= pay_pull (root_paid D) f hf.aestronglyMeasurable
  obtain ⟨hg,hp⟩:= conditional (CFC.sqrt (A:=Covar I) D) K (root_cost hD h) hK w hw hy
  exact ⟨hi.mp hg, he ▸ hp.trans_eq (by simp [Finset.mul_sum,mul_assoc])⟩

lemma linear_cloud (hD : D.PosSemidef) (h : Upper K D) (u : Vec I) :
    Integrable (fun z => Real.exp (u ⬝ᵥ z)) (cloud D) ∧ (∫ z,Real.exp (u ⬝ᵥ z) ∂cloud D) ≤ Real.exp (K*(u ⬝ᵥ u)/2) := by
  let f := fun z => Real.exp (crossed u z)
  have hf : Measurable f := by unfold f crossed; fun_prop
  obtain ⟨hi,he⟩ := pay_pull (root_paid D) f hf.aestronglyMeasurable
  unfold f at hi he; simp_rw [rewrite_row] at hi he
  obtain ⟨hl,hv⟩:=scattered (mapRows (Function.swap (CFC.sqrt (A:=Covar I) D)) u)
  change Integrable _ _ ∧ (∫ z, Real.exp (crossed u z) ∂cloud D) ≤ _
  rw [← he,hv]
  exact ⟨hi.mp hl,Real.exp_monotone (by rw [← squares_dot]; gcongr; exact root_cost hD h u)⟩


end gaussian

open Multi.Vacuum.Gauss (pay)

/-- Diagonal absolute majorant for the quadratic perturbation (trace = ∑ w_i).
A convenient sufficient criterion by entry weights is `by_rows`. -/
structure Trace (B : Covar I) (w : Vec I) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  charge : ∀ x, |quad B x /2| ≤ pay w x

omit [DecidableEq I] in
lemma pay_pos (h : ∀ i, 0 ≤ w i) (x : Vec I) : 0 ≤ pay w x := Finset.sum_nonneg fun _ _ => mul_nonneg (h _) (sq_nonneg _)

def spend (p K W b : ℝ) := 4*p*K*W + 2*p^2*K*b -- b = squared count u


/-- Pair budget; include the opposite-tilt integrability needed for a lower
bound on the normalizer. No determinant replaced by an extensivity loss. -/
theorem event {s : ℝ} (hD : D.PosSemidef) (h : Upper K D) (hK : 0 ≤ K)
    (hw : Trace B w) (hW : ∑ i,w i ≤ W) (hp : 0 ≤ p) (he : ∀ i, K * (2*p*w i) ≤ 1/4) (hs : |s| ≤ p) :
    Integrable (fun z => kernel B u z ^ s) (cloud D) ∧
      (∫ z,kernel B u z ^ s ∂cloud D) ≤ Real.exp (spend p K W (u ⬝ᵥ u)) := by
  let q i := 2*p*w i
  have hq i : 0 ≤ q i := by unfold q; have := hw.nonneg i; positivity
  let f := fun x => Real.exp (pay q x)
  let t := (2*s) • u
  let g := fun x => Real.exp (t ⬝ᵥ x)
  have hf := weighted_cloud hD h hK q hq he; change Integrable f _ ∧ _ at hf
  have hg := linear_cloud hD h t
  let c := fun x => kernel B u x ^ s
  have hx x : ‖c x‖ ≤ (f x+g x)/2 := by
    let b := quad B x / 2
    have hm : -b*s ≤ p*pay w x := calc
      _ ≤ |b| *|s| := by simpa [abs_mul] using le_abs_self (-b*s)
      _ ≤ _ := by rw [mul_comm]; gcongr; exact hw.charge x
    have hd : pay q x = 2*(p* pay w x) := by unfold pay q; rw [Finset.mul_sum,Finset.mul_sum]; simp [mul_assoc]
    unfold c kernel
    rw [← Real.exp_mul, exponent,Real.norm_of_nonneg (Real.exp_pos _).le]
    change Real.exp ((_ - b)*s) ≤ _
    calc
      _ ≤ Real.exp (p*pay w x + s*(u ⬝ᵥ x)) := Real.exp_monotone (by linarith)
      _ ≤ _ := by
        unfold f g t; rw [smul_dotProduct,smul_eq_mul,hd]
        let a := p*pay w x; let b := s*(u ⬝ᵥ x)
        rw [show (2*s)*(u ⬝ᵥ x)=2*b by unfold b; ring,Real.exp_add,
          show 2*(p*pay w x)=a+a by unfold a; ring, show 2*b=b+b by ring, Real.exp_add,Real.exp_add]
        nlinarith [sq_nonneg (Real.exp a-Real.exp b)]
  have hbase : Integrable (fun x => (f x+g x)/2) (cloud D) := (hf.1.add hg.1).div_const _
  have hi : Integrable c (cloud D) := hbase.mono' (((continuous_kernel ..).measurable.pow measurable_const).aestronglyMeasurable) (Eventually.of_forall hx)
  have hv : (∫ z,c z ∂cloud D) ≤ ∫ z,(f z+g z)/2 ∂cloud D := integral_mono hi hbase (fun x => (le_abs_self _).trans (hx x))
  have h0 : 0 ≤ W := (Finset.sum_nonneg (fun i _ => hw.nonneg i)).trans hW
  have hU := sumsq_nonneg u
  let k:=spend p K W (u ⬝ᵥ u)
  have ha : (∫ z, f z ∂cloud D) ≤ Real.exp k := by
    refine hf.2.trans (Real.exp_monotone ?_)
    unfold k spend q; rw [← Finset.mul_sum]; nlinarith [mul_le_mul_of_nonneg_left hW (show 0≤2*K*(2*p) by positivity), mul_nonneg (show 0≤p^2*K by positivity) hU]
  have hb : (∫ z, g z ∂cloud D) ≤ Real.exp k := by
    refine hg.2.trans (Real.exp_monotone ?_)
    unfold k spend t; rw [smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]
    have ht : s^2 ≤ p^2 := by rw [← sq_abs s]; gcongr
    nlinarith only [show 0 ≤ p*K*W by positivity, mul_le_mul_of_nonneg_right ht (mul_nonneg hK hU)]
  rw [integral_div, integral_add hf.1 hg.1] at hv; exact ⟨hi,by change (∫ z,c z ∂cloud D)≤Real.exp k; linarith⟩

/-- Cauchy trick: needn't make the extensive trace small when lower bounding
the normalization. -/
lemma denominator {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hp : ∀ x,0 < f x) (hf : Integrable f μ) (hg : Integrable (fun x => (f x)⁻¹) μ) :
    1 ≤ (∫ x,f x ∂μ)*(∫ x,(f x)⁻¹ ∂μ) := by
  let h := fun x => Real.sqrt (f x)
  let g := fun x => Real.sqrt ((f x)⁻¹)
  have he x : h x*g x=1 := by unfold g; rw [Real.sqrt_inv]; exact mul_inv_cancel₀ (Real.sqrt_pos_of_pos (hp x)).ne'
  have ha x : h x^(2:ℝ) = f x := by rw [Real.rpow_two]; exact Real.sq_sqrt (hp _).le
  have hb x : g x^(2:ℝ) = (f x)⁻¹ := by rw [Real.rpow_two]; exact Real.sq_sqrt (inv_pos.mpr (hp _)).le
  have h1 : MemLp h (ENNReal.ofReal 2) μ := by
    rw [mem_by_norm (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1) (by norm_num)]
    change Integrable (fun x => ‖h x‖ ^ (2:ℝ)) μ
    simp_rw [Real.norm_of_nonneg (show 0 ≤ h _ from Real.sqrt_nonneg _),ha]; exact hf
  have h2 : MemLp g (ENNReal.ofReal 2) μ := by
    rw [mem_by_norm (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1) (by norm_num)]
    change Integrable (fun x => ‖g x‖ ^ (2:ℝ)) μ
    simp_rw [Real.norm_of_nonneg (show 0 ≤ g _ from Real.sqrt_nonneg _),hb]; exact hg
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two (Eventually.of_forall (show ∀ x,0≤h x from fun _=>Real.sqrt_nonneg _))
    (Eventually.of_forall (show ∀ x,0≤g x from fun _ => Real.sqrt_nonneg _)) h1 h2
  simp_rw [he,ha,hb, integral_const,probReal_univ,one_smul,← Real.sqrt_eq_rpow] at hh
  have hu := Real.sq_sqrt (integral_nonneg_of_ae (μ:=μ) (Eventually.of_forall fun x => (hp x).le))
  have hv := Real.sq_sqrt (integral_nonneg_of_ae (μ:=μ) (Eventually.of_forall fun x => (inv_pos.mpr (hp x)).le))
  let a:=∫ x,f x ∂μ; let b:=∫ x,(f x)⁻¹ ∂μ
  change (Real.sqrt a)^2=a at hu; change (Real.sqrt b)^2=b at hv
  change _ ≤ Real.sqrt a*Real.sqrt b at hh
  change _ ≤ a*b
  calc
    (1:ℝ)=1^2 := by norm_num
    _ ≤ (Real.sqrt a * Real.sqrt b)^2 := pow_le_pow_left₀ zero_le_one hh _
    _ = _ := by rw [mul_pow,hu,hv]

/-- Weighted comparison, using the true determinant multiplier via
normalization. Even implies positive definite `mixed A D p` (not
required as another antecedent). -/
theorem weighted (hA : A.PosDef) (hD : D.PosDef) (hd : Upper K D) (hk : 0 ≤ K)
    (hw : Trace (A⁻¹-D⁻¹) w) (hW : ∑ i,w i ≤ W) (hp : 1 ≤ p) (he : ∀ i,K*(2*p*w i) ≤ 1/4) (h : Vec I) :
    let t:=-(A⁻¹ *ᵥ h)
    let k:=spend p K W (t ⬝ᵥ t)
    MemLp (trade A D h) (ENNReal.ofReal p) (cloud D) ∧ (mixed A D p).PosDef ∧
      price A D p h ≤ Real.exp ((p+1)*k) := by
  intro t k; let f := kernel (A⁻¹-D⁻¹) t
  let c:=tax A D h
  have hc : 0 < c := tax_pos hA hD _
  have hpp : 0<p := zero_lt_one.trans_le hp
  have hs := fun (s:ℝ) (hs:|s|≤p) => event (u:=t) hD.posSemidef hd hk hw hW hpp.le he hs
  obtain ⟨h1,h2⟩ := hs p (abs_of_nonneg hpp.le).le
  have hr (z : Vec I) : trade A D h z = c*f z := trade_as_potential hA D h z
  have hf z : 0 < f z := kernel_pos ..
  have hv z : trade A D h z^p=c^p*f z^p := by rw [hr,Real.mul_rpow hc.le (hf z).le]
  have ht : MemLp (trade A D h) (ENNReal.ofReal p) (cloud D) := by
    rw [mem_by_rpow (trade_cont ..).measurable (fun _ => (trade_pos hA hD _ _).le) hpp]
    simp_rw [hv]; exact h1.const_mul _
  have hM := (trade_mem_iff hA hD hpp).mp ht
  obtain ⟨ha,_⟩:=hs 1 (by simpa using hp); obtain ⟨hb,hl⟩:=hs (-1) (by simpa using hp)
  simp_rw [Real.rpow_one] at ha; simp_rw [Real.rpow_neg_one] at hb hl
  have hh:=denominator (μ:=cloud D) hf ha hb; have hi:=(normalized_trade hA hD h).2
  simp_rw [hr,integral_const_mul] at hi
  have hx : c ≤ Real.exp k := by
    refine le_trans ?_ hl
    change c ≤ ∫ x, (f x)⁻¹ ∂cloud D
    calc
      c=c*1 := by ring
      _ ≤ c*((∫ x,f x ∂cloud D)*∫ x,(f x)⁻¹ ∂cloud D) := by gcongr
      _ = _ := by rw [← mul_assoc,hi,one_mul]
  refine ⟨ht,hM,?_⟩
  rw [← trade_integral hA hD hM]; simp_rw [hv,integral_const_mul]
  have hg : (∫ z,f z^p ∂cloud D) ≤ Real.exp k := h2
  calc
    _ ≤ Real.exp k ^ p * Real.exp k := mul_le_mul (Real.rpow_le_rpow hc.le hx hpp.le) hg
      (integral_nonneg fun z => Real.rpow_nonneg (hf z).le _) (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = _ := by rw [←Real.exp_mul, ← Real.exp_add]; ring_nf

omit [DecidableEq I] in
/-- Entrywise sufficient check for tails at arbitrary supports. -/
theorem by_rows (h : B.IsSymm) (hw : ∀ i,0 ≤ w i) (he : ∀ i, ∑ j, |B i j| ≤ 2*w i) : Trace B w := by
  refine ⟨hw,fun x => ?_⟩
  let a := ∑ i, 2*w i*x i^2
  have ht : (∑ i, ∑ j, |B i j| *(x i)^2) ≤ a := by
    simp_rw [← Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (he i) (sq_nonneg _)
  have hu : (∑ i, ∑ j, |B i j| *(x j)^2) ≤ a := by
    rw [Finset.sum_comm]; simpa only [show ∀ i j,B i j=B j i from fun i j => (congr_fun (congr_fun h i) j).symm] using ht
  have hh i j : 2*|x i*(B i j*x j)| ≤ |B i j| *(x i)^2 + |B i j| *(x j)^2 := by
    rw [abs_mul,abs_mul]
    have ht := sq_nonneg (|x i|-|x j|); rw [sub_sq,sq_abs,sq_abs] at ht
    nlinarith [mul_nonneg (abs_nonneg (B i j)) ht]
  have hv : |quad B x| ≤ ∑ i,∑ j,|x i*(B i j*x j)| := by
    unfold quad Matrix.mulVec dotProduct; simp_rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs ..)
  have hz : (2:ℝ)*(∑ i,∑ j,|x i*(B i j*x j)|)≤ 2*a := by
    simp_rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (g:=fun i => ∑ j, (|B i j| *(x i)^2+|B i j| *(x j)^2)) (fun i _ => Finset.sum_le_sum fun j _ => hh i j)) ?_
    simp_rw [Finset.sum_add_distrib]; linarith
  have hy : a=2*pay w x := by unfold a pay; rw [Finset.mul_sum]; simp [mul_assoc]
  rw [abs_div,abs_two]; linarith
end YM.SectorTools.PhysicalGaussianSwitch.Weighted
