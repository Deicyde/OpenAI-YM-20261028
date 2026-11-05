import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Window
import YM.Push.FREE_RESOLVENT.Torus


/-!
# Compare any number of windows to the *same* Gram precision

All in actual exponential row/column currency. Purchase the two
prescriptions in question simultaneously rather than switch the reference
halfway through. For Π_u, E_u and discrepancy use the FreeResolvent
weighted inverse machinery (keeps the integrable u cost on discrepancy!)
on a Gapped input from SectorChange. Include switched precision cost in
the *weighted* norm. Keep this comparison (and later its relative
change of real Gaussian) separate from ordered log-chain tasks. Numerical
only here, no nonlinearity assumptions smuggled in. Addresses implemented
in the applications, arbitrary Near survey here.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange Function Set Matrix FreeResolvent Cost
open scoped Classical BigOperators
variable {ι κ X : Type} [Fintype ι] [DecidableEq ι] {D : Cost X} {a : ι → X}

/-- Exact currency adapter (Pours uses initial-to-final column distance
and additionally asserts cost nonnegative, even when both index types empty).
Includes rectangular labels. -/
lemma pours_iff [Fintype κ] {c : Lattice.Side} {a : ι → Lattice.Site c} {b : κ → Lattice.Site c}
    {s C : ℝ} {L : Matrix ι κ ℝ} :
    SectorChange.Schur.Pours L a b s C ↔ 0 ≤ C ∧ (native c).Schur a b s C L := by
  have he i j : (native c).weight s (b j) (a i) = SectorChange.Wisps.rate s (Lattice.separation (a i) (b j)) := by
    rw [Cost.weight_symm]; rfl
  constructor
  · intro h
    refine ⟨h.pos,⟨⟨h.row⟩,⟨fun j => ?_⟩⟩⟩
    simp only [he,Matrix.transpose_apply]; exact h.col _
  rintro ⟨hc,h⟩
  refine ⟨hc,h.rows.bound,fun j => ?_⟩
  simpa only [he,Matrix.transpose_apply] using h.cols.bound j

lemma gapped_iff {s : ℝ} {Q : Matrix ι ι ℝ} : SectorChange.Schur.Gapped Q s ↔ FreeResolvent.Gap Q s := by
  constructor
  · intro h; exact ⟨fun i => by simpa [SectorChange.Schur.sumSq_dot] using h i⟩
  intro h i; rw [SectorChange.Schur.sumSq_dot]; exact h.lower i

lemma gap_positive {s : ℝ} {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (h : FreeResolvent.Gap Q s) (hs : 0<s) : Q.PosDef :=
  SectorChange.Schur.dissolves (gapped_iff.mpr h) hQ hs

/-- Quoted by maximal weighted absolute row and transpose-row in the
given cost. Not just points. -/
lemma mirrored {s C : ℝ} {Q : Matrix ι ι ℝ} (h : D.Schur a a s C Q) : D.Schur a a s C (mirror Q) :=
  ((h.add h.transpose).smul (1/2)).mono le_rfl (le_of_eq (by rw [abs_of_pos (by norm_num)]; ring))
lemma mirror_symm_eq {Q : Matrix ι ι ℝ} (h : Q.IsSymm) : mirror Q=Q := by
  unfold mirror; rw [show Q.transpose=Q from h]; module
lemma mirror_sub (Q M : Matrix ι ι ℝ) : mirror (Q-M)=mirror Q-mirror M := by
  unfold mirror; rw [Matrix.transpose_sub,show Q-M+(Q.transpose-M.transpose)=Q+Q.transpose-(M+M.transpose) by abel,smul_sub]
lemma symm_resolve (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (u : ℝ) : (resolve Q u).IsSymm := by
  unfold Matrix.IsSymm resolve; rw [Matrix.transpose_nonsing_inv,Matrix.transpose_add,Matrix.transpose_smul,hQ.eq,Matrix.transpose_one]

/-- Inverting a perturbation of identity in the *same* Schur norm:
A posteriori pricing, no series/log branch. Check columns too. No
lower bound on δ needed here. -/
private lemma row_shock (A E : Matrix ι ι ℝ) (n δ : ℝ) (hδ : δ ≤ 1/2) (hn : 0 ≤ n)
    (h : A=1-A*E) (he : D.Rows a a n δ E) : D.Rows a a n (1+2*δ) A := by
  constructor; intro i
  let v (j k : ι) := D.weight n (a j) (a k)
  let C := ∑ j, v i j * |A i j|
  change C ≤ 1+2*δ
  have hh : C ≤ 1+C*δ := calc
    _ ≤ (∑ j, v i j * |(1:Matrix ι ι ℝ) i j|)+∑ j, v i j * |(A*E) i j| := by
      unfold C; nth_rw 1 [h]; rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub ..) (D.weight_nn ..)
    _ ≤ 1+C*δ := by
      apply add_le_add (show _ ≤ (1:ℝ) from Cost.Rows.one.bound i)
      calc
        _ ≤ ∑ j, ∑ k, (v i k * |A i k|)*(v k j * |E k j|) := Finset.sum_le_sum fun j _ => Cost.Rows.term_mul (D:=D) hn a a a A E i j
        _ ≤ _ := by
          rw [Finset.sum_comm]; unfold C; rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (he.bound k) (mul_nonneg (D.weight_nn ..) (abs_nonneg _))
  have hc : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg (D.weight_nn ..) (abs_nonneg _)
  have hE : 0 ≤ δ := (Finset.sum_nonneg (s:=Finset.univ) (fun j (_ : j ∈ Finset.univ) => mul_nonneg (D.weight_nn n (a i) (a j)) (abs_nonneg (E i j)))).trans (he.bound _)
  have hh' : C ≤ 2 := by nlinarith
  nlinarith

lemma shock {A E : Matrix ι ι ℝ} {s δ : ℝ} (hδ : δ ≤ 1/2) (hs : 0 ≤ s)
    (hA : A=1+E) (h : IsUnit A.det) (he : D.Schur a a s δ E) : D.Schur a a s (1+2*δ) A⁻¹ := by
  have hr := A.nonsing_inv_mul h; have hl := A.mul_nonsing_inv h
  let B := A⁻¹
  change B * A = _ at hr; change A * B = _ at hl
  rw [hA,Matrix.mul_add,Matrix.mul_one] at hr; rw [hA,Matrix.add_mul,Matrix.one_mul] at hl
  have hx := congr_arg Matrix.transpose hl
  simp only [Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_mul] at hx
  exact ⟨row_shock B _ s δ hδ hs (by rw [← hr]; abel) he.rows, row_shock B.transpose _ s δ hδ hs (by rw [← hx]; abel) he.cols⟩

/-- Precision discrepancy without forgetting the exponential norm. -/
theorem reversePrice {A C : Matrix ι ι ℝ} {s K e : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (he : 0 ≤ e)
    (ha : D.Schur a a s K A) (hA : A.PosDef) (hC : C.PosDef)
    (hr : D.Schur a a s e (C-A⁻¹)) (hd : K*e ≤ 1/2) :
    D.Schur a a s ((1+2*(K*e))*(K*e)*K) (C⁻¹-A) := by
  let T := A*C
  have h : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA.isUnit
  have ht : IsUnit T.det := by unfold T; rw [Matrix.det_mul]; exact h.mul (C.isUnit_iff_isUnit_det.mp hC.isUnit)
  have hj : D.Schur a a s (K*e) (T-1) := by
    rw [show T-1=A*(C-A⁻¹) from (by unfold T; rw [Matrix.mul_sub,A.mul_nonsing_inv h])]; exact ha.mul hr hs hK he
  have hB := shock hd hs (show T=1+(T-1) from (by abel)) ht hj
  have hh : C⁻¹-A=-(T⁻¹*(T-1)*A) := by
    rw [Matrix.mul_sub, Matrix.mul_one,T.nonsing_inv_mul ht,Matrix.sub_mul,Matrix.one_mul,neg_sub]
    unfold T; rw [Matrix.mul_inv_rev,Matrix.mul_assoc,A.nonsing_inv_mul h, Matrix.mul_one]
  have he' : 0 ≤ K*e := mul_nonneg hK he
  rw [hh]
  exact ((hB.mul hj hs (by linarith) he').mul ha hs (by positivity) hK).neg

/-- Mixed Schur test in Cost API. No sup-by-volume. -/
lemma mixed [Fintype κ] {A : Matrix ι κ ℝ} {b : κ → X} {M : ℝ} (h : D.Schur a b 0 M A)
    (x : ι → ℝ) (y : κ → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ M*((x ⬝ᵥ x)+(y ⬝ᵥ y))/2 := by
  have hi i j : |x i*(A i j*y j)| ≤ |A i j| * ((x i*x i)+(y j*y j))/2 := by
    rw [abs_mul,abs_mul]
    have he : |x i| *|y j| ≤ ((x i*x i)+(y j*y j))/2 := by
      have hv := sq_nonneg (|x i|-|y j|); rw [sub_sq,sq_abs,sq_abs] at hv; linarith
    nlinarith only [mul_le_mul_of_nonneg_left he (abs_nonneg (A i j))]
  unfold mulVec dotProduct
  simp_rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  refine (Finset.sum_le_sum (g:=fun i => ∑ j, |A i j| * ((x i*x i)+(y j*y j))/2) (fun i _ => (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j _ => hi i j))).trans ?_
  have hr i := h.rows.bound i; have hc j := h.cols.bound j
  simp_rw [Cost.weight_zero,one_mul] at hr hc
  simp_rw [← Finset.sum_div,mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
  rw [show ∑ i, ∑ j, |A i j| * (y j*y j)=∑ j, (∑ i, |A i j|)*(y j*y j) from ?_]
  swap
  · rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul]
  rw [Finset.mul_sum,Finset.mul_sum]
  gcongr
  all_goals first | exact mul_self_nonneg _ | exact hr _ | exact hc _

/-- Convenient counting gap on a full inverse. -/
lemma flipped_gap {A : Matrix ι ι ℝ} {η K : ℝ}
    (he : 0 < η) (hg : FreeResolvent.Gap A η) (hK : 0 ≤ K) (h : D.Schur a a 0 K A) :
    FreeResolvent.Gap A⁻¹ (η/(K+1)^2) := by
  constructor; intro x
  let B:=A⁻¹; let k:=K+1
  have hk : 0 < k := by unfold k; positivity
  let y := B *ᵥ x
  have ho : A*ᵥ y=x := by unfold y B; rw [Matrix.mulVec_mulVec,A.mul_nonsing_inv (hg.unit_det he),Matrix.one_mulVec]
  have hh := hg.lower y; rw [ho,dotProduct_comm y x] at hh
  apply le_trans _ hh
  have hm := mixed (h.mono le_rfl (show K ≤ k from (by unfold k; linarith))) (k⁻¹ • x) y
  rw [ho,smul_dotProduct, dotProduct_smul,smul_dotProduct] at hm
  simp only [smul_eq_mul] at hm
  have hi := le_of_abs_le hm
  field_simp at hi
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  change _ ≤ _ * k^2
  nlinarith

/-- One window quote. Explicit fixed data: µ for probe/full Schur
summation (use only γ < µ in difference), at chosen volume budget V.
No symmetry prerequisite on Q, only on precision applications later. -/
structure Margin (T : ι → Set ι) (Q : Gaussian.Table ι) (D : Cost X) (a : ι → X) (s M η V μ γ R : ℝ) : Prop where
  income : D.Schur a a s M Q
  gap : FreeResolvent.Gap Q η
  width : 0 < s
  upper : 0 ≤ M
  lower : 0 < η
  bulk : 0 ≤ V
  mass : D.Volume a (safeRate s M η-μ) V
  rates : 0 < γ ∧ γ < μ ∧ μ ≤ s
  centers (i) : i∈T i
  spans : (setSurvey T centers).Near D a R


def stampFee (V η : ℝ) := V*(min (η/2) 1)⁻¹
lemma stampFee_nn {V η : ℝ} (hv : 0 ≤ V) (he : 0<η) : 0 ≤ stampFee V η := by
  unfold stampFee; exact mul_nonneg hv (inv_nonneg.mpr (le_min (by positivity) zero_le_one))

variable {T : ι → Set ι} {Q : Gaussian.Table ι} {s M η V μ γ R : ℝ}

theorem fine (H : Margin T Q D a s M η V μ γ R) {u : ℝ} (hu : 0 ≤ u) :
    let P := pane T Q u
    let E := (Q+u • 1)*P-1
    let C := stampFee V η
    D.Schur a a μ (C*(1+u)⁻¹) P ∧ D.Schur a a μ (C*(1+u)⁻¹) (resolve Q u) ∧
      D.Schur a a γ (Real.exp (-(μ-γ)*R)*(M*C)*(1+u)⁻¹) E ∧
        D.Schur a a γ (Real.exp (-(μ-γ)*R)*(M*C^2)*((1+u)⁻¹)^2) (P-resolve Q u) := by
  intro P E C
  let W := setSurvey T H.centers
  have he : W.inspect Q u=P := inspect_sets T H.centers Q u
  have hQ := H.income
  have h₀ := H.gap
  have hh := H.width
  have hm := H.upper
  have hi := H.lower
  have hv := H.mass
  have ha := H.rates.1.le; have hl := H.rates.2.1.le; have hx := H.rates.2.2
  have hV := H.bulk
  let θ := (1+u)⁻¹; let c := (η/2+u)⁻¹
  have ht : 0 ≤ θ := by unfold θ; positivity
  have hφ := (Real.exp_pos (-(μ-γ)*R)).le
  have hc : 0 ≤ V*c := mul_nonneg hV (by unfold c; positivity)
  have hw : V*c ≤ C*θ := by
    refine (mul_le_mul_of_nonneg_left (uniform_shift η u hi hu) hV).trans_eq ?_
    unfold C stampFee θ; ring
  rw [show E=W.error Q u from (by unfold E FreeResolvent.Window.Survey.error; rw [he]),← he]
  refine ⟨(W.prices hu hi hh hm hQ h₀ hv).mono le_rfl hw,
    (resolve_schur hm hh hQ h₀ hi hu hv).mono le_rfl hw,
    (FreeResolvent.Window.Survey.error_price H.spans hu hi hh hm (ha.trans hl) hl hx hV hQ h₀ hv).mono le_rfl ?_,
    (FreeResolvent.Window.Survey.difference H.spans hu hi hh hm ha hl hx hV hQ h₀ hv).mono le_rfl ?_⟩
  · calc
      _ ≤ Real.exp _*(M*(C*θ)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hm) hφ
      _ = _ := by unfold θ; ring
  have hC : 0 ≤ C*θ := hc.trans hw
  calc
    _ ≤ C*θ*(Real.exp (-(μ-γ)*R)*(M*(C*θ))) := mul_le_mul hw
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hm) hφ)
      (mul_nonneg hφ (mul_nonneg hm hc)) hC
    _ = _ := by unfold θ; ring

/-- Uniform in all such
windows; covariance and precision error retain the weight. -/
theorem covariance (H : Margin T Q D a s M η V μ γ R) (hQ : Q.IsSymm) :
    let C := stampFee V η
    let Y := resolve Q 0
    let Z := mirror (pane T Q 0)
    let e := Real.exp (-(μ-γ)*R)*(M*C^2)
    let L := η/(M+1)^2
    e < L/2 → M*e ≤ 1/2 →
    Q.PosDef ∧ Z.PosDef ∧ FreeResolvent.Gap Z (L/2) ∧
      D.Schur a a μ C Z ∧ D.Schur a a γ e (Z-Y) ∧ D.Schur a a γ (2*M^2*e) (Z⁻¹-Q) ∧
      D.Schur a a γ (M*e) (Q*Z-1) := by
  intro C Y Z e L he hd
  have hm := H.upper; have hη := H.lower
  have hL : 0 < L := by unfold L; positivity
  have hs := H.rates.1.le; have hy := H.rates.2.1.le
  have ha := symm_resolve Q hQ 0
  have h : Q.PosDef := gap_positive hQ H.gap hη
  have hf := fine H (u:=0) le_rfl
  obtain ⟨hp,-,-,h₀⟩ := hf
  have ht : D.Schur a a γ e (Z-Y) := by
    unfold Z Y; rw [← mirror_symm_eq ha,← mirror_sub]
    exact mirrored (by simpa only [add_zero,inv_one,mul_one,one_pow] using h₀)
  have hn := H.income.mono (hs.trans (hy.trans H.rates.2.2)) le_rfl
  have hh : Q⁻¹=Y := by unfold Y resolve; rw [zero_smul,add_zero]
  have hx : FreeResolvent.Gap Z (L/2) := by
    have hc : FreeResolvent.Gap Y L := hh ▸ flipped_gap hη H.gap hm hn
    exact (hc.perturb (ht.mono hs le_rfl)).mono (by linarith)
  have hv : Z.PosDef := gap_positive (mirror_symm _) hx (half_pos hL)
  have hb : 0 ≤ e := by unfold e; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hm (sq_nonneg _))
  have hc := H.income.mono (hy.trans H.rates.2.2) le_rfl
  refine ⟨h,hv,hx,mirrored (by simpa only [add_zero,inv_one,mul_one] using hp),ht,
    (reversePrice hs hm hb hc h hv (hh.symm ▸ ht) hd).mono le_rfl ?_,?_⟩
  · have hN : 0 ≤ M*e*M := by positivity
    calc
      _ = (1+2*(M*e))*(M*e*M) := by ring
      _ ≤ 2*(M*e*M) := by gcongr; linarith
      _ = _ := by ring
  rw [show Q*Z-1=Q*(Z-Y) from (by rw [← hh,Matrix.mul_sub,Q.mul_nonsing_inv (H.gap.unit_det hη)])]
  exact hc.mul ht hs hm hb

end YM.AnalyticBridge.LocalGaussianLaws
