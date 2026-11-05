import YM.Push.STRESS_FLUX.Annular
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching

/-!
Reverse checks on a proposed calibration (for use on the FREE Maxwell
obligation, **not** assuming translation/rotation laws to produce interacting
fluxes). At separated positions conservation and symmetry are FORCED by the
two shell identities themselves, via integration by parts on displaced smooth
cutoffs. Includes the one-point test even though windows are only asked when
another field is present; pad any exterior with a distant unit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Reverse
open Table Work.A01 Function Filter Set MeasureTheory Analysis Metric
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ} {x : Points (n+1)} {V : E4 → E4} {J : S.Stress} {P : Climb.Parts S} {Z : Ward.SpinRows S}

lemma extend (χ ψ : E4 → ℝ) (hw : Window x χ) (he : ContDiff ℝ ∞ ψ) (hp : HasCompactSupport ψ) (ha : ∀ i, x i ∉ tsupport ψ) : Window x (χ+ψ) := by
  have ht i := notMem_tsupport_iff_eventuallyEq.mp (ha i)
  refine ⟨hw.1.add he,hw.2.1.add hp,?_,fun i => notMem_tsupport_iff_eventuallyEq.mpr ?_⟩
  · filter_upwards [hw.2.2.1,ht 0] with _ hg hc; exact (congr_arg₂ (· + ·) hg hc).trans (add_zero _)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 i),ht i.succ] with _ h g
  simp [h,g]

/-- The elementary real-test lemma, not assuming regularity of g off the open set. -/
lemma fundamental (g : E4 → ℂ) (E : Set E4) (he : IsOpen E) (hg : ContinuousOn g E) (ht : ∀ ψ : E4 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ E → (∫ y, ψ y • g y)=0) : EqOn g 0 E := by
  intro z hz; by_contra! h0
  let f := fun y => (star (g z) * g y).re
  have hf : ContinuousOn f E := Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hg)
  have hF : 0 < f z := by rw [show f z = Complex.normSq (g z) from congr_arg Complex.re ((mul_comm ..).trans (Complex.mul_conj _))]; exact Complex.normSq_pos.mpr h0
  obtain ⟨t,ht',h⟩ := nhds_basis_closedBall.mem_iff.mp (show E ∩ {y | 0 < f y} ∈ 𝓝 z from ((he.eventually_mem hz).and ((hf.continuousAt (he.mem_nhds hz)).eventually (lt_mem_nhds hF))))
  let B : ContDiffBump z := ⟨t/2,t,by positivity,by linarith⟩
  let u := fun y => B y * f y
  have hb : tsupport (B : E4 → ℝ) ⊆ E ∩ {y | 0 < f y} := B.tsupport_eq ▸ h
  have hp : Continuous u := continuous_iff_continuousAt.mpr fun y => by
    by_cases hy : y ∈ tsupport (B : E4 → ℝ)
    · exact B.continuous.continuousAt.mul (hf.continuousAt (he.mem_nhds (hb hy).1))
    exact (continuousAt_const (y:=(0:ℝ))).congr ((notMem_tsupport_iff_eventuallyEq.mp hy).mono fun _ hx => by simp [u,hx])
  have hu : 0 ≤ u := fun y => by
    by_cases hy : y∈tsupport (B:E4→ℝ)
    · exact mul_nonneg B.nonneg ((hb hy).2.le)
    simp [u,image_eq_zero_of_notMem_tsupport hy]
  have H := hp.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ:=volume) (B.hasCompactSupport.mul_right) hu (x:=z) (by simpa [u,show B z = 1 from B.eventuallyEq_one.self_of_nhds] using hF.ne')
  have hr := Complex.reCLM.integral_comp_comm ((cutoff_integrable B.hasCompactSupport B.continuous (fun y hy => hg.continuousAt (he.mem_nhds (hb hy).1))).const_mul (star (g z)))
  rw [integral_const_mul, ht B B.contDiff B.hasCompactSupport (hb.trans inter_subset_left),mul_zero, map_zero] at hr
  apply H.ne'; convert hr using 1
  apply integral_congr_ae; filter_upwards with y; change B y * f y = (star (g z) * (B y • g y)).re; rw [mul_smul_comm, Complex.real_smul]; simp [f]

lemma flux_ibp (hs : S.Smooth) (hx : x∈conf _) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun y => V y b)) (J : S.Stress) (q : Fin n → S.Tag) (B : S.Field d)
    (h : ∀ χ ψ, Window x χ → Window x ψ → flux J χ V x q B = flux J ψ V x q B) :
    ∀ y, Points.cons y x ∈ conf _ → ∑ a, D (basis a) (current J V x (Fin.cons ⟨d,B⟩ q) a) y = 0 := by
  let E := (fun y => Points.cons y x) ⁻¹' conf _
  let F := current J V x (Fin.cons (α:=fun _ => S.Tag) ⟨d,B⟩ q)
  let g y := ∑ a, D (basis a) (F a) y
  have he : IsOpen E := (conf_open _).preimage (f:=fun y => Points.cons y x) (shifting_head x ▸ (headDir (n+1)).continuous.add continuous_const)
  have hF a y (hy : y∈E) := smooth_current J V (Fin.cons ⟨d,B⟩ q) a hv hy hs
  have hg a y (hy : y∈E) := (dSmooth (m:=∞) (hF a y hy) (basis a) (by simp)).continuousAt
  apply fun y hy => fundamental g E he (continuousOn_finsetSum _ (fun a _ y hy => (hg a y hy).continuousWithinAt)) _ hy
  intro _ _ ψ hc hk hh
  have hy (i : Fin (n+1)) : x i ∉ tsupport ψ := fun h => (Fin.succ_ne_zero i) (hh h (show Points.cons (x i) x i.succ = Points.cons (x i) x 0 from rfl))
  have h1 a := cutoff_integrable (hk.fderiv_apply ℝ (basis a)) ((hc.continuous_fderiv (by simp)).clm_apply continuous_const) (fun y hy => (hF a y (hh (tsupport_fderiv_apply_subset ℝ _ hy))).continuousAt)
  have h2 a := cutoff_integrable hk hc.continuous (fun y hy => hg a y (hh hy))
  have hu a : (∫ y, ψ y • D (basis a) (F a) y) = - ∫ y, D (basis a) ψ y • F a y := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (h1 a) (h2 a)
    (cutoff_integrable hk hc.continuous (fun y hy => (hF a y (hh hy)).continuousAt))
    (fun y _ => hc.differentiable (by simp) y) (fun y hy => (hF a y (hh hy)).differentiableAt (by simp))
  obtain ⟨χ,hw⟩ := exists_window x hx
  have hp {χ : E4 → ℝ} (hw : Window x χ) := fun a => Annular.expanded (J:=J) hx hw hs q B (fun b => (hv b).continuous) a
  have hψ := Reverse.extend χ ψ hw hc hk hy
  have hχ (y : E4) (a : Axis) : D (basis a) (χ+ψ) y • F a y = D (basis a) χ y • F a y + D (basis a) ψ y • F a y := by simp only [D,fderiv_add ((hw.1.differentiable (by simp)) y) (hc.differentiable (by simp) y), add_apply, add_smul]
  have h0 := h _ _ hw hψ
  simp_rw [flux, (hp hw _).2,(hp hψ _).2] at h0
  change -(∑ a, ∫ y, D (basis a) χ y • F a y) = -(∑ a, ∫ y, D (basis a) (χ+ψ) y • F a y) at h0
  have h3 a : Integrable (fun y => D (basis a) ψ y • F a y) := h1 a
  have h4 a : Integrable (fun y => D (basis a) χ y • F a y) := (hp hw a).1
  have h5 a : Integrable (fun y => ψ y • D (basis a) (F a) y) := h2 a
  simp_rw [hχ, integral_add (h4 _) (h3 _)] at h0
  simp_rw [g, Finset.smul_sum, integral_finsetSum _ fun a _ => h5 a,hu, Finset.sum_neg_distrib]
  rw [Finset.sum_add_distrib] at h0; linear_combination -h0

variable (J) (q : Fin n → S.Tag)
abbrev obs (a b : Axis) (x : Points n) (y : E4) := S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q)
lemma obs_deriv (b : Axis) (hs : S.Hierarchy) (hp : StressLaws S J P Z) (hx : x∈conf _) (B : S.Field d) (y : E4) (hy : Points.cons y x∈conf _) :
    ∑ a, D (basis a) (obs J (Fin.cons ⟨d,B⟩ q) a b x) y = 0 := by
  have h := flux_ibp (V:=fun _ => basis b) hs.smooth hx (fun _ => contDiff_const) J q B (fun χ ψ hχ hψ => by
    rw [flux_translation,flux_translation,hp.translation hx q hχ,hp.translation hx q hψ]) y hy
  have he a : current J (fun _ => basis b) x (Fin.cons (α:=fun _ => S.Tag) ⟨d,B⟩ q) a = obs J (Fin.cons ⟨d,B⟩ q) a b x := by funext; simp [current,obs,basis_eq]
  simpa only [he] using h

def generator (i j : Axis) : Ortho.Skew := ⟨Matrix.single i j 1 - Matrix.single j i 1,by
    change star (_ : M4) = -_
    ext a b; simp [Matrix.star_apply,Matrix.single_apply, and_comm, sub_eq_add_neg]⟩

lemma deriv_arm (K : Ortho.Skew) (w y : E4) (a b : Axis) : D (basis a) (fun y => orbital K w y b) y = K.val b a := by
  let f := (PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) b).comp (Matrix.toEuclideanLin K.val).toContinuousLinearMap
  rw [show (fun y => orbital K w y b) = fun y => f y - f w from funext fun y => map_sub f y w,D,fderiv_fun_sub f.differentiableAt (differentiableAt_const _), f.fderiv, (hasFDerivAt_const _ _).fderiv, sub_zero]
  exact M4.move_basis K.val b a

lemma obs_symm (i j : Axis) (hs : S.Hierarchy) (hp : StressLaws S J P Z) (hx : x∈conf _) (B : S.Field d) (y : E4) (hy : Points.cons y x∈conf _) :
    obs J (Fin.cons ⟨d,B⟩ q) i j x y = obs J (Fin.cons ⟨d,B⟩ q) j i x y := by
  let g := generator i j
  let V := orbital g (x 0)
  let F a b := obs J (Fin.cons ⟨d,B⟩ q) a b x
  have he := flux_ibp hs.smooth hx (smooth_orbital g (x 0)) J q B (fun χ ψ hχ hψ => (hp.rotation hx q hχ g d B).trans (hp.rotation hx q hψ g d B).symm) y hy
  have hv b := ((smooth_orbital g (x 0) b).differentiable (by simp) y)
  have hF (a b : Axis) : DifferentiableAt ℝ (F a b) y := (smooth_cons _ hs.smooth (⟨4,J a b⟩ : S.Tag) (Fin.cons ⟨d,B⟩ q) hy).differentiableAt (by simp)
  change (∑ a, D (basis a) (fun y => ∑ b : Axis, V y b • F a b y) y) = 0 at he
  have hu a : D (basis a) (fun y => ∑ b : Axis, V y b • F a b y) y = ∑ b, (g.val b a • F a b y + V y b • D (basis a) (F a b) y) := by
    unfold D
    rw [fderiv_fun_sum (fun b _ => (hv b).fun_smul (hF a b)), _root_.sum_apply]; apply Finset.sum_congr rfl; intro b _
    rw [fderiv_fun_smul (hv b) (hF a b)]; simp only [ContinuousLinearMap.smulRight_apply,add_apply,smul_apply]; rw [show fderiv ℝ _ y (basis a)=_ from deriv_arm g (x 0) y a b]; rw [add_comm]
  have hk a b : g.val b a • F a b y =
      (if i=b ∧ j=a then F a b y else 0) - (if j=b ∧ i=a then F a b y else 0) := by dsimp [g,generator,Matrix.single_apply]; rw [Complex.ofReal_sub,sub_mul]; split_ifs <;> simp
  simp_rw [hu, Finset.sum_add_distrib] at he
  have hz : ∑ a, ∑ b, V y b • D (basis a) (F a b) y = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro b _; rw [← Finset.smul_sum,obs_deriv J q b hs hp hx B y hy,smul_zero]
  rw [hz,add_zero] at he
  simp [hk,Finset.sum_sub_distrib, ite_and, Finset.sum_ite_eq] at he
  exact (sub_eq_zero.mp he).symm

lemma point_cons_tail (x : Points (n+1)) : Points.cons (x 0) (Points.tail x) = x := by ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def obs' (A : S.Field d) (p : S.Tag) {n : ℕ} (q : Fin n → S.Tag) (x : Points (n+1)) y := S.useAt S (Points.cons y x) (Fin.cons ⟨d,A⟩ (Fin.cons p q))
lemma front_ext_padded (hs : S.Basic) {A B : S.Field d} (he : ∀ (n : ℕ) (q : Fin n → S.Tag) (p : S.Tag) (x : Points (n+1)) (_hx : x ∈ conf _) (y : E4), Points.cons y x ∈ conf _ →
    obs' A p q x y = obs' B p q x y) : A=B := by
  apply S.field_ext hs.toSymmetric
  intro n q x hx
  obtain ⟨z,hz⟩ := (finite_range x.ofLp).exists_notMem
  let t := Points.cons (x 0) (Points.cons z (Points.tail x))
  let t' := Points.rearrange (exchangeFirst n) t
  have ht' : t ∈ conf _ := conf_cons (conf_cons (Points.tail_in hx) fun i hi => hz ⟨i.succ,hi.symm⟩) (fun i => Fin.cases (fun h => hz ⟨0,h⟩) (fun j h => Fin.succ_ne_zero _ (hx h.symm : j.succ = 0)) i)
  have ht : Points.tail t'=x := by
    unfold t' t; rw [exchange_positions, show Points.tail (Points.cons z (Points.tail x))=Points.tail x from rfl, point_cons_tail x]
  have hu u := exchange_use (x:=t) hs.toSymmetric ht' (⟨d,u⟩ : S.Tag) ⟨0,S.unit 0⟩ q |>.trans (S.at_unit hs (Points.rearrange_in _ ht') _ 0)
  rw [← ht,← hu, ← hu]
  exact he n q _ _ (Points.tail_in ht') _ ht'


lemma symmetric (hs : S.Hierarchy) (hp : StressLaws S J P Z) (i j : Axis) : J i j = J j i := by
  apply front_ext_padded hs.laws; intro n q ⟨d,B⟩ x hx y hy
  exact obs_symm J q i j hs hp hx B y hy


end YM.StressFlux.Reverse
