import YM.Next.ROTATIONS.Moments
import YM.Next.ROTATIONS.Tensor

/-!
# Testing across axes. One negative (reflection-parity), one positive-time spectrum.
Product-test interface also for a spectator cluster with offsets and a required time gap.
-/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Row OS Word
open scoped Topology InnerProductSpace ContDiff NNReal ENNReal BigOperators ComplexConjugate

def side (b : ℂ) (t : ℝ) := if t<0 then b else 1
lemma side_m (b) : Measurable (side b) := Measurable.ite measurableSet_Iio measurable_const measurable_const
lemma side_norm (b : ℂ) (hb : ‖b‖=1) (t : ℝ) : ‖side b t‖=1 := by unfold side; split <;> simp_all

def damped (b : ℂ) (h : Form) (E t : ℝ) := side b t * (Real.exp (-|t| *E) : ℝ) * hat h t
lemma damped_m (b : ℂ) (h : Form) : Measurable (fun p : ℝ × ℝ => damped b h p.2 p.1) := by
  have hm := side_m b
  unfold damped; fun_prop

def Lap (b : ℂ) (h : Form) (E : ℝ) := ∫ t : ℝ,damped b h E t

def Runs (μ : Measure E4) (i : Axis) (b : ℂ) (h : Form) :=
  Integrable (fun p : ℝ × E4 => damped b h (p.2 i) p.1) (volume.prod μ)

def answer (i : Axis) (b : ℂ) (f : Panels) (p : E4) := Lap b (f i) (p i) * reading i f p
private def lineFeed (i : Axis) (b : ℂ) (f : Panels) (u : ℝ × Tang) (p : E4) :=
  damped b (f i) (p i) u.1 * (plane p (elsewhere i u.2).val * tests (fun i => hat (f i)) i u.2)

def toll : ℝ := (pref ℝ)^3
lemma toll_pos : 0<toll := pow_pos prepos _
lemma toll_nz : (toll:ℂ) ≠ 0 := by exact_mod_cast toll_pos.ne'

private lemma line_cast (i : Axis) (b) (f : Panels) (u : ℝ × Tang) (μ : Measure E4) :
    (∫ p,lineFeed i b f u p ∂μ) = side b u.1 * positionTest f (make i u) *
      ∫ p, propagator i |u.1| (elsewhere i u.2).val p ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  unfold lineFeed positionTest
  simp only [damped, propagator,tensor_made]; ring

private lemma both (i : Axis) (b : ℂ) (f : Panels) (μ : Measure E4) [SigmaFinite μ] (hm : Runs μ i b (f i)) :
    Integrable (answer i b f) μ ∧
      let R := fun z => ∫ p,lineFeed i b f z p ∂μ
      Integrable R (volume : Measure (ℝ × Tang)) ∧ (∫ z, R z) = ↑toll * ∫ p,answer i b f p ∂μ := by
  let H := fun i => hat (f i)
  let w := fun p : (ℝ × Tang) × E4 => lineFeed i b f p.1 p.2
  have hv : AEStronglyMeasurable w (volume.prod μ) := by
    have ha : Measurable fun x => (elsewhere i x).val := by
      unfold elsewhere; fun_prop
    have hy : Measurable fun p : (ℝ × Tang) × E4 => damped b (f i) (p.2 i) p.1.1 := by
      have hx := side_m b; unfold damped; fun_prop
    have hp : Measurable fun p : (ℝ × Tang) × E4 => plane p.2 (elsewhere i p.1.2).val := by unfold plane;fun_prop
    exact (hy.mul (hp.mul (by unfold tests;fun_prop))).aestronglyMeasurable
  have hx : Integrable w (volume.prod μ) := by
    unfold Runs at hm
    obtain ⟨he,hD⟩ := (integrable_prod_iff' hm.1).1 hm
    refine (integrable_prod_iff' hv).2 ⟨?_,?_⟩
    · filter_upwards [he] with p h
      refine h.mul_prod (μ:=volume) (ν:=volume) (g:=fun x : Tang => plane p (elsewhere i x).val * tests H i x) ?_
      exact (tests_int H i).bdd_mul (c:=1) (by
        change AEStronglyMeasurable (fun x => plane p ((make i) (0,x))) _; unfold plane;apply Measurable.aestronglyMeasurable; fun_prop)
        (ae_of_all _ fun x => le_of_eq (plane_norm ..))
    have he (p) : (∫ z : ℝ × Tang, ‖w (z,p)‖) = (∫ t : ℝ, ‖damped b (f i) (p i) t‖) * ∫ x : Tang, ‖tests H i x‖ := calc
      _ = ∫ z : ℝ × Tang, ‖damped b (f i) (p i) z.1‖ * ‖tests H i z.2‖ := integral_congr_ae (ae_of_all _ fun z => by
        dsimp only [w,lineFeed]; rw [norm_mul,norm_mul,plane_norm,one_mul])
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume) (fun t => ‖damped b (f i) (p i) t‖) (fun x => ‖tests H i x‖)
    change Integrable (fun p => ∫ z : ℝ × Tang, ‖w (z,p)‖) μ
    simp_rw [he]; exact hD.mul_const _
  have he p : (∫ z,lineFeed i b f z p)=(toll:ℂ)*answer i b f p := by
    unfold lineFeed
    rw [show (volume : Measure (ℝ × Tang))=volume.prod volume from rfl,
      integral_prod_mul (f:=fun t => damped b (f i) (p i) t) (g:=fun x : Tang => plane p (elsewhere i x).val * tests (fun i => hat (f i)) i x), tensor_wave]
    simp only [answer,Lap, Complex.real_smul, toll]; ring
  have hy : Integrable (fun p => (toll:ℂ)*answer i b f p) μ := by
    simp_rw [← he]; exact hx.integral_prod_right
  refine ⟨?_,hx.integral_prod_left,?_⟩
  · have h := hy.const_mul (toll:ℂ)⁻¹
    simp_rw [← mul_assoc (toll:ℂ)⁻¹, inv_mul_cancel₀ toll_nz, one_mul] at h
    exact h
  change (∫ z, ∫ p,lineFeed _ _ _ z p ∂μ) = _
  rw [integral_integral_swap (f:=fun z p => lineFeed i b f z p) hx]
  simp_rw [he, integral_const_mul]

variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis}

def Allows (i : Axis) (B A : Weight L) (h : Form) := ∀ t : ℝ,t≠0 → hat h t≠0 → ∃ u : ℝ≥0,
  Lowered i B u ∧ Lowered i A u ∧ ((u+u:ℝ≥0):ℝ) ≤ |t|
lemma allows_all (A B : Weight L) (i : Axis) (h) (hA : Pressed i A) (hB : Pressed i B) : Allows i A B h := by
  intro t ht hk
  let u : ℝ≥0 := ⟨|t|/2,by positivity⟩
  have hv : 0<(u:ℝ) := by change 0 < |t|/2; positivity
  exact ⟨u,presses _ _ hA _ hv,presses _ _ hB _ hv,le_of_eq (by rw [NNReal.coe_add];exact add_halves _)⟩

private lemma par (H : S.Hierarchy) (B A : Weight L) {α β} (hb : Own B i β) (ha : Own A i α)
    (t : ℝ) (x : Tang) :
    readsCluster S B A (make i (t,x))=side (signValue β * signValue α) t * readsCluster S B A (make i (|t|,x)) := by
  unfold side; split_ifs with ht
  · rw [abs_of_neg ht,mul_assoc,← reads_mirror S H.spin i B A β α hb ha (make i (-t,x)),make_mirror,neg_neg]
  rw [one_mul,abs_of_nonneg (by exact le_of_not_gt ht)]

private lemma space_ae : ∀ᵐ p : ℝ×Tang, p.1≠0 := by
  have hp : ∀ᵐ x : ℝ,x≠0 := by
    simp only [ae_iff]; simp
  exact (Measure.quasiMeasurePreserving_fst (ν:=volume)).tendsto_ae hp
private lemma sign_nz b : signValue b≠0 := by cases b <;> simp [signValue]

/-- Signed cross correlation tested by product profiles without contact assumption. -/
lemma cross_slice (V : Chamber S i) (H : S.Hierarchy) (B A : Weight L) {α β} (hb : Own B i β) (ha : Own A i α)
    (f : Panels) (hl : Allows i B A (f i))
    (hr : ∀ j, Runs (ν V (combo B A j)) i (signValue β* signValue α) (f i)) :
    let b := signValue β*signValue α
    Integrable (fun y => readsCluster S B A y * positionTest f y) ∧ fits V B A (answer i b f) ∧
    signValue β * (∫ y, readsCluster S B A y * positionTest f y)=(toll:ℂ)*cross V B A (answer i b f) := by
  intro b
  let R := fun y => readsCluster S B A y * positionTest f y
  let q := fun j z => ∫ p,lineFeed i b f z p ∂ν V (combo B A j)
  have hq j : Integrable (answer i b f) (ν V (combo B A j)) ∧ Integrable (q j) ∧ (∫ z,q j z)= (toll:ℂ)*∫ p, answer i b f p ∂ν V (combo B A j) := both i b f _ (hr j)
  let Z z := (4:ℂ)⁻¹ * ∑ j, star (Row.phase j)*q j z
  have hi : Integrable Z := (integrable_finsetSum _ (fun j _ => (hq j).2.1.const_mul _)).const_mul _
  have he : Z =ᵐ[volume] fun z : ℝ×Tang => signValue β * R (make i z) := by
    filter_upwards [space_ae] with z hz
    rcases z with ⟨t,x⟩
    have hu j : q j (t,x)=_ := line_cast i b f (t,x) (ν V (combo B A j))
    unfold Z R; simp_rw [hu]
    by_cases h : hat (f i) t=0
    · unfold positionTest; simp [tensor_made,h]
    obtain ⟨u,hU,hV,hL⟩ := hl t hz h
    rw [par H B A hb ha t,make_eq i |t| x]
    have hp := (axis_rep V H.translations B A β hb u hU hV |t| (by simpa using hL) (elsewhere i x)).2
    conv_rhs => rw [show signValue β * _ = side b t * positionTest f (make i (t,x)) *
                        (signValue β * readsCluster S B A (|t| • basis i + (elsewhere i x).val)) by dsimp only [b]; ring]
    rw [hp]; unfold Row.cross
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨?_,fun j => (hq j).1,?_⟩
  · have hz := (hi.congr he).const_mul (signValue β)⁻¹
    simp_rw [← mul_assoc (signValue β)⁻¹,inv_mul_cancel₀ (sign_nz β),one_mul] at hz
    exact ((make_pres i).integrable_comp_emb (make i).measurableEmbedding (g:=R)).mp hz
  change signValue β * (∫ y,R y) = _
  rw [← (make_pres i).integral_comp',← integral_const_mul,integral_congr_ae he.symm]
  unfold Z Row.cross; rw [integral_const_mul,integral_finsetSum _ (fun j _ => (hq j).2.1.const_mul _)]
  simp_rw [integral_const_mul,(hq _).2.2]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma auto_slice (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) {α} (ha : Own A i α)
    (f : Panels) (hl : Allows i A A (f i)) (hr : Runs (ν V A) i 1 (f i)) :
    Integrable (fun y => readsCluster S A A y * positionTest f y) ∧ Integrable (answer i 1 f) (ν V A) ∧
      signValue α * (∫ y, readsCluster S A A y * positionTest f y)=(toll:ℂ)*∫ p,answer i 1 f p ∂ν V A := by
  let R y := readsCluster S A A y * positionTest f y
  let Z z := ∫ p,lineFeed i 1 f z p ∂ν V A
  obtain ⟨hz,hq,hh⟩ := (show Integrable _ (ν V A) ∧ Integrable Z ∧ (∫ x,Z x)=_ from both i 1 f _ hr)
  have he : Z =ᵐ[volume] fun z => signValue α * R (make i z) := by
    filter_upwards [space_ae] with z hu
    obtain ⟨t,x⟩ := z
    unfold Z R; rw [line_cast]
    by_cases h : hat (f i) t=0
    · unfold positionTest; simp [tensor_made,h]
    obtain ⟨u,hU,hV,hL⟩ := hl t hu h
    dsimp only
    rw [← (axis_auto V H.translations A α ha u hU |t| (by simpa using hL) (elsewhere i x)).2]
    rw [par H A A ha ha t x,make_eq i |t| x, sign_sq]
    simp only [side,ite_self]; ring
  refine ⟨?_,hz,?_⟩
  · have hv := (hq.congr he).const_mul (signValue α)⁻¹
    simp_rw [← mul_assoc (signValue α)⁻¹,inv_mul_cancel₀ (sign_nz α),one_mul] at hv
    exact ((make_pres i).integrable_comp_emb (make i).measurableEmbedding (g:=R)).mp hv
  change signValue α * (∫ y,R y)=_
  rw [← (make_pres i).integral_comp',← integral_const_mul,integral_congr_ae he.symm]; exact hh



lemma damped_n (b : ℂ) (hb : ‖b‖=1) (f : Form) (E t) : ‖damped b f E t‖=‖hat f t‖*Real.exp (-|t| *E) := by
  simp only [damped,norm_mul,side_norm b hb,Complex.norm_real,Real.norm_eq_abs,Real.abs_exp,one_mul]; rw [mul_comm]
lemma damped_fiber (b) (h : Form) {E : ℝ} (hE : 0≤E) : Integrable (fun t => damped b h E t) (volume : Measure ℝ) := by
  refine (hat h).integrable.bdd_mul (c:=‖b‖+1) ?_ ?_
  · have hm := side_m b
    apply Measurable.aestronglyMeasurable
    fun_prop
  filter_upwards with t
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs, Real.abs_exp]
  apply (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)).trans
  · unfold side; split <;> simp
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hE

private lemma ae_time : ∀ᵐ t : ℝ, t≠0 := by simp only [ae_iff];simp

/-- Temporal zero bound. (No requirements at large t beyond Schwartz.) -/
def Hollow (h : Form) (D : ℕ) := ∃ C : ℝ,0≤C ∧ ∀ t : ℝ, t ≠ 0 → |t|≤1 → ‖hat h t‖ ≤ C*|t|^D

lemma runs_point (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (hA : Pressed i A) :
    ∃ D : ℕ, ∀ h : Form, Hollow h D → ∀ b : ℂ, ‖b‖=1 → Runs (ν V A) i b h := by
  obtain ⟨j,hj⟩ := exists_ne i
  obtain ⟨C,D,hC,h⟩ := point_moment V H A hA j hj 0
  let E (t : ℝ) (p : E4) := Real.exp (-t*p i)
  have hw t : E t = mom i j 0 t := by ext1; simp [E,mom]
  simp_rw [← hw] at h
  refine ⟨D,fun F hF b hb => ?_⟩
  obtain ⟨w,W,Hw⟩ := hF
  let μ := ν V A
  let f (p : ℝ × E4) := damped b F (p.2 i) p.1
  have hv : AEStronglyMeasurable f (volume.prod μ) := by
    have hm := side_m b
    unfold f damped; apply Measurable.aestronglyMeasurable; fun_prop
  have he (t : ℝ) (ht : t≠0) : Integrable (E |t|) μ := by
    rcases le_or_gt |t| 1 with ha|ha
    · exact (h _ (abs_pos.mpr ht) ha).1
    refine (h 1 (by norm_num) le_rfl).1.mono' ?_ ?_
    · unfold E; fun_prop
    filter_upwards [before V A] with p hp
    change ‖Real.exp _‖ ≤ Real.exp _
    rw [Real.norm_eq_abs,Real.abs_exp,Real.exp_le_exp]; gcongr
  refine (integrable_prod_iff hv).2 ⟨?_,?_⟩
  · filter_upwards [ae_time] with t ht
    have heq : Measurable fun p : E4 => damped b F (p i) t := by unfold damped;fun_prop
    exact ((he t ht).const_mul ‖hat F t‖).mono' heq.aestronglyMeasurable (ae_of_all _ fun p => (damped_n b hb F _ _).le)
  let s := Icc (-1:ℝ) 1
  have hh : Integrable (s.indicator fun _ => C*w) (volume : Measure ℝ) :=
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc
  refine (hh.add ((hat F).integrable.norm.const_mul C)).mono' hv.norm.integral_prod_right' ?_
  filter_upwards [ae_time] with t ht
  have ht' := abs_pos.mpr ht
  have heq : (∫ p, ‖f (t,p)‖ ∂μ) = ‖hat F t‖ * ∫ p,E |t| p ∂μ := by
    unfold f; simp_rw [damped_n b hb]; exact integral_const_mul ..
  change ‖∫ p, ‖f (t,p)‖ ∂μ‖ ≤ s.indicator _ t + C*‖hat F t‖
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg (f _)),heq]
  rcases le_or_gt |t| 1 with ha|ha
  · rw [indicator_of_mem (show t ∈ s from abs_le.mp ha)]
    calc
      _ ≤ w*|t|^D*(C*|t|⁻¹^D) := mul_le_mul (Hw t ht ha) (h _ ht' ha).2
        (integral_nonneg (f:=fun p => E |t| p) (fun _ => (Real.exp_pos _).le)) (by positivity)
      _ = C*w := by rw [inv_pow]; field_simp
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · rw [indicator_of_notMem (show t∉s from fun h => ha.not_ge (abs_le.mpr h)),zero_add,mul_comm C]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (le_trans (b:=∫ p,E 1 p ∂μ) _ (by simpa using (h 1 (by norm_num) le_rfl).2))
    refine integral_mono_ae (he t ht) (h 1 (by norm_num) le_rfl).1 ?_
    filter_upwards [before V A] with p hp
    apply Real.exp_le_exp.mpr
    gcongr

/-- Gap version needs no small-time moments. Equality allowed on endpoints. -/
lemma runs_gap (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (u : ℝ≥0) (ha : Lowered i A u) (b : ℂ) (hb : ‖b‖=1)
    (F : Form) (hf : ∀ t, hat F t ≠ 0 → (↑(u+u:ℝ≥0):ℝ)≤|t|) : Runs (ν V A) i b F := by
  obtain ⟨j,hj⟩ := exists_ne i
  refine ((hat F).integrable.norm.mul_prod (placed_moment V H A j hj 0 u ha)).mono' ?_ ?_
  · have hx := side_m b; unfold damped; apply Measurable.aestronglyMeasurable; fun_prop
  have H : ∀ᵐ p : ℝ × E4 ∂volume.prod (ν V A), 0≤p.2 i := Measure.quasiMeasurePreserving_snd.tendsto_ae (before V A)
  filter_upwards [H] with p hp
  simp only [damped_n b hb, mom,Nat.mul_zero,pow_zero,mul_one]
  by_cases h : hat F p.1=0
  · simp [h]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr; gcongr; exact hf _ h
end YM.Outer
