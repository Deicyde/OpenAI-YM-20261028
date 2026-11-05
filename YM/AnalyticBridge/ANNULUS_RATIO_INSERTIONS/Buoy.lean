import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Brume

/-!
# Trigger cost, and polynomial detector cost on the same actual enrollment

Additional powers for 
should cost only a polynomial in that larger dimension, not a constant
to that dimension. Make this precise even for large I and fixed scores.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism
open Function Filter ProbabilityTheory MeasureTheory Matrix Precision
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Schur
open scoped Topology BigOperators Classical ENNReal
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  {G : Gauge}

def load (z : Prices G I) (i : I) : ℝ := ‖tape z i‖^2
lemma load_nonneg (z : Prices G I) (i : I) : 0 ≤ load z i := sq_nonneg _

/-- J has DISTINCT physical positions, counting color by the implementation
basis, no assumption on reconstruction components. -/
def enrolled (J : Finset I) (z : Prices G I) := ∑ i∈J, load z i
lemma enrolled_nn (J : Finset I) (z : Prices G I) : 0 ≤ enrolled J z := Finset.sum_nonneg fun i _=>load_nonneg _ i

@[fun_prop] lemma load_measurable (i : I) : Measurable (fun z : Prices G I=>load z i) := Measurable.pow_const (Measurable.norm ((measurable_pi_apply _).comp tape.measurable)) _
@[fun_prop] lemma enrolled_measurable (J : Finset I) : Measurable (α:=Prices G I) (enrolled J) := by unfold enrolled; fun_prop

def levy (J : Finset I) (t : ℝ) (z : Prices G I) : ℝ := Real.exp (t*enrolled J z)
@[fun_prop] lemma levy_measurable (J : Finset I) (t : ℝ) : Measurable (α:=Prices G I) (levy J t) := by unfold levy; fun_prop
lemma levy_pos (J : Finset I) (t : ℝ) (z : Prices G I) : 0 < levy J t z := Real.exp_pos _

def tuck (G : Gauge) := (2:ℝ)^Fintype.card G.ColorIndex
lemma tuck_one (G : Gauge) : 1 ≤ tuck G := one_le_pow₀ (by norm_num)
lemma tuck_pos (G : Gauge) : 0 < tuck G := lt_of_lt_of_le zero_lt_one (tuck_one _)

private lemma slips (J : Finset I) (z : Prices G I) : enrolled J z =
    let u := pocket (fun i : J × G.ColorIndex => ((i.1:I),i.2)) z
    u ⬝ᵥ u := by
  dsimp only
  rw [price_square (ι:=J)]; unfold enrolled load
  rw [Finset.sum_subtype J (show ∀ i, i∈J ↔ i∈J from fun _=>Iff.rfl)]
  refine Finset.sum_congr rfl fun j _=>?_
  rfl

/-- including the L¹ assertion. -/
theorem held_mgf {C : Gaussian.Table (I × G.ColorIndex)} (hC : C.PosSemidef) {η L t : ℝ} (h : Numeric C η L)
    (hL : 0<L) (ht : 0≤t) (hv : t≤leisure L) (J : Finset I) :
    Integrable (levy J t) (cloud C) ∧ (∫ z,levy J t z ∂cloud C) ≤ (tuck G)^J.card := by
  let e : J × G.ColorIndex → I × G.ColorIndex := fun i => (i.1,i.2)
  have he : Function.Injective e := fun i j h' => Prod.ext (Subtype.ext (congr_arg Prod.fst h')) (congr_arg (fun x : I × G.ColorIndex => x.2) h')
  have ha := pockets hL hC h ht hv e he
  have hk (z : Prices G I) : ((gleam t) ∘ pocket e) z = levy J t z := by rw [Function.comp_apply, levy, gleam, slips J z]
  simp only [Fintype.card_prod,Fintype.card_coe,pow_mul,funext hk] at ha
  rw [show tuck G^J.card=(2:ℝ)^(Fintype.card (↥J) * Fintype.card G.ColorIndex) from by
    unfold tuck; rw [Nat.mul_comm,pow_mul,Fintype.card_coe],pow_mul,Fintype.card_coe]; exact ha

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {ρ : ℝ}
  (J : Finset I)

def triggered (ρ : ℝ) : Set (Prices G I) := {z|∀ i∈J,ρ≤‖tape z i‖}
lemma triggered_measurable : MeasurableSet (triggered (G:=G) J ρ) := by
  have h (i : I) : MeasurableSet {z: Prices G I| ρ ≤ ‖tape z i‖} := measurableSet_le measurable_const (((measurable_pi_apply _).comp tape.measurable).norm)
  simp_rw [triggered,Set.setOf_forall]; exact MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun _=>h i))
lemma lit_heat {z : Prices G I} (h : z ∈ triggered J ρ) (hρ : 0≤ρ) : J.card*ρ^2 ≤ enrolled J z := by
  simpa [enrolled] using Finset.sum_le_sum (s:=J) (f:=fun _=>ρ^2) (g:=load z) (fun i hi=>pow_le_pow_left₀ hρ (h i hi) 2)

def buzzer (ρ : ℝ) (z : Prices G I) := (triggered J ρ).indicator (fun _=> (1:ℝ)) z

@[fun_prop] lemma measurable_buzzer (ρ : ℝ) : Measurable (α:=Prices G I) (buzzer J ρ) := measurable_const.indicator (triggered_measurable _)
lemma buzzing {t : ℝ} (ht : 0≤t) (hρ : 0≤ρ) (z : Prices G I) : buzzer J ρ z ≤ Real.exp (-t*J.card*ρ^2) * levy J t z := by
  unfold buzzer
  by_cases h : z ∈ triggered J ρ
  · rw [Set.indicator_of_mem h,levy,← Real.exp_add]; exact Real.one_le_exp (by
      linarith only [mul_le_mul_of_nonneg_left (lit_heat J h hρ) ht])
  rw [Set.indicator_of_notMem h]; exact mul_nonneg (Real.exp_pos _).le (levy_pos ..).le



/-- Reserve does not require additional entropy spending. -/
private lemma cash_pow (t : ℝ) (ht : 0<t) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ i : ℝ, 0 ≤ i → i^k ≤ C*Real.exp (t*i) := by
  let a := t/(1+k)
  have ha : 0<a := div_pos ht (by positivity)
  refine ⟨a⁻¹^k,pow_pos (inv_pos.mpr ha) _,fun i hi=>?_⟩
  have h : i ≤ a⁻¹*Real.exp (a*i) := by
    rw [inv_mul_eq_div,le_div_iff₀ ha]
    linarith only [Real.add_one_le_exp (a*i)]
  apply (pow_le_pow_left₀ hi h _).trans
  rw [mul_pow,← Real.exp_nat_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (inv_nonneg.mpr ha.le) _)
  have he : (k : ℝ)*a ≤ t := by
    unfold a; field_simp; linarith
  nlinarith only [mul_le_mul_of_nonneg_right he hi]

def gaugeMark (z : Vec V) := z ⬝ᵥ z
@[fun_prop] lemma measurable_gaugeMark : Measurable (gaugeMark (V:=V)) := by unfold gaugeMark dotProduct; fun_prop

/-- Uniform in number n of indicated real coordinates, with explicit
polynomial in n. Equivalent score `(1+|z|²)^k` vs `(1+|z|)^{2k}` up
to fixed-k factor, counting norm on all I. -/
theorem many (L : ℝ) (hL : 0<L) (k : ℕ) : ∃ D : ℝ, 0<D ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] {C : Gaussian.Table V} {η}, C.PosSemidef → Numeric C η L →
    let n : ℝ := Fintype.card V
    let u (z : Vec V) := (1+gaugeMark z)^k
    Integrable u (cloud C) ∧ (∫ z, u z ∂cloud C) ≤ D*(1+n)^(k+1) := by
  let t := leisure L
  obtain ⟨D,hD,H⟩ := cash_pow t (leisure_pos hL) k
  refine ⟨1+2*D,by positivity,?_⟩
  intro V hV _ C η hC h n u
  have hn : 0≤n := by unfold n; exact Nat.cast_nonneg _
  let s (x : V) (i : Vec V) := Real.exp (t*(i x)^2)
  have hi (x : V) : Integrable (s x) (cloud C) ∧ (∫ z,s x z ∂cloud C) ≤ 2 := by
    obtain ⟨he,hf⟩ := pockets hL hC h (leisure_pos hL).le (show t≤_ from le_rfl) (fun _ : Unit=> x) (fun _ _ _=>Subsingleton.elim ..)
    simp only [Fintype.card_unique,pow_one] at hf
    have hh (z : Vec V) : s x z = (gleam t ∘ pocket (fun _ : Unit=> x)) z := by simp [s,pocket,gleam,dotProduct,sq]
    rw [funext hh]; exact ⟨he,hf⟩
  let v (i: Vec V) := (1+n)^k*(1+D*∑ x, s x i)
  have hp (x : V) (z : Vec V) : 0 ≤ s x z := (Real.exp_pos _).le
  have h0 := integrable_finsetSum (μ:=cloud C) Finset.univ fun i _=>(hi i).1
  have hv : Integrable v (cloud C) := ((integrable_const (1:ℝ)).add (h0.const_mul D)).const_mul ((1+n)^k)
  have hh (z : Vec V) : ‖u z‖ ≤ v z := by
    let f x := z x ^ 2
    have h0 : gaugeMark z = ∑ x,f x := by simp [gaugeMark,dotProduct,f,sq]
    rw [Real.norm_of_nonneg (pow_nonneg (by linarith only [show 0≤gaugeMark z from dot_nonneg z] : 0≤1+gaugeMark z) _)]
    change (1+gaugeMark z)^k ≤ _
    by_cases hI : Nonempty V
    · obtain ⟨i,-,hh⟩ := Finset.exists_max_image (s:=(Finset.univ : Finset V)) f Finset.univ_nonempty
      have he : gaugeMark z ≤ n*f i := by
        rw [h0]
        simpa [n] using (Finset.sum_le_sum (s:=Finset.univ) (f:=f) (g:=fun _=>f i) (fun j hj=>hh j hj))
      by_cases hl : f i ≤ 1
      · apply (pow_le_pow_left₀ (by have := dot_nonneg z; unfold gaugeMark; positivity) (add_le_add_right (le_trans he (show n*f i ≤ n by nlinarith)) 1) k).trans
        exact le_mul_of_one_le_right (by positivity) (by have h0 := Finset.sum_nonneg (s:=Finset.univ) (f:=fun x=>s x z) fun x _=>hp x z; nlinarith)
      have hx : 1 ≤ f i := le_of_not_ge hl
      apply (pow_le_pow_left₀ (by have := dot_nonneg z; unfold gaugeMark; positivity) (show 1 + gaugeMark z ≤ (1+n)*f i by linarith) k).trans
      rw [mul_pow]; unfold v; gcongr
      exact le_trans (H _ (sq_nonneg _)) (le_trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (s:=Finset.univ) (f:=fun x=>s x z) (fun j _=>hp j z) (Finset.mem_univ i)) hD.le) (by linarith))
    haveI : IsEmpty V := not_nonempty_iff.mp hI
    simp [h0,v,n]
  have hu : Integrable u (cloud C) := hv.mono' (by unfold u; fun_prop) (ae_of_all _ hh)
  refine ⟨hu,(integral_mono hu hv fun i => (le_abs_self _).trans (hh i)).trans ?_⟩
  have he : (∑ x,∫ z,s x z ∂cloud C) ≤ n*2 := by
    simpa [n] using Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=> (2:ℝ)) fun x _=>(hi x).2
  unfold v
  rw [integral_const_mul,integral_add (integrable_const _) (h0.const_mul D),integral_const,probReal_univ,one_smul,integral_const_mul,
    integral_finsetSum _ fun i _=>(hi i).1,pow_succ]
  rw [mul_left_comm (1+2*D)] -- check
  gcongr
  nlinarith
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism
