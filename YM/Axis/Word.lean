import YM.Heat.Duration

/-!
# Undamped positive measures on all COMBINATIONS

Upper placement arbitrary t> enough; equality of reads. Differential approximations
need bounds in all transverse directions; not yet. Any x-axis collision across
clusters forbidden but internal distinct. Define attempts for all large times,
not arbitrary extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Row
open Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe OS Word
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {G : Gauge} (L : Register G) (a : Axis) {S : Table L}

abbrev Core := {w : L.Word // distinct w}
abbrev Weight := Core L →₀ ℂ
variable {L}

def Lowered (A : Weight L) (t : ℝ) := ∀ i∈A.support, ∀ x∈ i.val, 0 < x.1 a + t

def Pressed (A : Weight L) := ∀ i∈A.support, ∀ x∈ i.val, x.1 a=0

lemma presses (A : Weight L) (h : Pressed a A) (t : ℝ) (ht : 0<t) : Lowered a A t := by
  intro i hi x hx; rw [h i hi x hx,zero_add]; exact ht

lemma descends (A : Weight L) : ∀ᶠ i : ℝ≥0 in atTop, Lowered a A (i:ℝ) := by
  classical
  have he (v : ℝ) : ∀ᶠ t : ℝ≥0 in atTop, 0 < v+(t:ℝ) := by
    apply (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0))) |>.eventually
      (eventually_gt_atTop (-v))).mono
    intro t ht; change -v < (t:ℝ) at ht; linarith
  refine (eventually_all_finset A.support).mpr fun i hi => ?_
  simpa using (eventually_all_finset i.val.toFinset).mpr (fun x _ => he (x.1 a))

variable {a} (V : Chamber S a)

def bud (w : Core L) (t : ℝ) : V.GNS.H := open scoped Classical in
  if h : Positive (carry w.val (t • basis a)) a then V.GNS.plant ⟨_,h⟩ else 0

def root (A : Weight L) (t : ℝ) := A.sum (fun w x => x • bud V w t)
lemma enough (A : Weight L) (t u : ℝ≥0) (h : Lowered a A t) :
    V.flow.E u (root V A t) = root V A (t+u:ℝ≥0) := by
  classical
  unfold root; rw [map_finsuppSum]; apply Finsupp.sum_congr
  intro x hx
  rw [map_smul]; congr 1
  let w := carry x.val ((t:ℝ) • basis a)
  have hw : Positive w a := by
    refine ⟨still x.property _,fun i hi => ?_⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; have he := h x hx j hj; simpa using he
  let r : Future L a := ⟨w,hw⟩
  unfold bud; split_ifs with H ht ht; all_goals try contradiction
  · rw [← V.atBirth]; congr 1
    apply Subtype.ext; simp [travel,add_smul]
  exfalso; apply ht
  rw [show carry x.val (((t+u:ℝ≥0):ℝ) • basis a)= (travel r u).val by simp [r,travel,w,add_smul]]
  exact (travel r u).property

def weighted (A : Weight L) (t : ℝ≥0) : Measure E4 := Semigroup.transform a (-((t+t:ℝ≥0):ℝ))
  (V.flow.ℚmeasure.diagonal (root V A t))

lemma by_right (A : Weight L) (t k : ℝ≥0) (hk : Lowered a A t) : weighted V A (t+k) = weighted V A t := by
  rw [weighted, ← enough V A t k hk,V.flow.damp, Semigroup.growth]
  unfold weighted; congr 1; push_cast;ring

abbrev Kstage (A : Weight L) : ℝ≥0 := (descends a A).exists.choose

def ν (A : Weight L) := weighted V A (Kstage (a := a) A)

lemma issued (A : Weight L) (t : ℝ≥0) (h : Lowered a A t) : ν V A = weighted V A t := by
  let p : ℝ≥0 := Kstage (a := a) A
  unfold ν
  have hh : Lowered a A p := (descends a A).exists.choose_spec
  rw [← by_right V A p t hh,← by_right V A t p h, add_comm]
lemma band (A : Weight L) (t : ℝ≥0) (h : Lowered a A t) : Semigroup.transform a ((t+t:ℝ≥0):ℝ) (ν V A) =
    V.flow.ℚmeasure.diagonal (root V A t) := by
  rw [issued V A t h,weighted,Semigroup.growth]; simp [Semigroup.stays_put]

instance sigma (A : Weight L) : SigmaFinite (ν V A) := SigmaFinite.withDensity_of_ne_top
  (ae_of_all _ fun _ => ENNReal.coe_ne_top)
lemma before (A : Weight L) : ∀ᵐ i ∂ν V A, 0 ≤ i a := (V.flow.bright _).filter_mono
  (MeasureTheory.Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous ..))

def terminal (A : Weight L) (N : ℝ) := (ν V A) {p | p a ≤ N}

theorem within (A : Weight L) (N : ℝ) : terminal V A N < ⊤ := by
  let t : ℝ≥0 := Kstage (a := a) A
  let μ := V.flow.ℚmeasure.diagonal (root V A t)
  let D : Set E4 := {p | p a ≤ N}
  have hd : MeasurableSet D := (isClosed_le (show Continuous (fun p : E4 => p a) by fun_prop) continuous_const).measurableSet
  unfold terminal ν weighted Semigroup.transform
  rw [withDensity_apply _ hd]
  let r : ℝ≥0 := ⟨Real.exp (((t+t:ℝ≥0):ℝ)*N), Real.exp_nonneg _⟩
  apply lt_of_le_of_lt (b := ∫⁻ _ in D, (r:ℝ≥0∞) ∂μ)
  · apply lintegral_mono_ae; filter_upwards [ae_restrict_mem hd] with i hi
    rw [ENNReal.coe_le_coe];
    change Real.exp (_ * i a) ≤ Real.exp _
    rw [neg_neg]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (by positivity))
  haveI : IsFiniteMeasure μ := Spectral.PVM.finite ..
  simp
  finiteness
end YM.Row
