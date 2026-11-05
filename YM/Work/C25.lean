import YM.Bid.Grow
import YM.Spark.Limit
/-!
# Tensor density for joint Schwartz tests

Compact real-space tests suffice. Keep a fixed tensor cutoff equal to one there,
then cap the Fourier transform and use inversion; after the two cutoffs this
is a compact integral of tensor tests (the cutoff times plane waves). `Spark.records`
implements strong quadrature for such a continuous Schwartz-valued family via
its pointwise integrals. No support restrictions requested on the tensor span.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C25
open Set Filter Function MeasureTheory Boundary Probe
open scoped ContDiff Topology BigOperators InnerProductSpace
variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] in
theorem continuous_partialJet (F : P × X → ℂ) (j : ℕ) (h : ContDiff ℝ j F) :
    Continuous (fun y : P × X => iteratedFDeriv ℝ j (fun x => F (y.1, x)) y.2) := by
  let L := ContinuousLinearMap.inr ℝ P X
  have he (p : P) (x : X) : iteratedFDeriv ℝ j (fun t => F (p,t)) x =
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => L) (iteratedFDeriv ℝ j F (p,x)) := by
    let G : P × X → ℂ := fun y => F ((p,0) + y)
    have hg : ContDiff ℝ j G := h.comp (contDiff_const.add contDiff_id)
    have hG : G ∘ L = (fun t => F (p,t)) := by ext t : 1; simp [G,L]
    rw [← hG,L.iteratedFDeriv_comp_right hg x le_rfl, show G=(fun y => F ((p,0)+y)) from rfl,
      iteratedFDeriv_comp_add_left]
    simp [L]
  simp_rw [he]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => L)).continuous.comp
    (h.continuous_iteratedFDeriv le_rfl)

theorem continuous_probes (f : P → Probe X) {K : Set X} (hK : IsCompact K)
    (ht : ∀ p, tsupport (f p) ⊆ K)
    (h : ContDiff ℝ ∞ (fun y : P × X => f y.1 y.2)) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun p => Spark.ready (fun j x => ?_) (fun i j => ?_)
  · rw [← nhds_prod_eq]
    exact (continuous_partialJet _ j (h.of_le (mod_cast le_top))).tendsto (p,x)
  let g (y : P × X) := ‖y.2‖^i * ‖iteratedFDeriv ℝ j (f y.1) y.2‖
  have hg : Continuous g := ((continuous_norm.comp continuous_snd).pow _).mul
    (continuous_partialJet (fun y : P × X => f y.1 y.2) j (h.of_le (mod_cast le_top))).norm
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod hK).bddAbove_image hg.continuousOn
  refine ⟨max 0 C, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds p (zero_lt_one : 0 < (1 : ℝ))] with q hq
  refine (f q).seminorm_le_bound ℂ i j (le_max_left ..) (fun x => ?_)
  by_cases hx : x ∈ K
  · exact (hC ⟨(q,x), mk_mem_prod hq hx, rfl⟩).trans (le_max_right ..)
  have hv : ⇑(f q) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hv => hx (ht q hv))
  rw [Probe.vanish_j _ _ hv,norm_zero,mul_zero]; exact le_max_left ..

omit [FiniteDimensional ℝ X] in
theorem smooth_plane : ContDiff ℝ ∞ (fun y : X × X => plane y.1 y.2) :=
  ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.inner ℝ contDiff_snd)).mul contDiff_const).cexp

theorem compact_keeper (k : ℕ) : HasCompactSupport ⇑(keeper (X:=X) k) := by
  have hc : HasCompactSupport (tint (stall (X:=X)) : X → ℂ) := by
    rw [HasCompactSupport,tint_support]; exact isCompact_closedBall ..
  exact hc.comp_homeomorph (compress k).toHomeomorph

def cut_plane (k : ℕ) (p : X) : Probe X :=
  ((compact_keeper k).mul_right (f' := plane p)).toSchwartzMap
    (((keeper k).smooth ⊤).mul (smooth_plane.comp (contDiff_const.prodMk contDiff_id)))

theorem continuous_cut_plane (k : ℕ) : Continuous (cut_plane (X:=X) k) := by
  apply continuous_probes _ (compact_keeper k) (fun p => ?_)
  · exact (((keeper k).smooth ⊤).comp contDiff_snd).mul smooth_plane
  exact closure_mono fun x hx => left_ne_zero_of_mul hx

def box (n k : ℕ) := Joint.materialize n fun _ => keeper k

def boxedPlane (n k : ℕ) (p : Points n) := Joint.materialize n fun i => cut_plane k (p i)

theorem boxedPlane_apply {n : ℕ} (k : ℕ) (p x : Points n) : boxedPlane n k p x = box n k x * plane p x := by
  simp [boxedPlane, box, cut_plane, plane, PiLp.inner_apply, Finset.sum_mul, Complex.exp_sum, Finset.prod_mul_distrib]

theorem continuous_boxedPlane (n k : ℕ) : Continuous (boxedPlane n k) := by
  exact (Joint.jointCont n).comp (continuous_pi fun i => (continuous_cut_plane k).comp (by fun_prop))

abbrev span (n : ℕ) := Submodule.span ℂ (range (Joint.materialize n))
abbrev closedSpan (n : ℕ) := (span n).topologicalClosure

attribute [local instance] Measure.Subtype.measureSpace in
theorem cut_port_mem {n : ℕ} (w : Joint n) (hw : HasCompactSupport ⇑w) (k : ℕ) :
    sew (box n k) (port w) ∈ closedSpan n := by
  let K := tsupport w
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hw
  haveI : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ hKm.nullMeasurableSet]; exact (show IsCompact K from hw).measure_lt_top⟩
  let c := (pref (Points n))⁻¹
  let f : K → Joint n := fun p => c • (w (p : Points n) • boxedPlane n k p)
  have hc : Continuous f := ((w.continuous.smul (continuous_boxedPlane n k)).comp continuous_subtype_val).const_smul c
  have h (x : Points n) : sew (box n k) (port w) x = ∫ u : K, f u x := by
    rw [sews,port_eq]
    change _ = ∫ u : K, c • (w (u : Points n) * boxedPlane n k u x)
    rw [integral_smul,integral_subtype hKm (fun u => w u * boxedPlane n k u x),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => ?_)]
    · rw [show (fun u : Points n => w u * boxedPlane n k u x)=(fun u => box n k x * (plane u x * w u)) from
          funext (fun u => by rw [boxedPlane_apply]; ring),integral_const_mul, mul_smul_comm]
    rw [show w u=0 from image_eq_zero_of_notMem_tsupport hu,zero_mul]
  refine (span n).isClosed_topologicalClosure.mem_of_tendsto (Spark.records volume f _ h hc) ?_
  refine Eventually.of_forall fun i => (closedSpan n).sum_mem (fun j _ => ?_)
  refine (closedSpan n).smul_of_tower_mem _ ((closedSpan n).smul_of_tower_mem c ((closedSpan n).smul_mem _ ?_))
  exact (span n).le_topologicalClosure (Submodule.subset_span ⟨_, rfl⟩)

theorem compact_mem {n : ℕ} (v : Joint n) (hv : HasCompactSupport ⇑v) : v ∈ closedSpan n := by
  obtain ⟨C,hC⟩ := (show IsCompact (tsupport v) from hv).bddAbove_image continuous_norm.continuousOn
  obtain ⟨k,hk⟩ := exists_nat_gt C
  have he : sew (box n k) v = v := by
    ext x : 1
    rw [sews]
    by_cases hx : x ∈ tsupport v
    · have hh := (hC (mem_image_of_mem _ hx)).trans hk.le
      have hb i := keeper_one k (x:=x i) ((PiLp.norm_apply_le x i).trans (hh.trans (by linarith)))
      rw [show box n k x=1 by simp [box,hb], one_mul]
    rw [show v x=0 from image_eq_zero_of_notMem_tsupport hx,mul_zero]
  have ht : Tendsto (fun l => sew (box n k) (port (cap l (hat v)))) atTop (𝓝 v) := by
    convert! (((sew (box n k)).continuous.comp port.continuous).tendsto (hat v)).comp (persistent (hat v)) using 1
    rw [comp_apply,comes,he]
  exact (span n).isClosed_topologicalClosure.mem_of_tendsto ht (Eventually.of_forall
    fun l => cut_port_mem (cap l (hat v)) (finite_cap l) k)

/-- Sanity check: the empty tuple is not a missing generator. -/
theorem span_zero : span 0 = ⊤ := by
  refine top_unique fun v _ => ?_
  have he : v = v 0 • Joint.materialize 0 0 := by
    ext x : 1
    rw [Subsingleton.elim x 0]; simp
  rw [he]
  exact (span 0).smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)

theorem answer : YM.Bid.C25 := by
  intro n
  exact top_unique fun v _ => (span n).isClosed_topologicalClosure.mem_of_tendsto (persistent v)
    (Eventually.of_forall fun l => compact_mem (cap l v) (finite_cap l))
end YM.Work.C25
