import YM.Bid.Tar

/-!
# Matching tube emission with ordered complex times

Absolute spacetime tests. Use `during` at *negatively lifted compact*
frequency tests (not claiming a bare exponential acts on all Schwartz).
`cones` allows the blanket damping to replace that compact-test operation,
and then both Fourier-side answers are continuous on Schwartz space.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C15
open Function Set Filter MeasureTheory Distribution Boundary Boundary.Surface Probe
open scoped Topology InnerProductSpace ContDiff

variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ}

theorem east_broad {y : Heights n} (hy : y ∈ east n) : ∃ k ∈ Ioc (0:ℝ) 1, broad y k := by
  have he : ∀ᶠ k in 𝓝 (0:ℝ), ∀ i j : Fin n, i < j → k ≤ y j-y i := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases h : i < j
    · exact (gt_mem_nhds (sub_pos.mpr (hy h))).mono fun _ hx _ => hx.le
    exact Eventually.of_forall fun _ hp => (h hp).elim
  apply Filter.Eventually.exists (f := 𝓝[>] (0:ℝ))
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds,
    he.filter_mono nhdsWithin_le_nhds] with k hk hk' hb using ⟨⟨hk,hk'.le⟩,hb⟩

theorem restricted_bounded {F : Waves S} (p : F.Breathes) (v : Fin n → S.Union)
    {y : Heights n} (hy : y ∈ east n) : ∃ K : ℝ, ∀ x, ‖F.restricted v y x‖ ≤ K := by
  obtain ⟨m,C,_,h⟩ := p n v
  obtain ⟨k,hk,hb⟩ := east_broad hy
  exact ⟨_,h y k hk hb⟩

/-- At fixed ordered heights the tested wave really defines a tempered distribution. -/
theorem psi_tempered {F : Waves S} (p : F.Breathes) (b : F.Bounds) (v : Fin n → S.Union)
    {y : Heights n} (hy : y ∈ east n) : ∃ u : Distn (Points n), ∀ f : Joint n, u f = F.psi v y f := by
  obtain ⟨K,hK⟩ := restricted_bounded p v hy
  let u : Joint n →ₗ[ℂ] ℂ :=
    { toFun := F.psi v y
      map_add' := by
        intro f g
        unfold Waves.psi
        rw [← integral_add (b n v y hy f) (b n v y hy g)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f
        change (∫ x, F.restricted v y x * (c • f) x) = c * F.psi v y f
        rw [Waves.psi, ← integral_const_mul]; apply integral_congr_ae
        filter_upwards with x; simp; ring }
  have hu : Continuous u := sways (fun f => K * weight f)
    (weight_cont.const_mul K) (by simp) (fun f => compromise f _ _ hK)
  exact ⟨⟨u,hu⟩,fun _ => rfl⟩

/-- On compact tests a blanket with the actual attenuated multiplier may be
removed at frequencies carried by the cone. -/
theorem blanketed_eq {B : Blanket n} (h : B.Modified) (u : Distn (Points n))
    (hs : dsupport u ⊆ coneM n) (y : Points n) (hy : y ∈ shores n) (f : Joint n)
    (hf : HasCompactSupport ⇑f) : u (B.diffuser y f) = u (lifts (-y) f hf) := by
  apply sub_eq_zero.mp; rw [← map_sub]
  apply (Distn.due u _ (closedM _)).mp hs
  intro p ht hp
  have he : Disjoint (Metric.ball p 1) (support (B.diffuser y f - lifts (-y) f hf)) := by
    apply Set.disjoint_left.mpr
    intro x hx hv
    apply hv
    have hB : B.cut x=1 := B.immediate x ⟨p,hp,hx⟩
    change B.diffuser y f x-lifts (-y) f hf x=0
    simp [Blanket.diffuser, SchwartzMap.smulLeftCLM_apply_apply (h.actual _ hy),
      Blanket.attenuate, hB]
  exact Set.disjoint_left.mp (he.closure_right Metric.isOpen_ball) (Metric.mem_ball_self zero_lt_one) ht

theorem lifts_cancel (p : Points n) (f : Joint n) (hf : HasCompactSupport ⇑f) :
    lifts p (lifts (-p) f hf) (remains (-p) f hf) = f := by
  ext1 x
  simp only [rises, inner_neg_left, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
  simp

/-- Fourier transform of the strict restriction, then back to absolute position variables. -/
theorem partialD_psi {W : Surface S} {B : Blanket n} {F : Waves S} (hb : B.Modified)
    (hw : Bid.cones W) (p : F.Breathes) (b : F.Bounds) (d : F.during W)
    (v : Fin n → S.Union) {y : Heights n} (hy : y ∈ east n) (f : Joint n) :
    B.partialD (W.W n v) (dawn y) f = F.psi v y f := by
  obtain ⟨u,hu⟩ := psi_tempered p b v hy
  let w := (Distn.fourier (W.W n v)).comp (B.diffuser (dawn y))
  have he (g : Joint n) (hg : HasCompactSupport ⇑g) : w g = Distn.fourier u g := by
    change Distn.fourier (W.W n v) (B.diffuser (dawn y) g) = u (hat g)
    rw [blanketed_eq hb _ (hw n v) _ (warmer n (etched hy)) _ hg,
      d n v y hy _ (remains _ g hg), lifts_cancel, hu]
  have hEq : w = Distn.fourier u := by
    ext1 g
    exact tendsto_nhds_unique_of_eventuallyEq ((w.continuous.tendsto g).comp (persistent g))
      (((Distn.fourier u).continuous.tendsto g).comp (persistent g))
      (Eventually.of_forall fun k => he (cap k g) (finite_cap k))
  change Distn.inverse w f = _
  rw [hEq, Distn.one, hu]

theorem restricted_continuous {F : Waves S} (r : F.Region T) (v : Fin n → S.Union)
    {y : Heights n} (hy : y ∈ east n) : Continuous (F.restricted v y) := by
  have hc : Continuous (fun x : Points n => (shift x y, Boundary.trace x)) := by
    unfold shift Boundary.trace; fun_prop
  apply continuousOn_univ.mp ((r.together n v).comp hc.continuousOn (fun x _ => ?_))
  refine ⟨?_,mem_univ _⟩
  change (fun i => (shift x y i).im) ∈ east n
  simpa [shift] using hy

theorem eq_of_tests (g h : Points n → ℂ) (pg : Continuous g) (ph : Continuous h)
    (ht : ∀ f : Joint n, (∫ x, g x * f x) = ∫ x, h x * f x) : g = h := by
  refine Measure.eq_of_ae_eq (μ := volume) (ae_eq_of_integral_contDiff_smul_eq
    pg.locallyIntegrable ph.locallyIntegrable ?_) pg ph
  intro f hf hf'
  let t : Joint n := (hf'.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hf)
  simpa only [Complex.real_smul, show (t : Points n → ℂ) = (fun x => (f x : ℂ)) from rfl,
    mul_comm (g _) _,mul_comm (h _) _] using ht t

theorem answer : YM.Bid.C15 := by
  intro G L S T W D hD hw Y hY i F r p b d
  refine ⟨hY,i.builds,i.leaned,fun n v x y hy => ?_⟩
  have hc : Continuous (fun x : Points n => glow x (dawn y)) :=
    (home n).comp (continuous_id.prodMk continuous_const)
  have ht (x : Points n) : glow x (dawn y) ∈ tube n := by simpa [tube] using etched hy
  have hg : Continuous (fun x => Y.emit v (glow x (dawn y))) :=
    continuousOn_univ.mp ((hY n v).continuousOn.comp hc.continuousOn (fun x _ => ht x))
  apply congr_fun (eq_of_tests _ _ hg (restricted_continuous r v hy) _) x
  intro f
  rw [← i.builds n v _ (etched hy) f]
  exact partialD_psi (hD n) hw p b d v hy f

end YM.Work.C15
