import YM.TraceExtension.Fock.Data

/-! Recover equal-time data of v-v⁺. Use approximate identity, with time
derivatives harmless at fixed order because of the one-slot massless shell. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff
variable {m n d : ℕ}
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
   [MeasurableSpace V] [BorelSpace V]
lemma plus_minus (f : Probe V) (p) : Probe.hat f p=testPlus f (-p) := by rw [Probe.hat_eq,testPlus_apply]
lemma atom_negative (p : V) : Tendsto (fun k => Probe.hat (atom V k) p) atTop (𝓝 1) := by simp_rw [plus_minus]; exact atom_delta V _
end

def timeJet : ℕ → Probe ℝ→Probe ℝ
 | 0,f=>f
 | n+1,f=>SchwartzMap.derivCLM ℂ ℂ (timeJet n f)
lemma time_support (n) (f : Probe ℝ) : tsupport (timeJet n f) ⊆ tsupport f := by
    induction n with
    | zero=> exact subset_rfl
    | succ n ih=> exact tsupport_deriv_subset.trans ih
private lemma time_derive (f : Probe ℝ) (p : ℝ) :
    testPlus (SchwartzMap.derivCLM ℂ ℂ f) p = (-I) * (p:ℂ) * testPlus f p := by
    let u (x : ℝ) := Probe.plane x p; let c := I*(p:ℂ)
    have hd (x : ℝ) : HasDerivAt u (c*u x) x := by
        have hv : HasDerivAt Complex.ofReal (1:ℂ) x := (ofRealCLM.hasFDerivAt (x:=x)).hasDerivAt
        convert! ((hv.const_mul c).cexp) using 1
        · funext x; simp [u,Probe.plane,c]; ring_nf
        simp [u,Probe.plane,c]; ring_nf
    have he (g : Probe ℝ) : Integrable (fun x => u x*g x) volume := g.integrable.bdd_mul (show Continuous u from by unfold u Probe.plane; fun_prop).aestronglyMeasurable
       (ae_of_all _ fun i => (show ‖u i‖=1 from Probe.plane_norm ..).le)
    rw [testPlus_apply,testPlus_apply]
    change (∫ x,u x * deriv (⇑f) x) = _
    rw [integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _=> hd x) (fun x _=>(f.differentiableAt).hasDerivAt)
       (he (SchwartzMap.derivCLM ℂ ℂ f)) ?_ (he f)]
    · simp_rw [mul_assoc c]; rw [integral_const_mul]; unfold u c; ring
    convert (he f).const_mul c using 1
    ext x; dsimp; ring
lemma jet_fourier (n) (f : Probe ℝ) (p) :
    testPlus (timeJet n f) p = (-I*(p:ℂ))^n * testPlus f p := by
    induction n with
    | zero=> simp [timeJet]
    | succ n ih=> rw [timeJet,time_derive,ih,pow_succ]; ring
lemma jet_minus (n) (f : Probe ℝ) (p) :
    Probe.hat (timeJet n f) p=(I*(p:ℂ))^n * Probe.hat f p := by simp only [plus_minus,jet_fourier,ofReal_neg,neg_mul_neg]

def separate (f : Probe Space3) (g : Probe ℝ) := Probe.along divide (Probe.combine f g)
lemma separate_eval (f : Probe Space3) (g : Probe ℝ) (x) : separate f g x=f (spatial x)*g (time x) := rfl
lemma plane_two (x p : E4) : Probe.plane x p= Probe.plane (spatial x) (spatial p)*Probe.plane (time x) (time p) := by
    unfold Probe.plane; rw [Mink.pairing, ← Complex.exp_add, ofReal_add, add_mul]; congr 3; simp [mul_comm]
lemma separate_fourier (f : Probe Space3) (g : Probe ℝ) (x) :
    testPlus (separate f g) x=testPlus f (spatial x)*testPlus g (time x) := by
    rw [testPlus_apply,testPlus_apply,testPlus_apply,← integral_prod_mul]
    let K := fun p : Space3 × ℝ => (Probe.plane p.1 (spatial x)*f p.1)*(Probe.plane p.2 (time x)*g p.2)
    refine Eq.trans ?_ (volume_divide.integral_comp divide.toHomeomorph.toMeasurableEquiv.measurableEmbedding K)
    congr! 1; ext p; rw [plane_two,separate_eval]; simp only [K,divide_at]; ring
lemma separate_minus (f : Probe Space3) (g : Probe ℝ) (x) : Probe.hat (separate f g) x=Probe.hat f (spatial x)*Probe.hat g (time x) := by simp [plus_minus,separate_fourier]
lemma separate_away (b : ℕ) (f : Probe Space3) (hp : HasCompactSupport ⇑f) (hf : 0 ∉ tsupport f) :
    ∀ᶠ k : ℝ in atTop, Remote (separate f (timeJet b (atom ℝ k))) := by
    obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp ((isClosed_tsupport f).isOpen_compl.mem_nhds hf)
    filter_upwards [atom_small ℝ hr] with k hk; let g := timeJet b (atom ℝ k)
    have hg := time_support b (atom ℝ k); have hG : HasCompactSupport g := hk.2.of_isClosed_subset (isClosed_tsupport _) hg
    refine ⟨(Probe.compact_combine hp hG).comp_homeomorph divide.toHomeomorph,?_⟩
    have hs : tsupport (separate f g) ⊆ divide ⁻¹' (tsupport (⇑f) ×ˢ tsupport (⇑g)) := by
        apply closure_minimal _ (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage divide.continuous)
        intro x hx
        change f (spatial x)*g (time x) ≠ 0 at hx
        exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx),subset_tsupport _ (right_ne_zero_of_mul hx)⟩
    intro x hx; obtain ⟨ha,hJ⟩ := hs hx
    apply (Mink.lateral _).2; apply lt_of_lt_of_le (b:=r)
    · simpa using (show time x∈ball (0:ℝ) r from hk.1 (hg hJ))
    by_contra! hb; exact he (mem_ball.mpr (by simpa using hb)) ha

private lemma substituteTest (i : Fin n) (g : Fin n→ Probe E4) (f : Probe E4) (p : Mom n) :
    frontList (update g i f) p = front f (p i)*slot g i p := by
    unfold frontList slot; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
    congr 1; exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
private lemma update_comp {V W : Type*} (f : V → W) (g : Fin n→V) (i x) : f ∘ update g i x = update (f ∘ g) i (f x) := by
    ext j; by_cases h:j=i <;> simp [h]

/-- Use equality only off the union of closed light cones *by leg*. Obtain
point-supported equal-time value and time derivatives. -/
lemma cauchy_point (q : Wave n) (hq : tempered q d) (h : ∀ g, (∀ i, Remote (g i)) → paired_at q g=adjoint_at q g) (i : Fin n) (g : Fin n→ Probe E4)
    (he : ∀ j, Remote (g j)) (b : ℕ) (f : Probe Space3) (hw : HasCompactSupport ⇑f) (hs : 0∉tsupport f) : data b q g i f=0 := by
    let w := atom ℝ; let G k := update g i (separate f (timeJet b (w k)))
    have hm k p : frontList (Probe.hat ∘ G k) p=I^b * Probe.hat (w k) ‖p i‖ * sink b (Probe.hat ∘ g) i (Probe.hat f) p := by
        unfold G; rw [update_comp,substituteTest]; unfold front sink; rw [separate_minus,momentum_space,momentum_energy,jet_minus]; ring
    have hp k p : frontList (testPlus ∘ G k) p=(-I)^b * testPlus (w k) ‖p i‖ * sink b (testPlus ∘ g) i (testPlus f) p := by
        unfold G; rw [update_comp,substituteTest]; unfold front sink; rw [separate_fourier,momentum_space,momentum_energy,jet_fourier]; ring
    have ht k : paired_at q (G k) = I^b * ∫ p : Mom n, Probe.hat (w k) ‖p i‖ * (q p*sink b (Probe.hat ∘ g) i (Probe.hat f) p) ∂photons n := by
        unfold paired_at; rw [← integral_const_mul]; congr! 1; ext p; rw [hm]; ring
    have hu k : adjoint_at q (G k) = (-I)^b * ∫ p : Mom n, testPlus (w k) ‖p i‖ * (star (q p)*sink b (testPlus ∘ g) i (testPlus f) p) ∂photons n := by
        unfold adjoint_at; rw [← integral_const_mul]; congr! 1; ext p; rw [hp]; ring
    have ht : Tendsto (fun k => paired_at q (G k)) atTop (𝓝 (I^b * dataM b q g i f)) := by
      simp_rw [ht, dataM]; apply Tendsto.const_mul; let u (p:Mom n) := q p*sink b (Probe.hat ∘ g) i (Probe.hat f) p
      have hu : Integrable u (photons n) := (sink_int b q hq ..).1
      apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖u p‖) (Eventually.of_forall fun k => ?_) _ hu.norm
      · filter_upwards with p; simpa only [one_mul] using (atom_negative ‖p i‖).mul_const (u p)
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with k hk; filter_upwards with p
        rw [norm_mul, plus_minus]; exact mul_le_of_le_one_left (norm_nonneg _) (atom_bound ℝ k hk _)
      exact ((show Continuous (fun p : Mom n => Probe.hat (w k) ‖p i‖) from by fun_prop).aestronglyMeasurable.mul hu.1)
    have hu : Tendsto (fun k => adjoint_at q (G k)) atTop (𝓝 ((-I)^b * dataP b q g i f)) := by
      simp_rw [hu,dataP]; apply Tendsto.const_mul; let u (p:Mom n) := star (q p)*sink b (testPlus ∘ g) i (testPlus f) p
      have hu : Integrable u (photons n) := (sink_int b q hq ..).2
      apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖u p‖) (Eventually.of_forall fun k => ?_) _ hu.norm
      · filter_upwards with p; simpa only [one_mul] using (atom_delta ℝ ‖p i‖).mul_const (u p)
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with k hk; filter_upwards with p
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (atom_bound ℝ k hk _)
      exact ((show Continuous (fun p : Mom n => testPlus (w k) ‖p i‖) from by fun_prop).aestronglyMeasurable.mul hu.1)
    have hz := tendsto_nhds_unique_of_eventuallyEq ht hu (Eventually.mono (separate_away b f hw hs) (fun k hk => h _ (fun j => by unfold G; by_cases hp:j=i <;> simp [hp,hk,he,w])))
    unfold data; apply sub_eq_zero.mpr; apply mul_left_cancel₀ (pow_ne_zero b I_ne_zero)
    rw [hz, ← mul_assoc, ← mul_pow,mul_neg_one]
end YM.TraceExtension.Photons
