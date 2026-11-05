import YM.Further.DENSE_MIXED_KERNELS.Surface
import YM.Work.F05.Transport

/-!
# Kernel expenses at one V, patch may be restricted

Includes Bochner exchange for the input factor systems. Different contexts
for tilts in V must still call these with a legitimate kernel on those
fields; no uniform const inferred around a Healthy point from estimates
at that point. Dimensions/costs of joint moments, not per-operand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels.Surface
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    {A : ChartRatio G} {H : Port A} {μ : Measure Ω} {S : Surface H ι κ Ω} {g c : ℝ}
local notation "X" => H.front ι (H.Room κ)
local notation "Y" => H.back ι (H.Room κ)

section switch
variable {E : Type*} [NormedAddCommGroup E]
    {f : Ω × H.front ι (H.Room κ) → E} {φ : Ω × H.back ι (H.Room κ) → E}

lemma Valid.through_gate (h : S.Valid) (hg : 0<g) (hp : AEStronglyMeasurable φ (S.aboard μ g)) :
    Integrable φ (S.aboard μ g) ↔ IntegrableOn (φ ∘ S.mapDown g) (S.gateway g) (S.ante μ) := by
  unfold IntegrableOn
  rw [← h.hold g hg μ] at hp ⊢; exact integrable_map_measure hp (h.down_meas g).aemeasurable

variable [NormedSpace ℝ E]
lemma Valid.charging (h : S.Valid) (hg : 0<g) :
    Integrable φ (S.aboard μ g) ↔ Integrable (fun x => S.confirm g x • φ x) (ambient H ι κ μ) := by
  unfold aboard; rw [integrable_withDensity_iff_integrable_smul' (h.confirm_meas g).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]; simp only [ENNReal.toReal_ofReal (h.confirm_nonneg g hg _)]

lemma Valid.walk (h : S.Valid) (hg : 0<g) (hf : Integrable φ (S.aboard μ g)) :
    (∫ x,φ x ∂S.aboard μ g) = ∫ x in S.gateway g,φ (S.mapDown g x) ∂S.ante μ := by
  rw [← h.hold g hg μ] at hf ⊢; exact integral_map (h.down_meas g).aemeasurable hf.1

lemma Valid.took (h : S.Valid) (hg : 0<g) (_hf : Integrable φ (S.aboard μ g)) :
    (∫ x,φ x ∂S.aboard μ g) = ∫ x,S.confirm g x • φ x ∂ambient H ι κ μ := by
  unfold aboard; rw [integral_withDensity_eq_integral_toReal_smul (h.confirm_meas g).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]; simp only [ENNReal.toReal_ofReal (h.confirm_nonneg g hg _)]

/-- Exact formula changing protected arguments. 'vanish outside' supplied on
the real first-integral branch; never evaluating a passed piece on a different
ancestry. Use for `f` full integrand excluding final output mask; at a forced
entry either apply on its inventory test or use value zero. -/
theorem Valid.first_copy (h : S.Valid) (hg : 0<g) (he : Integrable (fun x => S.confirm g x • φ x) (ambient H ι κ μ))
    (hv : ∀ x∉S.gateway g, f x=0) (hr : ∀ x∈S.gateway g, f x=φ (S.mapDown g x)) :
    Integrable f (S.ante μ) ∧ (∫ x,f x ∂S.ante μ) = ∫ x,S.confirm g x • φ x ∂ambient H ι κ μ := by
  have hp := (h.charging hg).2 he
  have hh := (h.through_gate hg hp.1).mp hp
  have hE : (S.gateway g).indicator (φ ∘ S.mapDown g)=f := by
    funext x
    by_cases hs : x∈S.gateway g
    · rw [indicator_of_mem hs]; exact (hr x hs).symm
    rw [indicator_of_notMem hs,hv x hs]
  rw [← hE]; exact ⟨(integrable_indicator_iff (h.gate_meas g)).mpr hh,
    (integral_indicator (h.gate_meas g)).trans ((h.walk hg hp).symm.trans (h.took hg hp))⟩

end switch

variable [IsProbabilityMeasure μ]

abbrev due (H : Port A) (ι κ : Type) [Fintype ι] [Fintype κ] (d : ℕ) (c : ℝ) := expense (finrank ℝ (H.front ι (H.Room κ))) d c

def tower (S : Surface H ι κ Ω) (g : ℝ) (v : Ω × Y) := (1+‖(S.mapUp g v).2‖)

lemma Valid.tower_meas (h : S.Valid) : Measurable (S.tower g) := measurable_const.add (h.up_meas g).snd.norm

lemma Valid.budget (h : S.Valid) (k : ℕ) (hc : 0<c) (hp : ∀ i x,c*‖x‖^2 ≤ S.B i x x) :
    let K := fun i : Ω × X => (1+‖i.2‖)^k
    Integrable K (S.ante μ) ∧ (∫ x,K x ∂S.ante μ) ≤ due H ι κ k c := by
  have := add_haar H ι κ
  intro K
  let f (x : Ω×X) := S.lifted x * K x
  let u := due H ι κ k c
  have hv x : 0≤f x := mul_nonneg (h.lifted_pos x).le (by unfold K; positivity)
  have hF i : (∫ y:X,f (i,y))≤u := weighted_bill volume hc (hp i) _
  have hh : Measurable f := h.lifted_meas.mul (by unfold K; fun_prop)
  have ht : Integrable f (μ.prod volume) := by
    refine (integrable_prod_iff hh.aestronglyMeasurable).2 ⟨Eventually.of_forall fun i =>
      weighted_integrable volume hc (hp i) k, ?_⟩
    simp_rw [Real.norm_of_nonneg (hv _)]
    refine Integrable.of_bound hh.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable u
      (Eventually.of_forall fun i => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun y:X => hv (i,y))]; exact hF _
  constructor
  · unfold ante; rw [integrable_withDensity_iff_integrable_smul' h.lifted_meas.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (h.lifted_pos _).le, smul_eq_mul] using! ht
  unfold ante; rw [integral_withDensity_eq_integral_toReal_smul h.lifted_meas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (h.lifted_pos _).le, smul_eq_mul]; change (∫ x,f x ∂μ.prod volume)≤u
  rw [integral_prod f ht]
  simpa using integral_mono (ht.integral_prod_left) (μ:=μ) (g:=fun _ => u) (integrable_const u) hF

-- polynomial of the whole marginal dimension. uniform over tags even on moving support
lemma Valid.returned (h : S.Valid) (hg : 0<g) (k : ℕ) (hc : 0<c) (hp : ∀ i x,c*‖x‖^2 ≤ S.B i x x) :
    Integrable (fun x => S.tower g x ^ k) (S.aboard μ g) ∧ (∫ x,S.tower g x ^ k ∂S.aboard μ g) ≤ due H ι κ k c := by
  let f := fun i : Ω × X => (1+‖i.2‖)^k
  let φ := fun x => S.tower g x ^ k
  have h₀ x (hx : x∈S.gateway g) : φ (S.mapDown g x)= f x := by dsimp only [φ,tower]; rw [upDown g hg hx]
  have hm := h.gate_meas g
  have ha : f =ᵐ[(S.ante μ).restrict (S.gateway g)] φ ∘ S.mapDown g := by
    filter_upwards [ae_restrict_mem hm] with x hx using (h₀ x hx).symm
  have hb := h.budget (μ:=μ) k hc hp
  have he : Integrable φ (S.aboard μ g) := (h.through_gate hg
    ((Measurable.pow_const h.tower_meas k).aestronglyMeasurable)).mpr (hb.1.restrict.congr ha)
  refine ⟨he,(h.walk hg he).trans_le ?_⟩
  exact (setIntegral_congr_fun hm (fun x hx => h₀ x hx)).trans_le ((setIntegral_le_integral hb.1
    (Eventually.of_forall fun x => (show 0≤f x from (by unfold f; positivity)))).trans hb.2)

end YM.Further.DenseMixedKernels.Surface
