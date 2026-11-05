import YM.Fields.System
import YM.Heat.Lift
import YM.Phase.Mixture
import YM.Shift.Swap



/-!
# Uniqueness and forwardum for ANY subword covariant domain

From a specified isometric intertwiner for translations into SAME or selected
chamber. No gap. Use M.test rolls on negative directions; no cones assumed
on OS. Projection identity proved at Hilbert level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Set Filter MeasureTheory Measure OS Mink Probe Spectral Complex
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L} {X : Hilbert}

namespace Action
variable (P : Action X)
def spaceKeep (s : Poincare) : X→ₗᵢ[ℂ] X := ⟨(P.V s).toLinearMap,P.usual s⟩
lemma flavor (s : Poincare) (x y : X) : inner ℂ (P.V s x) (P.V s y)=inner ℂ x y := (P.spaceKeep s).inner_map_map _ _

def μ (x : X) := P.orbit.P.diagonal x
instance (x : X) : IsFiniteMeasure (P.μ x) := P.orbit.P.finite _
lemma placed (r : Lorentz) (x : X) : P.μ (P.V (Poincare.motion r) x) = (P.μ x).map (Lorentz.act (Lorentz.dual r)) := by
  have he (p : E4) : Poincare.translation (r.act p)*Poincare.motion r=Poincare.motion r*Poincare.translation p := by
    apply Poincare.by_placement;intro b;simp
  have hm : IsFiniteMeasure ((P.μ x).map (Lorentz.act (Lorentz.dual r))) := by infer_instance
  apply Measure.ext_of_charFun; ext1 b
  obtain ⟨p,rfl⟩ := r.sends.surjective b
  have hx : charFun (P.μ (P.V (Poincare.motion r) x)) (r.act p) = charFun (P.μ x) p := by
    unfold μ; rw [P.orbit.total,P.orbit.total]
    change inner ℂ _ (P.V (Poincare.translation (r.act p)) (P.V _ _)) = inner ℂ _ (P.V (Poincare.translation p) x)
    rw [← ContinuousLinearMap.comp_apply, ← P.mult,he p,P.mult]; exact P.flavor ..
  rw [Lorentz.sent,hx, charFun_apply,charFun_apply, integral_map _ _]; rotate_left
  · exact (ContinuousLinearMap.continuous _).measurable.aemeasurable
  · exact (show Continuous (fun y : E4 => Complex.exp ((↑(inner ℝ y (r.act p)):ℂ)*I)) from by fun_prop).aestronglyMeasurable
  congr! 3
  simpa using (Lorentz.dual_sent (Lorentz.dual r) p _).symm

/-- every direction sharpened; true spectrum not just symbols. -/
lemma south (hp : ∀ v : X, (P.μ v).support ⊆ {p : E4|0 ≤ p timeAxis}) : P.orbit.P.region coneᶜ=0 := by
  have h v : (P.μ v).support ⊆ cone := fun x hx => (Lorentz.from_half x).2 fun r => by
    apply hp (P.V (Poincare.motion r) v); rw [P.placed]
    apply Measure.mem_support_iff_forall _|>.mpr
    intro A hA
    obtain ⟨U,hU,hu,hA'⟩ := mem_nhds_iff.mp hA
    refine lt_of_lt_of_le ?_ (measure_mono hU)
    rw [Measure.map_apply (ContinuousLinearMap.continuous _).measurable hu.measurableSet]
    exact ((Measure.mem_support_iff_forall _).1 hx _ ((hu.preimage (ContinuousLinearMap.continuous _)).mem_nhds hA'))
  ext1 x
  apply (P.orbit.P.null_pair closed_cone.isOpen_compl.measurableSet _).mp
  exact measure_mono_null (compl_subset_compl.mpr (h x)) (measure_compl_support)
end Action

section heat
open OS.Semigroup
variable {H : Hilbert} {a : Axis} (U : OS.Semigroup H a)

lemma offiero (x : H) (h : ∀ t : ℝ, U.unit.translation (t • basis a) x=x) : x∈U.ground := by
  have hp (t : ℝ) : U.edge t x=x := by
    have he : SEP a (t • basis a)=0 := Subtype.ext (show t • basis a-_=_ by simp)
    have hv := h t
    simpa [unit,he,U.uZero] using hv
  let f : ℂ → H := fun z => U.F z x
  have hF : AnalyticOnNhd ℂ f OS.Semigroup.inside := fun _ hz =>
    (ContinuousLinearMap.apply ℂ H.space x).analyticAt _ |>.comp (U.localHeat _ hz)
  have hg : duration 1∈OS.Semigroup.inside := dur.mpr (by norm_num)
  have he : EqOn f (fun _ => f (duration 1)) OS.Semigroup.inside := by
    apply hF.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) hg
    intro z
    have hy : Tendsto (fun p : ℝ => duration 1 + sideways p) (𝓝[>] 0) (𝓝[≠] duration 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have ht : Continuous (fun i => duration 1 + sideways i) := by unfold sideways; fun_prop
        simpa using ((ht.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with k hk
      change _ ≠ _; intro he
      have hv := congr_arg Complex.im he; simp [sideways,duration] at hv
      exact (mem_Ioi.mp hk).ne' hv
    obtain ⟨p,hp'⟩ := (hy.eventually z).exists
    apply hp'; unfold f; rw [← U.either hg _]; change U.F _ (U.edge _ _) = _
    rw [hp]
  apply (U.fixed x).2
  have ht (p : ℝ≥0) (hx : 0<p) : U.E p x=f (duration 1) := by rw [← U.roots_heat hx]; exact he (dur.mpr hx)
  have hx : f (duration 1) = x := by
    apply tendsto_nhds_unique (f:=fun t : ℝ≥0 => U.E t x) (l:=𝓝[>] (0:ℝ≥0)) (tendsto_const_nhds.congr' ?_) ?_
    · exact Eventually.mono self_mem_nhdsWithin fun i hI => (ht i hI).symm
    simpa [U.eZero] using! (((U.continuousE x).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
  intro k; rcases eq_or_ne k 0 with hh|hh
  · rw [hh,U.eZero];rfl
  rw [ht _ (pos_iff_ne_zero.mpr hh),hx]
end heat

namespace Action
variable {C : Chamber S timeAxis} (P : Action X) {W : X→L[ℂ] C.H}

/-- W maps into the chamber but distinguished Vacuum AND flows proved
later/specified before projection; not arbitrary filter limits. -/
structure Intervenes (W : X→L[ℂ] C.H) (v : X) : Prop where
  scale (x : X) : ‖W x‖=‖x‖
  across (p) : W.comp (P.orbit.translation p) = (C.flow.unit.translation p).comp W
  start : W v=C.omega

lemma spectrum {w : X} (h : P.Intervenes (C := C) W w) : P.orbit.P.region coneᶜ=0 := by
  refine P.south fun x => ?_
  have he : P.μ x=C.flow.ℚmeasure.diagonal (W x) := by
    apply Measure.ext_of_charFun; ext1 i; unfold μ; rw [P.orbit.total,C.flow.joint]
    rw [← ContinuousLinearMap.comp_apply _ W,h.across i |>.symm]
    exact (LinearIsometry.inner_map_map (⟨W.toLinearMap,h.scale⟩ : X →ₗᵢ[ℂ] C.H) x _).symm
  rw [he]; exact C.flow.nonneg _

theorem only {w : X} (h : P.Intervenes (C:=C) W w) (hc : C.UniqueHeat) (x : X) (hp : ∀ i,P.orbit.translation i x=x) :
    ∃ z : ℂ,z • w=x := by
  have he : W x∈C.D := offiero _ (W x) fun t => by rw [← ContinuousLinearMap.comp_apply _ W, ← h.across, ContinuousLinearMap.comp_apply,hp]
  obtain ⟨z,H⟩ := hc ⟨W x,he⟩
  refine ⟨z,(show Injective W from (⟨W.toLinearMap,h.scale⟩ : X→ₗᵢ[ℂ] C.H).injective) ?_⟩
  rw [map_smul,h.start];exact congr_arg Subtype.val H
end Action
end YM.Boundary
