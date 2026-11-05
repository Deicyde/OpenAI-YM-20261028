import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Calendar
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Jacobi
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix

/-!
# A Borel real regular extension for actual law tests

No smoothness or (awkward to schedule, off analytic predicate branches)
Borel calculation imposed on off-domain behavior of all inputs to the
integral here. Use any unmasked formula proved to have all the required
local charts including equality boundaries. Preserves full Y and gauge
invariance when true *also off-domain* for the same arithmetic formula.
Doesn't erase the flags or indicator reads in an actual label.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Multi Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c : Side} {V : Config G c} {P : BudgetPoint} {n : ℕ} {Y : Support c}
section abstract
variable {X : Type} [TopologicalSpace X] {g : X → ℝ} {x : X}
def stage (g : X → ℝ) := interior {x | ContinuousAt g x}

def repair (g : X → ℝ) := (stage g).piecewise g (fun _ => 0)
lemma moved_stage (f : X → X) (hf : Continuous f) (h : g ∘ f=g) (he : f x∈stage g) : x∈stage g := by
  rw [stage, mem_interior_iff_mem_nhds] at *
  filter_upwards [hf.continuousAt.eventually (show ∀ᶠ y in 𝓝 (f x), ContinuousAt g y from he)] with y hy
  exact h ▸ hy.comp hf.continuousAt

lemma repaired_eq {x y : X} (h : ∀ p∈({(x,y),(y,x)}:Set (X×X)), ∃ f : X → X, Continuous f ∧ g ∘ f = g ∧ f p.1=p.2) : repair g x = repair g y := by
  obtain ⟨f,hf,he,hx⟩:=h (x,y) (by simp); obtain ⟨F,hF,hE,hy⟩ := h (y,x) (by simp)
  have H : x∈stage g ↔ y∈stage g := ⟨fun h => moved_stage F hF hE (hy.symm ▸ h),fun h => moved_stage f hf he (hx.symm ▸ h)⟩
  unfold repair Set.piecewise; by_cases ht : x ∈ stage g; swap; · simp [ht, not_iff_not.mpr H |>.mp ht]
  rw [if_pos ht, if_pos (H.mp ht), ← show f x=y from hx]; exact (congr_fun he x).symm
lemma repair_measurable [MeasurableSpace X] [OpensMeasurableSpace X] : Measurable (repair g) := ContinuousOn.measurable_piecewise
    (fun _ hx => ((show ContinuousAt g _ from interior_subset hx)).continuousWithinAt) continuousOn_const isOpen_interior.measurableSet
end abstract

variable {h : Config G c → ℝ}
lemma repair_at (hv : Crest n h V) : repair h =ᶠ[𝓝 V] h := by
  have ht : V∈stage h := mem_interior_iff_mem_nhds.mpr (hv.near.mono fun _ hh => crest_tr hh)
  exact (show ∀ᶠ U in 𝓝 V,U∈stage h from isOpen_interior.mem_nhds ht).mono fun _ h => if_pos h
lemma repair_local (he : LocalOn Y h) : LocalOn Y (repair h) := by
  intro U V hAA; apply repaired_eq
  have H (U V : Config G c) (hA : Agrees Y U V) : ∃ f : Config G c → Config G c, Continuous f ∧ h ∘ f=h ∧ f U=V := by
    refine ⟨fun z => z*(U⁻¹*V),by fun_prop,funext fun z => he _ _ (fun i hi hj => ?_),by group⟩
    change z i*((U i)⁻¹*V i) = z i; rw [hA i hi hj]; group
  rintro a (ha|ha)
  · exact ha ▸ H U V hAA
  exact (mem_singleton_iff.mp ha) ▸ H V U (fun i hi hj => (hAA i hi hj).symm)
lemma repair_gauge (hg : GaugeInvariant h) : GaugeInvariant (repair h) := by
  intro g V; apply repaired_eq
  have hh (g : Site c → G.El) := show Continuous (fun v : Config G c => gauge g v) by unfold Lattice.gauge; fun_prop
  rintro a (ha|ha)
  · subst a; refine ⟨gauge (g⁻¹),hh _, funext (hg _),funext fun i => ?_⟩
    dsimp [Lattice.gauge]; group
  exact (mem_singleton_iff.mp ha) ▸ ⟨gauge g,hh g,funext (hg g),rfl⟩

set_option maxHeartbeats 520000 in
lemma repair_valid (hg : GaugeInvariant h) (he : LocalOn Y h) (hf : ∀ V, Healthy P.threshold Y V → Crest P.order h V) : P.Regular Y (repair h) := by
  have H V (hV : Healthy P.threshold Y V) : Crest P.order (repair h) V := by obtain ⟨g,hh,hg⟩ := hf V hV; exact ⟨g,hh,(repair_at (hf V hV)).trans hg⟩
  have hr V (hV : Healthy P.threshold Y V) : Germ P.order (repair h) V := (H V hV).germ
  exact ⟨repair_local he,repair_measurable,repair_gauge hg,fun V hV => hr V hV,fun V hV A l hl => (hr V hV).has _ _ hl⟩
end YM.PhysicalNext.JointLoad.Heir
