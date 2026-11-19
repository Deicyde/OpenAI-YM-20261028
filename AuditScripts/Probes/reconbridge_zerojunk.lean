import ChallengeSpec

/-! Audit probe (reconstruction bridge, contested `Reconstructed.boundary` / ZeroInvisible).
Not part of the submission.

1. `vector_eq_zero_of_mem`, `ve_eq_zero`: a word containing a zero label has vacuum
   expectation `0` (linearity of `FieldSystem.field` in the label).
2. `boundary_of_junk`: for such a word, `Reconstructed.boundary` is DISCHARGED by eventual
   non-integrability of the shifted integrand (Bochner junk value `integral_undef`), with no
   condition on the continuation or the selected correlation.
3. `one_point_integral_zero`: for `n = 1` the constant height `0` is `StrictMono`, the shift
   surface does not move with `r`, and `boundary` yields the exact equation
   `∫ F(time x, space x) * f x = 0` for every test (junk included). -/

set_option autoImplicit false
noncomputable section

namespace YMAuditZeroJunk
open YangMills MeasureTheory Filter Topology Set

theorem vector_eq_zero_of_mem {H : HilbertSpace} {L : FieldLabels} (F : FieldSystem H L) :
    ∀ (w : List (L.carrier × TestFunction)), (∃ p ∈ w, p.1 = 0) → F.vector w = 0
  | [], ⟨p, hp, _⟩ => by simp at hp
  | q :: w, ⟨p, hp, h0⟩ => by
    rcases List.mem_cons.1 hp with rfl | hp'
    · simp [FieldSystem.vector, h0]
    · simp [FieldSystem.vector, vector_eq_zero_of_mem F w ⟨p, hp', h0⟩]

theorem ve_eq_zero {H : HilbertSpace} {L : FieldLabels} (F : FieldSystem H L) {n : ℕ}
    (labels : Fin n → L.carrier) (tests : Fin n → TestFunction) (i : Fin n)
    (hi : labels i = 0) : F.vacuumExpectation labels tests = 0 := by
  unfold FieldSystem.vacuumExpectation
  rw [vector_eq_zero_of_mem F _ ⟨(labels i, tests i), List.mem_ofFn.2 ⟨i, rfl⟩, hi⟩]
  simp

theorem boundary_of_junk {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) {n : ℕ}
    (v : Fin n → T.Tag) (i : Fin n) (hv : (v i).2 = 0) (height : Fin n → ℝ)
    (tests : Fin n → TestFunction)
    (hni : ∀ᶠ r in 𝓝[>] (0:ℝ), ¬ Integrable (fun x : Points n =>
      T.continuation v (Hierarchy.complexShift r height x) (Hierarchy.spatialPoints x) *
        Hierarchy.tensorTest tests x)) :
    Tendsto (fun r => ∫ x : Points n, T.continuation v (Hierarchy.complexShift r height x)
      (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x) (𝓝[>] 0)
      (𝓝 (T.theory.fields.vacuumExpectation (fun i => T.toLabel (v i).1 (v i).2) tests)) := by
  rw [ve_eq_zero _ _ _ i (by simp [hv])]
  have he : (fun _ : ℝ => (0:ℂ)) =ᶠ[𝓝[>] (0:ℝ)] (fun r => ∫ x : Points n,
      T.continuation v (Hierarchy.complexShift r height x) (Hierarchy.spatialPoints x) *
        Hierarchy.tensorTest tests x) :=
    hni.mono fun r hr => (integral_undef hr).symm
  exact tendsto_const_nhds.congr' he

theorem one_point_integral_zero {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (hR : T.Reconstructed) (v : Fin 1 → T.Tag) (hv : (v 0).2 = 0)
    (tests : Fin 1 → TestFunction) :
    ∫ x : Points 1, T.continuation v (fun i => (time (x.ofLp i) : ℂ))
      (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x = 0 := by
  have hb := hR.boundary v 0 (Subsingleton.strictMono _) tests
  rw [ve_eq_zero _ _ _ 0 (by simp [hv])] at hb
  have hc : (fun r : ℝ => ∫ x : Points 1, T.continuation v (Hierarchy.complexShift r 0 x)
      (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x) =
      fun _ => ∫ x : Points 1, T.continuation v (fun i => (time (x.ofLp i) : ℂ))
        (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x := by
    funext r
    congr 1
    funext x
    congr 2
    funext i
    simp [Hierarchy.complexShift]
  rw [hc] at hb
  exact tendsto_nhds_unique tendsto_const_nhds hb

/-- For `n = 2` no admissible height is constant in `r`: imaginary gaps are `r * (h j - h i)`. -/
example (r : ℝ) (height : Fin 2 → ℝ) (x : Points 2) :
    (Hierarchy.complexShift r height x 1).im - (Hierarchy.complexShift r height x 0).im =
      r * (height 1 - height 0) := by
  simp [Hierarchy.complexShift]
  ring

#print axioms boundary_of_junk
#print axioms one_point_integral_zero

end YMAuditZeroJunk
