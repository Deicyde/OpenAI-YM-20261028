import YM.Integration.WilsonInverseSchedule
import YM.RG08.Calendar.Venture

/-! Joint admission of the extra inverse-map price with all original
Calendar targets, using a single original `oneC` selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInverseSchedule
open RG08 RG08.Admission
open Function Filter Lattice Wilson Exterior Precision Laurent Finset RG Next.Free RG.Supply Bloch Input Conductor Wings Stationary Staffer Drift Virtue
open Town Run Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Creek Dart Wax Canon
open Next.Foundations UVExtension PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch
open scoped BigOperators Topology Real ContDiff Classical
variable {G : Gauge} {I : Type}

structure DocksWithInverse (C : Family G) (N : Names G C.path.levels.clock.kernel)
    extends Docks C N where
  inverseReserves : ∀ᶠ n in atTop, Affords (inverseNeed N) C.path.levels n

/-- All windows use the same Family, Names and inverse receipt. -/
theorem DocksWithInverse.samples {C : Family G} (hG : G.Simple)
    {N : Names G C.path.levels.clock.kernel} (W : DocksWithInverse C N)
    (a : Ask) :
    ∀ᶠ k in atTop, ∀ u : I → Windows, NearZ C.path.levels u →
      (∀ i, k ≤ (u i).start) → ∀ ν : G.ColorIndex,
        BallWithInverse N (chart G) ν u a.E a.vac ∧
          Lights (W.plan a) u ν (chart G) ∧ Tincture (W.plan a) u := by
  filter_upwards [W.toDocks.samples hG a, W.inverseReserves] with k hk hInv
  intro u hu hs ν
  obtain ⟨ball, lights, tincture⟩ := hk u hu hs ν
  exact ⟨⟨ball, inverseEarned hG hu (fun i => hInv.later (hs i))⟩,
    lights, tincture⟩

set_option maxRecDepth 8000 in
/-- Buy all original targets and the inverse charge in one original `oneC`
selection.  This is not an assertion about an arbitrarily preselected C. -/
theorem coadmit (h : G.Simple) (K : KernelChoices)
    (hp : ∀ P : RG.Patch, P.Branches K G) [Encodable I] (W : I → Need) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book),
      Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel = K ∧ Oasis.Floral (hG := h) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ p in atTop, ∀ n (v : Fin n → C.book.Token),
        (∀ i, (v i).1 ≤ d) → ∃ g, Poppy.Margins C n p k v g) ∧
      Bindage C ∧ (∀ i, ∀ᶠ n in atTop, Affords (W i) C.path.levels n) ∧
      ∃ N : Names G C.path.levels.clock.kernel, Nonempty (DocksWithInverse C N) := by
  obtain ⟨N⟩ := names h K
  let B (a : Ask) := Classical.choice
    (wishes (Next.Foundations.sound G) (valuation G) N a)
  let V : (I ⊕ Ask) ⊕ Unit → Need :=
    Sum.elim (Sum.elim W (fun a => treasury (chart G) (B a)))
      (fun _ => inverseNeed N)
  let v : Orders := ⟨4, fun i => 6 + i, fun i => 2 + i, fun i => 100 + i⟩
  have hE (i : ℕ) : 100 ≤ v.supportExp i := by
    change (100 : ℝ) ≤ 100 + i
    simp
  have he : Draft v := by
    refine ⟨le_rfl, fun i j hij => Nat.add_le_add_left hij 6,
      fun i j hij => Nat.add_le_add_left hij 2, fun i j hij => ?_,
      fun i => lt_of_lt_of_le (by norm_num) (hE i),
      fun i => by change _ ≤ 6 + i; omega,
      fun i => by change _ ≤ 2 + i; omega⟩
    change (100 : ℝ) + i ≤ 100 + j
    gcongr
  obtain ⟨C, f, T, hZ, hC, hF, hX, H, x, hS, J, hB⟩ :=
    oneC h K hp v he hE V
  have hV (i : (I ⊕ Ask) ⊕ Unit) :
      ∀ᶠ n in atTop, Affords (V i) C.path.levels n :=
    (C.path.levels.fits.deep.eventually
      (eventually_ge_atTop (Encodable.encode i))).mono
        (fun j hj => hB _ j hj)
  refine ⟨C, f, T, hZ, hC, hF, hS, hX, H, x, J,
    fun i => hV (Sum.inl (Sum.inl i)), ?_⟩
  subst K
  obtain ⟨Z, -, hz⟩ := same_frames (X := C.path.levels)
    J.fonts.symm J.stencil.symm J.parcel.symm B
  refine ⟨N, ⟨{ toDocks := ?_, inverseReserves := ?_ }⟩⟩
  · exact ⟨Z, fun i => by rw [← hz]; exact hV (Sum.inl (Sum.inr i)),
      hC.sections, same_pop J.fonts.symm J.stencil.symm (valuation G)⟩
  · exact hV (Sum.inr ())

end YM.Integration.WilsonInverseSchedule
