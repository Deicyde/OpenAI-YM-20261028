import YM.Next.UV_STRESS.Across

/-!
# Detect all Q columns, using physical uniform bounds on mixed tests from Zebra

Coarse offset maps at weight four. `filled_four` still to come from RFree,
doesn't follow from a Tracks hypothesis. Check calibration parameter quantifier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Cells
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {F : Extraction.Order} {h c : ℕ}

abbrev Beans (C : Family G) := Fin (Module.finrank ℂ (Entry C))

def pod (C : Family G) (j : Beans C) := Module.finBasis ℂ (Entry C) j

-- exact tolerance choosing prior to stations. Difference on free continuum
-- compact-budget detector. Pointwise estimates upper and all offsets.

def sturdy (I : Finset (Palette C)) (ε : ℝ) :=
    ∃ B : ℝ,0 < B ∧ ∀ (f : Entry C →L[ℂ] (I→ℂ)),
      (∀ i j, ‖f (pod C j) i- Palette.eval C i.val (pod C j)‖ ≤ ε) →
        ∀ x : Entry C, ‖x‖ ≤ B*‖f x‖

lemma sturdy_exists (I : Finset (Palette C)) (hi : Injective (LinearMap.pi fun i : I => (i.val.eval C).toLinearMap)) :
    ∃ ε : ℝ,0<ε ∧ sturdy C I ε := by
  let A := ContinuousLinearMap.pi fun i : I => i.val.eval C
  obtain ⟨g,hg⟩ := A.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let B := LinearMap.toContinuousLinearMap g
  let M := ‖B‖+1
  have hM : 0<M := by unfold M; positivity
  let G j := LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (Entry C)).coord j)
  let L := (∑ j : Beans C, ‖G j‖)+1
  have hL : 0<L := by unfold L; positivity
  let ε := (1:ℝ)/(2*M)/L
  have he : 0<ε := by unfold ε; positivity
  refine ⟨ε,he,2*M,by positivity,fun f hf x => ?_⟩
  let Y := f-A
  have hB : ‖x‖ ≤ M*‖A x‖ := by
    calc
      _ = ‖B (A x)‖ := congr_arg norm (LinearMap.congr_fun hg x).symm
      _ ≤ _ := (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by unfold M; linarith) (norm_nonneg _))
  have hz : ‖Y x‖ ≤ (1:ℝ)/(2*M)*‖x‖ := by
    have hu (j) : ‖Y (pod C j)‖ ≤ ε := (pi_norm_le_iff_of_nonneg he.le).mpr fun i => hf i j
    have hh : x=∑ j : Beans C, G j x • pod C j := ((Module.finBasis ℂ (Entry C)).sum_repr x).symm
    calc
      _ = ‖∑ j : Beans C, G j x • Y (pod C j)‖ := by
        conv_lhs => rw [hh,map_sum]
        simp_rw [map_smul]
      _ ≤ _ := norm_sum_le ..
      _ ≤ ∑ j : Beans C, (‖G j‖*‖x‖)*ε := Finset.sum_le_sum (fun j _ => by rw [norm_smul]; exact mul_le_mul ((G j).le_opNorm _) (hu j) (norm_nonneg _) (by positivity))
      _ ≤ L*ε*‖x‖ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul,mul_right_comm L ε ‖x‖]
        gcongr; dsimp [L]; linarith
      _ = _ := by unfold ε; field_simp
  have he : ‖A x‖ ≤ ‖f x‖ + (1:ℝ)/(2*M)*‖x‖ := by
    rw [show A x=f x-Y x by change _=f x-(f x-A x); abel]
    exact (norm_sub_le ..).trans (add_le_add_right hz _)
  have hh := hB.trans (mul_le_mul_of_nonneg_left he hM.le)
  rw [mul_add, ← mul_assoc M,show M*(1/(2*M))=1/2 by field_simp] at hh
  linarith

/-- The one offset-Q calibration comparison and root prices needed for spanning.
Physical estimate at this k0 (`c`); no claim inherited by changing hierarchy
or all calibration parameters. E route should choose `D`, not expect granted
at arbitrary displacements satisfying a combinatorial nonoverlap. `Seen`
requires seam-compatible genuine *individual* spectator estimates.
-/
structure AtOffset (Q : QMap C) (h : ℕ) (hc : h+1 ≤ c) (I : Finset (Palette C)) (ε : ℝ) (F : Extraction.Order) : Prop where
  depth : 16*C.S.a c≤C.S.a h
  live : ∀ i : I,∃ D : Marking C i.val, D.Seen C F h hc ∧ ∀ j : Beans C, F.late (fun N p => ∀ o : Site (C.side N p),
    ‖D.live C h o (Q N p o (pod C j)) - i.val.eval C (pod C j)‖ ≤ ε)






end YM.Next.UVStress
