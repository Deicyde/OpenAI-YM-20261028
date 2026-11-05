import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Next.FOUNDATIONS.Regular
import YM.Work.F02
import YM.Work.F05.Actions

/-!
# Canonical terms have the finite-order physical left bounds

Each directional price with polynomially growing test directions is paid
before summing the true path norms. No claim that the hard occurrence or the
kept-row selector is differentiated as a function across a switch. One term,
before multiplying by beta or transferring between levels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Derivs
open Function Lattice Wilson RG Exterior Precision Work.F02 Metric NormedSpace Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}

lemma atom_local (a : Atom G k) (x : Site n) : LocalOn (a.footprint x) (fun U => a.unmasked U x) := by
  intro U V h
  refine congr_arg a.poly (funext fun i => LocalOn.expandAt _ _ (a.leg i).covered x U V (agrees_mono h ?_))
  rintro _ ⟨p,hp,rfl⟩; exact mem_image.mpr ⟨_,mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ _,hp⟩),rfl⟩

lemma stencil_length (s : Slot) (y : Cover) (hy : y∈s.stencil) : Laurent.size y ≤ s.length := by
  rcases mem_union.mp hy with h|h
  · simpa only [Slot.length,sub_zero] using (along_size 0 y s.walk (List.mem_toFinset.mp h)).trans (Nat.le_add_right _ 4)
  · rw [← sub_add_cancel y s.offset]
    have hx : Laurent.size (y-s.offset) ≤ 4 := along_size _ _ _ (List.mem_toFinset.mp h)
    exact (Laurent.size_add ..).trans (by have := offset_size s; unfold Slot.length; omega)


def restrict (S : Support n) (v : Directions G n) : Directions G n := fun e => if e.1 ∈ S then v e else 0


lemma canonical_regular (a : Atom G k) (x : Site n) (p : BudgetPoint) (ha : a.Invariant) :
    p.Regular (a.footprint x) (fun U => a.unmasked U x) := by
  have hf (U : Config G n) : ContDiffAt ℝ (↑p.order : WithTop ℕ∞) (fun v => a.unmasked (increment U v) x) 0 := by
    refine (show ContDiffAt ℝ ω (fun v => a.unmasked (increment U v) x) 0 from ?_).of_le le_top
    have hi : ContDiffAt ℝ ω (fun v => atomExt a x (physical (increment U v))) 0 := (atomExt_contDiff a x).restrict_scalars ℝ
      |>.contDiffAt.comp 0 (physical_contDiffAt (A:=increment U) (fun i => by
        simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt))
    convert Complex.reCLM.contDiff.contDiffAt.comp _ hi using 1
    ext1; simp only [Function.comp_apply,atomExt_physical,Complex.reCLM_apply, Complex.ofReal_re]
  refine ⟨atom_local a x,(a.unmasked_cont x).measurable,?_,fun U _ => hf U, fun U _ A l hl => Next.Foundations.left_has A hl (hf U)⟩
  intro t U; simp only [Atom.unmasked, Work.F05.slot_gauge]; apply ha





namespace ExpPrice
variable (P : ExpPrice G)






end ExpPrice
end YM.Extra.Iteration.Derivs
