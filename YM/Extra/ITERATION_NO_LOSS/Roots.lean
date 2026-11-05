import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Next.FOUNDATIONS.SU2

/-!
# A path implementation of any funded metric row

Path tie rule `slot` on Cover, reading at all native tori (including signed
orientation average applied later on actual terms, not flat transporters).
No dependence on period or actual beta. `Floor` used also at size one for
the constant-fiber normalization; does not require a physical RG step there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Lattice Wilson RG Exterior Precision Bloch Laurent Matrix
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev RootLabel := PlaqAxes × Cover

def rooted (H : Bed) (b : PlaqAxes) (k : RootLabel) : ℝ × Slot :=
  (H.roots (plaquette b) (plaquette k.1) k.2,slot k.2 k.1)

def bundle (H : Bed) (three : ℕ → Atom G 3) (four : ℕ → Atom G 4) (two : ℕ → Atom G 2) : PathData G where
  row b := rooted H b ∘ numbering RootLabel
  loop := two
  cubic := three
  quartic := four

variable {W : PathData G} {u v A η : ℝ} {C : Clip} {H : Bed}

def Aligned (W : PathData G) (H : Bed) := W.row = fun b => rooted H b ∘ numbering RootLabel

def rootPrice (η A : ℝ) := (Fintype.card PlaqAxes : ℝ) * (Real.exp (η * 4) * A)

namespace Aligned
variable (hw : Aligned W H)
include hw
lemma rootsBudget (h : H.roots.strip η A) (b : PlaqAxes) :
    SumBudget (fun i => |(W.row b i).1| * Real.exp (η * (W.row b i).2.length)) (rootPrice η A) := by
  rw [hw]; apply Cost.equiv (f:=fun k : RootLabel => |(rooted H b k).1| * Real.exp (η * (rooted H b k).2.length))
  letI : Nonempty PlaqAxes := ⟨b⟩
  have hb := Cost.nonneg (h (plaquette b) (plaquette b))
  refine Cost.product (Cost.finite _ (mul_nonneg (Real.exp_pos _).le hb)) fun p => ?_
  convert Cost.scale (h (plaquette b) (plaquette p)) (Real.exp (η*4)) (Real.exp_pos _).le using 2

  simp only [rooted,slot_length,Nat.cast_add,Nat.cast_ofNat,Real.norm_eq_abs,mul_add,Real.exp_add]; ring

lemma attached : Attached H W := by
  constructor; intro b p y
  rw [hw]; let F (z : RootLabel) := if (rooted H b z).2.plaq=p ∧ (rooted H b z).2.offset=y then (rooted H b z).1 else 0
  refine ((numbering RootLabel).hasSum_iff (f:=F)).2 ?_
  classical
  convert hasSum_ite_eq (β:=RootLabel) (p,y) (H.roots (plaquette b) (plaquette p) y) using 1
  ext ⟨z,v⟩
  dsimp [F]; split_ifs <;> simp_all [rooted,eq_comm]

lemma termBudget (h : H.roots.strip η A) (he : 0 ≤ η) (b p) :
    HasSum (fun k => if (W.row b k).2.plaq = p then (W.row b k).1 else 0)
      (∑' x, H.roots (plaquette b) (plaquette p) x) := by
  rw [hw]
  let F (q : RootLabel) := if (rooted H b q).2.plaq=p then (rooted H b q).1 else 0
  refine ((numbering RootLabel).hasSum_iff (f:=F)).2 ?_
  have hi : Function.Injective (fun x : Cover => (p,x)) := fun _ _ he => Prod.mk.inj he |>.2
  refine (hi.hasSum_iff ?_).1 ?_
  · rintro ⟨i,x⟩ h; by_cases he : i=p
    · exact False.elim (h ⟨x,by simp [he]⟩)
    simp [F,rooted, he]
  simpa only [Function.comp_def,F,rooted,slot_plaq,if_true] using ((h _ _).summable he).hasSum

private def uno : Side := 1
private local instance : Unique (Site uno) := by change Unique (Axis → ZMod 1); infer_instance
omit hw in
private lemma uno_acts {α β : Type*} (M : Row α β) (i j) : M.acts uno (0,i) (0,j) = ∑' x, M i j x := by
  simp only [Row.acts, of_apply, Subsingleton.elim (0+_) (0:Site uno), if_true]

omit hw in
private lemma metr0 (h : Floor H C uno u v) (i j) : H.metric.acts uno (0,i) (0,j) = if i=j then 1 else 0 := by
  apply Complex.ofReal_injective
  rw [uno_acts, Complex.ofReal_tsum, apply_ite ((↑):ℝ→ℂ),Complex.ofReal_one, Complex.ofReal_zero]
  have he := congr_fun (congr_fun h.starts i) j
  simpa only [Row.read, Laurent.read, of_apply, mode_constant, one_smul, Matrix.one_apply] using he

lemma normalized (h : H.roots.strip η A) (he : 0 ≤ η) (hf : ∀ n, Floor H C n u v) : W.metric_zero C := by
  classical
  intro i j
  have hh (b p : PlaqAxes) : W.symbol0 b p = H.roots.acts uno (0,plaquette b) (0,plaquette p) :=
    (termBudget hw h he b p).tsum_eq.trans (uno_acts ..).symm
  have hy := congr_fun (congr_fun (hf uno).roots (0,plaquette i)) (0,plaquette j)
  rw [mul_apply, Fintype.sum_prod_type, Fintype.sum_unique,Fintype.sum_sum_type, metr0 (hf uno)] at hy
  simp only [transpose_apply,Bed.full,of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, Prod.mk.injEq] at hy
  simp only [Subsingleton.elim (@default (Site uno) (Unique.toInhabited inferInstance)) (0 : Site uno)] at hy
  rw [← plaqEquiv.sum_comp (fun k => H.roots.acts uno (0,k) (0,plaquette i) * H.roots.acts uno (0,k) (0,plaquette j))] at hy
  simp only [true_and] at hy
  simp_rw [hh]
  by_cases e : i = j <;> simpa [mul_ite, ite_mul, e,Ne.symm,(show Function.Injective plaquette from plaqEquiv.injective).eq_iff, ← sq, Real.sq_sqrt C.quadratic_pos.le,plaq_map] using hy

lemma bound {three four two : ℝ} (hσ : 0 < η) (h : H.roots.strip η A) (hf : ∀ n, Floor H C n u v)
    (h2 : Charged W.loop η two) (h3 : Charged W.cubic η three) (h4 : Charged W.quartic η four)
    (s : Silent W.loop) (s2 : SymmetricAtoms W.loop) (s3 : SymmetricAtoms W.cubic) (s4 : SymmetricAtoms W.quartic)
    (paths : ℝ) (hR : rootPrice η A ≤ paths) (hC : three ≤ paths) (hQ : four ≤ paths) : W.Bounds C η paths two :=
  { width := hσ
    rows b := Cost.enlarge (rootsBudget hw h b) hR
    two := h2
    three := Cost.enlarge h3 hC
    four := Cost.enlarge h4 hQ
    invariant i := ⟨s2 i, s3 i, s4 i⟩
    symTerms b p := (termBudget hw h hσ.le b p).summable
    metric := normalized hw h hσ.le hf
    loopTerms i b := ⟨(s i b).1.summable,fun l => ((s i b).2 l).summable⟩
    loop_normal i b := ⟨(s i b).1.tsum_eq,fun l => ((s i b).2 l).tsum_eq⟩ }
end Aligned
end YM.Extra.Iteration
