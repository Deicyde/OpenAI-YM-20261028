import YM.Push.GRID_APPROXIMATION.Produce

/-!
# Projection checks: support clouds, signs, low cases

Strict distances to h cells are port requirements for chess estimates,
and the Cover itself needs only ordinary bounded measurable observables.
Verify here exactly what's meant by its actually local implementation, also
for the FLASH. Don't need to fix a finite detector arity in the supply.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Labels MeasureTheory Function Filter Set Cells OS Next.BOUNDARY
open scoped Topology BigOperators

variable {G : Gauge} {ι : Type*} [Fintype ι] {C : Family G} {h : ℕ} {f : Extraction.Order}




variable {n : ℕ} {v : Fin n → C.book.Token} (x : Fin n → Cover)
variable (Z : ∀ i, Figures C (v i) h) (D : ∀ i, Figures C (flipTokens (C:=C) v i) h)
variable (hz : ∀ i, (Z i).Gives f) (hd : ∀ i, (D i).Gives f)







private lemma through_one (d) (he : d≤1) (F : Frame G d) (i : F.Index) : i=0 := by
  classical
  let p := F.basis i
  let k := MvPolynomial.coeff 0 p.val
  have hp : p=k • Labels.unit G d := by
    apply Subtype.ext
    change p.val=k • (1 : Pol G); ext a
    rcases eq_or_ne a 0 with h|h
    · subst a; simp [k]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_one, if_neg (Ne.symm h), smul_zero]
    by_contra hh
    have ht : height a ≤ d := (MvPolynomial.mem_restrictSupport_iff ℂ).mp
      (show p.val ∈ limited G d from p.property.1) (MvPolynomial.mem_support_iff.mpr hh)
    obtain ⟨j,hj⟩ : a.support.Nonempty := by simpa using h
    have hg : 2 ≤ height a := by
      unfold height; rw [Finsupp.weight_apply,Finsupp.sum]; apply le_trans _
        (Finset.single_le_sum (f:=fun x => a x • generation x) (fun i _ => Nat.zero_le _) hj)
      have hv : generation j ≤ a j*generation j := le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj))
      exact le_trans (show 2 ≤ generation j by unfold generation; omega) hv
    omega
  by_contra hm
  have hx := congr_arg (fun p => F.coords p i) hp
  unfold p at hx; simp [hm,Frame.e0] at hx

/-- Low weight (d=0,1) palette is just unit direction in the actual
conventions. `C.Makes` supplies it. No kinetic inputs needed here. -/
lemma low (T : C.Makes) (d h : ℕ) (he : d≤1) (x : Fin n → Cover) : PlotBounds C f d h n x := by
  refine plots T ?_ x
  intro i hi j hj
  exact False.elim (hj (through_one i (hi.trans he) _ _))
end YM.Push.GridApprox
