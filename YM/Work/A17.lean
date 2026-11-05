import Mathlib.Analysis.ODE.ExistUnique
import YM.Bid.Angular


/-!
At each cap the transported action is a representation. The Euclidean laws
control its generators (by the explicit derivative relation of the free
boosts). Uniqueness for the constant-coefficient linear ODE on the larger cap
then propagates the inclusion along boosts, without aligning the changes of
basis themselves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A17
open Set Function Org Spec Extraction Climb Table Spin Boundary Mink Bid
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {S : Table C.book} (W : MaxwellData C) (U : ∀ d, change S d)

private lemma run_one (n : ℕ) (x : S.Field n) : run U W.vacuum n 1 x=x := by
  have h (p : (Bel C.book).Field n) : W.vacuum.shell n 1 p=p :=
    (Bel C.book).pin_inj n ((W.rolls.ties 1 n p).symm.trans (W.rolls.identity _))
  simp [run,h]

private lemma run_mul (n : ℕ) (a b : Lorentz) (x : S.Field n) :
    run U W.vacuum n (a*b) x=run U W.vacuum n a (run U W.vacuum n b x) := by
  have h (p : (Bel C.book).Field n) := W.rolls.representation a b ((Bel C.book).pin n p)
  have he (p : (Bel C.book).Field n) : W.vacuum.shell n (a*b) p = W.vacuum.shell n a (W.vacuum.shell n b p) := by
    apply (Bel C.book).pin_inj
    simpa only [W.rolls.ties] using h p
  simp [run,he]

variable {W U} {I : IR (C:=C) S} {V : DiffPlan S} {F : Extraction.Order}
    {H : UV C F S V W I} {c : ℝ} {J : Stress S} (h : Tab S V W I H c U J)
private abbrev generator (n : ℕ) (i : SpaceAxis) : S.Field n →ₗ[ℂ] S.Field n :=
  (-Complex.I) • (mill W I c U).lie n (Ortho.plane timeAxis i.castSucc)

include h
private lemma run_deriv_zero (n : ℕ) (i : SpaceAxis) (x : S.Field n) : HasDerivAt
    (fun t => run U W.vacuum n ((Ray.fromAxis i).boost t) x)
    (generator (W:=W) (I:=I) (c:=c) (U:=U) n i x) (0 : ℝ) := by
  obtain ⟨u,rfl⟩ := (U n).surjective x
  let M := (U n).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have ht := M.hasFDerivAt.comp_hasDerivAt 0 (W.rolls.boosts n i u)
  have he := Spin.transmits U _ W.lit _ h.pivot
  change HasDerivAt _ ((-Complex.I) • (mill W I c U).lie n _ (U n u)) (0 : ℝ)
  rw [he n _ _ , ← (U n).map_smul]
  simpa only [run, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using! ht

private lemma run_deriv (n : ℕ) (i : SpaceAxis) (x : S.Field n) (t : ℝ) : HasDerivAt
    (fun r => run U W.vacuum n ((Ray.fromAxis i).boost r) x)
    (generator (W:=W) (I:=I) (c:=c) (U:=U) n i (run U W.vacuum n ((Ray.fromAxis i).boost t) x)) t := by
  have hd := run_deriv_zero h n i (run U W.vacuum n ((Ray.fromAxis i).boost t) x)
  simpa only [Function.comp_def,one_smul, ← run_mul, ← Ray.boost_add, sub_add_cancel] using
    hd.scomp_of_eq t ((hasDerivAt_id' t).sub_const t) (by simp)

private lemma rise_generator (i : SpaceAxis) {d e : ℕ} (hle : d ≤ e) (x : S.Field d) :
    generator (W:=W) (I:=I) (c:=c) (U:=U) e i (V.rise hle x) =
      V.rise hle (generator (W:=W) (I:=I) (c:=c) (U:=U) d i x) := by
  let R := mill W I c U
  have hs : R.Laws V H.basis.kernel.spin := h.locality.spots
  let g := Ortho.plane timeAxis i.castSucc
  let N := (V.rise hle).toContinuousLinearMap.restrictScalars ℝ
  have he := hs.infinitesimal e g (V.rise hle x)
  simp_rw [hs.filtered] at he
  have heq := he.unique (N.hasFDerivAt.comp_hasDerivAt 0 (hs.infinitesimal d g x))
  change (-Complex.I) • R.lie e g (V.rise hle x) = V.rise hle ((-Complex.I) • R.lie d g x)
  rw [map_smul, heq]; rfl

private lemma run_boost {d e : ℕ} (hle : d ≤ e) (i : SpaceAxis) (x : S.Field d) (t : ℝ) :
    run U W.vacuum e ((Ray.fromAxis i).boost t) (V.rise hle x) = V.rise hle (run U W.vacuum d ((Ray.fromAxis i).boost t) x) := by
  let M := (generator (W:=W) (I:=I) (c:=c) (U:=U) e i).toContinuousLinearMap
  let N := (V.rise hle).toContinuousLinearMap.restrictScalars ℝ
  let f := fun t => run U W.vacuum e ((Ray.fromAxis i).boost t) (V.rise hle x)
  let g := fun t => V.rise hle (run U W.vacuum d ((Ray.fromAxis i).boost t) x)
  have hf (t) : HasDerivAt f (M (f t)) t := run_deriv h e i _ t
  have hg (t : ℝ) : HasDerivAt g (M (g t)) t := by
    change HasDerivAt g (generator (W:=W) (I:=I) (c:=c) (U:=U) e i (V.rise hle _)) t
    rw [rise_generator h i]
    exact N.hasFDerivAt.comp_hasDerivAt t (run_deriv h d i _ t)
  have he : f 0 = g 0 := by simp [f,g,run_one]
  have heq := ODE_solution_unique_univ (s := fun _ => Set.univ) (fun (_ : ℝ) => M.lipschitz.lipschitzOnWith)
    (fun t => ⟨hf t, mem_univ _⟩) (fun t => ⟨hg t, mem_univ _⟩) he
  exact congr_fun heq t

omit h

theorem answer : YM.Bid.A17 := by
  intro gens G C S F V W I H c U J h d e hle p
  have hp : p ∈ beamGens := by rw [(gens : beamGens = ⊤)]; trivial
  exact Subgroup.closure_induction (p := fun p _ => ∀ v, run U W.vacuum e p (V.rise hle v) = V.rise hle (run U W.vacuum d p v)) (by
    intro p hp v
    rcases hp with ⟨K,hk,rfl⟩ | ⟨i,t,rfl⟩
    · simpa only [run,LinearEquiv.trans_apply,W.rolls.spatial, mill, morph] using h.locality.spots.filtered d e hle K v
    exact run_boost h hle i v t)
    (by simp only [run_one, implies_true])
    (by intro a b _ _ ha hb v; simp only [run_mul,hb,ha])
    (by
      intro a _ ha v
      apply (run U W.vacuum e a).injective
      rw [← run_mul,ha,← run_mul, mul_inv_cancel,run_one,run_one]) hp
end YM.Work.A17
