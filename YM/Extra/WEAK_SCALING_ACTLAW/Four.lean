import YM.Extra.WEAK_SCALING_ACTLAW.Pairs

/-! # Canonical free weight-four generators in the actual Wick moment table -/
set_option maxHeartbeats 500000
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Set Filter Function Labels Maxwell Wick Tensor Climb
open scoped Matrix.Norms.Frobenius Topology InnerProductSpace ContDiff
variable {G : Gauge}

theorem strength_is_curl (A : Taylor G 0) (a b : Axis) (z : Fin 0 → E4) : takeCurl A a b z = strength A a b := by
  have h c d : (A.val c).curryLeft (basis d) z = A.value c (basis d) := by
    rw [ContinuousMultilinearMap.curryLeft_apply]; apply congrArg (A.val c); funext i; exact Fin.cases rfl (fun j => j.elim0) i
  have hs := skew A b a
  rw [strength,strength,← smul_neg] at hs
  rw [takeCurl,smul_apply,sub_apply,h,h,(smul_right_injective _ (two_ne_zero (α:=ℝ)) hs : A.value a (basis b) = _),strength]
  simp [two_smul]

abbrev leg (a b : Axis) (c : G.ColorIndex) : Maxwell.Probe G 0 := constrain (fromF G (fun _ => 0) c a b)
lemma reduced (a b : Axis) (c : G.ColorIndex) : reduceEq (pol a b c) = Maxwell.symbol 0 (leg a b c) := by
  apply equalPol; intro A
  rw [Maxwell.symbol_test,jet_value,pol_eval,← strength_is_curl _ _ _ 0, match_leg]; rfl

lemma one_wick (x : Points 1) (v : Fin 1 → WickPol G) : Wick.moment G x v = probe (0 : TaylorTower G) (v 0) := by
  let l := (Wick.moment G x).toLinearMap (fun _ => 0) 0
  have ht : (v' : Fin 1 → WickPol G) → _ := fun (v' : Fin 1 → WickPol G) => show l (v' 0) = Wick.moment G x v' from
    congrArg (Wick.moment G x) (funext (fun i => by rw [Subsingleton.elim i 0,Function.update_self]))
  have hl : l = (probe (0 : TaylorTower G)).toLinearMap := by
    refine (monBasis G).ext fun i => ?_
    by_cases h : i=0
    · simpa [h,monBasis] using (ht (fun _ => 1)).trans (Wick.constants _)
    rw [show l (monBasis G i) = monomial x (fun _ => i) from (ht (fun _ => monBasis G i)).trans (moment_basis (fun _ => i) _)]
    let w : Powers G 1 := fun _ => i
    obtain ⟨j,hj⟩ := Finsupp.ne_iff.mp h
    let u := Occ.atSlot (W:=w) 0 j 0 (Nat.pos_of_ne_zero hj)
    haveI : IsEmpty (Occ.Matching w) := ⟨fun P => Occ.different P u (Subsingleton.elim ..)⟩
    rw [show monomial x w = 0 by simp [monomial]]
    simp [monBasis,Maxwell.probe, Maxwell.coord,MvPolynomial.aeval_zero',MvPolynomial.constantCoeff_eq,h]
  exact (ht v).symm.trans (LinearMap.congr_fun hl _)

variable (L : Register G)
def pinned (a b i j : Axis) : (Bel L).Field 4 :=
    (Bel L).project 4 (((Maxwell.standard L.grid).coord 4).coords (pairLabel G a b i j))
lemma pairing_types (h : G.Simple) (H : (Bel L).Hierarchy) : Cube.Types H.spin (pinned L) := by
  refine ⟨fun a b c d => ?_,fun a b c d => ?_,fun a b c d => ?_,fun k a b c d => ?_,fun a b c d => ?_, fun x => ?_⟩
  · apply congrArg ((Bel L).project 4 ∘ ((Maxwell.standard L.grid).coord 4).coords)
    exact Subtype.ext (Labels.eval_ext _ _ (fun A => by rw [pairLabel,pairLabel,pair_eval,pair_eval,real_inner_comm]))
  · unfold pinned
    rw [← map_neg,← map_neg]; apply congrArg ((Bel L).project 4 ∘ ((Maxwell.standard L.grid).coord 4).coords)
    exact Subtype.ext (Labels.eval_ext _ _ (fun A => by simp only [Submodule.coe_neg,map_neg,pairLabel,pair_eval]; rw [skew (A 0) a b,inner_neg_left,Complex.ofReal_neg]))
  · rw [pinned,Table.conj_project]; apply congrArg
    have he : realBar (pairLabel G a b c d) = pairLabel G a b c d := Subtype.ext (Labels.eval_ext _ _ (fun A => by
      change Labels.read A (conjPol _) = _; simp only [conj_value,pairLabel,pair_eval, Complex.star_def,Complex.conj_ofReal]))
    apply ((Maxwell.standard L.grid).coord 4).coords.symm.injective
    rw [← (Maxwell.standard L.grid).geom_conj,LinearEquiv.symm_apply_apply,he]
  · simp only [pinned, Table.mirror_project]; change (Bel L).project _ (Labels.Frame.act _ _ (((Maxwell.standard L.grid).coord _).coords _)) = _
    rw [Labels.Frame.act_coords, rotated, map_smul, map_smul]; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _).symm
  · rw [Work.A15.front_apply]
    let Y := Bel L
    have ht : ∀ t : (Maxwell.standard L.grid).Token, Y.read (n:=1) 0 (fun _ => t) =
        probe (0: TaylorTower G) (observable G t.1 (((Maxwell.standard L.grid).coord _).coords.symm t.2)) := fun _ => one_wick ..
    let t : (Maxwell.standard L.grid).Token := ⟨4,((Maxwell.standard L.grid).coord _).coords (pairLabel G a b c d)⟩
    rw [show Fin.cons (α:=fun _ => Y.Tag) ⟨4,pinned L a b c d⟩ Fin.elim0 = Y.classTokens ∘ (fun _ => t) by
      funext i; exact Fin.cases rfl (fun j => j.elim0) i, Y.at_project Y H.laws.toSymmetric (fun _ => le_rfl) (fun i j _ => @Subsingleton.elim (Fin 1) _ _ _),ht]
    dsimp only [t]; rw [LinearEquiv.symm_apply_apply]; change probe 0 (reduceEq (pairPol G a b c d)) = 0
    simp only [jet_value,pair_eval, Pi.zero_apply,map_zero,strength,Taylor.value,Tensor.diagonal, ZeroMemClass.coe_zero, zero_apply,smul_zero,inner_zero_left,Complex.ofReal_zero]
  · obtain ⟨p,rfl⟩ := (Bel L).onto _ x
    obtain ⟨p,rfl⟩ := ((Maxwell.standard L.grid).coord 4).coords.surjective p
    obtain ⟨z,q,hq⟩ := inputs h p
    have hU : ((Maxwell.standard L.grid).coord 4).coords (Labels.unit G 4) = (Maxwell.standard L.grid).scalar 4 := by
      rw [Register.scalar]; simp [Register.coord,Maxwell.standard]; exact ((L.coord 4).coords_unit).trans (one_smul ℂ _).symm
    refine ⟨z,q,?_⟩
    rw [hq]; simp only [map_sum,map_add,map_smul,hU]; rfl
end YM.Extra.WeakScaling.Color
