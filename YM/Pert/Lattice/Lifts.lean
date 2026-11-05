import YM.Pert.Lattice.Coherence
import YM.Extra.FREE_DETECTOR_ALGEBRA.Filtrate
import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank
import YM.UVNext.FREE_STRESS_CERTIFICATE.Samples
/-! Linear projections onto Maxwell+Bianchi sector polynomial representatives, using the supplied orthogonal projection in derivative-coordinate norm. All horizon inclusions commute with the label lift.
No field equations on interacting dynamics are imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Pert.RawLabels
open Function Filter Labels Maxwell Extra.FD Tensor UVNext
open scoped Topology InnerProductSpace
variable {G : Gauge} {d e j : ℕ} (F : Frames G)

private lemma inner_inv (u : G.El) (x y : G.Color) : inner ℝ (G.adjoint u x) (G.adjoint u y)= inner ℝ x y := by simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,G.norm_adjoint]
private lemma color_dot (u : G.El) (P Q : Maxwell.TwoJet G.Color j) : dotF (dye (conjG u) P) (dye (conjG u) Q) = dotF P Q := by
  simp only [dotF_eval, dotDir_eval]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  exact inner_inv u _ _
private lemma restr (u : G.El) (Q : Sol G.Color j) : dye (conjG u) Q.val = (actionG u j Q).val := rfl
lemma color_asSol (u : G.El) (P : TwoJet G.Color j) : asSol (dye (conjG u) P) = actionG u j (asSol P) := by
  apply (dualSol G.Color j).injective; apply LinearMap.ext; intro q
  have he : q = actionG u j (actionG u⁻¹ j q) := by
    apply Subtype.ext; funext a b; ext1 x
    exact Eq.symm ((G.adjoint_mul u u⁻¹ (q.val a b x)).symm.trans (by rw [mul_inv_cancel]; simp))
  let z := actionG u⁻¹ j q
  rw [asSol_duality,dualSol_val,he,← restr, ← restr, ← restr, color_dot, color_dot]
  exact (asSol_duality P z).symm
private lemma calc_dual {P : TwoJet G.Color j} {A : Sol G.Color j} : (∀ q : Sol G.Color j, dotF P q.val = dotF A.val q.val) → asSol P = A := fun h=> (dualSol G.Color j).injective (LinearMap.ext (fun q=> (asSol_duality P q).trans (h q)))
lemma turned_asSol (s : Ortho) (P : TwoJet G.Color j) : asSol (carry s P) = solO s (asSol P) := by
  apply calc_dual; intro q
  let u := (solO (F:=G.Color) (j:=j) s).symm q
  have he : q.val = carry s u.val := congrArg Subtype.val (show q=solO s u from (LinearEquiv.apply_symm_apply ..).symm)
  refine (congrArg _ he).trans ((carry_dot _ _ _).trans ?_)
  calc
    dotF P u.val = dotF (asSol P).val u.val := (asSol_duality P u).symm
    _ = dotF (carry s (asSol P).val) (carry s u.val) := (carry_dot s _ _).symm
    _ = dotF (carry s (asSol P).val) q.val := congrArg _ he.symm
lemma takeCurl_color (u : G.El) (p : Taylor G j) : takeCurl (Taylor.paint u p)=dye (conjG u) (takeCurl p) := by
  funext a b; ext1 v
  change ((j+1:ℕ):ℝ) • (G.adjoint u _ - G.adjoint u _) = G.adjoint u (((j+1:ℕ):ℝ) • (_ - _)); rw [map_smul,map_sub]; rfl
lemma jet_color (u : G.El) (q : Sol G.Color j) : gaugeJet (actionG u j q) = Taylor.paint u (gaugeJet q) := by
  apply potential.injective; apply Subtype.ext; change takeCurl _ = takeCurl _; rw [match_leg, takeCurl_color,match_leg,restr]
/-- Coordinate projection onto the gauge jet of the closest on-shell linear curvature (only a free-theory representative). -/
def rebase (G : Gauge) (j : ℕ) := gaugeJet ∘ₗ sendTo G j
lemma rebase_color (u : G.El) (p : Taylor G j) : rebase G j (Taylor.paint u p) = Taylor.paint u (rebase G j p) := by
  change gaugeJet (asSol (takeCurl _)) = _
  unfold rebase; rw [LinearMap.comp_apply,← jet_color u (sendTo G j p)]; apply congrArg _; change asSol (takeCurl _) = _; rw [takeCurl_color, color_asSol]; rfl
lemma rebase_turn (u : Ortho) (p : Taylor G j) : rebase G j (Taylor.turn u p) = Taylor.turn u (rebase G j p) := by
  change gaugeJet (asSol (takeCurl _)) = _
  unfold rebase; rw [LinearMap.comp_apply,← radial_turn u (sendTo G j p)]; apply congrArg _; change asSol (takeCurl _) = _; rw [takeTurn,turned_asSol]; rfl
lemma convertPol (p : Pol G) : changed (rebase G) p = writeRaw (reduceEq p) := by apply eval_ext; intro A; rw [eval_changed,writeRaw_read,jet_value]; rfl
lemma unchanged (p : Pol G) : reduceEq (changed (rebase G) p) = reduceEq p := by rw [convertPol,writeRaw_after]
lemma flat_idem (p : Pol G) : changed (rebase G) (changed (rebase G) p)= changed (rebase G) p := by nth_rw 1 [convertPol,unchanged]; rw [convertPol]

def fixedPolynomial (G : Gauge) (d : ℕ) : Labels.Label G d →ₗ[ℂ] Label G d where
  toFun p := ⟨changed (rebase G) p.val, ⟨moved_limit p.property.1 _, fun A u=> by
    simp only [eval_changed, show changedJet (rebase G) (colored u A) = colored u (changedJet (rebase G) A) from funext fun j => rebase_color u _]
    exact (show p.val ∈ invariantSpace G from p.property.2) _ u⟩⟩
  map_add' a b := Subtype.ext (map_add (changed (rebase G)) a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (changed (rebase G)) r a.val)
lemma fixed_unit : fixedPolynomial G d (Labels.unit G d)= Labels.unit G d := Subtype.ext (map_one (changed (rebase G)))
lemma fixed_includes (w : d≤e) (p : Label G d) : fixedPolynomial G e (raiseLabel G w p) = raiseLabel G w (fixedPolynomial G d p) := rfl
lemma fixed_pure (p : Label G d) (m) : gradePart m (fixedPolynomial G d p) = fixedPolynomial G d (gradePart m p) := Subtype.ext ((component_change (rebase G) p.val m).symm)
lemma fixed_real (p : Label G d) : Labels.realBar (fixedPolynomial G d p) = fixedPolynomial G d (Labels.realBar p) := by
  apply Subtype.ext (eval_ext _ _ ?_); intro A; simp only [Labels.realBar,fixedPolynomial,LinearMap.coe_mk, AddHom.coe_mk, Subtype.val,conj_value,eval_changed]
lemma fixed_ortho (s : Ortho) (p : Label G d) : Labels.tensor s (fixedPolynomial G d p) = fixedPolynomial G d (Labels.tensor s p) := by
  apply Subtype.ext (eval_ext _ _ ?_); intro A; change read A (rotated s (changed _ _)) = read A (changed (rebase G) (rotated s p.val)); simp only [rotated,eval_changed]; refine congrArg (fun q => read q p.val) ?_; exact funext (fun j => rebase_turn s⁻¹ _)

-- Use actual filtered comparator labels, not an independent quotient type.
def enroll (d : ℕ) := FreeStress.embed F d
lemma enroll_eq {p q : Label G d} : enroll F d p = enroll F d q ↔ reduceEq p.val = reduceEq q.val := by
  have hp (Q : Label G d) : writes F d (enroll F d Q)= reduceEq Q.val := by
    rw [show enroll F d Q = (freeTable F).project d ((F.level d).coords Q) from rfl, writes_project]; change observable G d (_) = _
    exact congrArg (fun q : Label G d => reduceEq q.val) ((F.level d).coords.symm_apply_apply Q)
  exact ⟨fun h => (hp _).symm.trans ((congrArg _ h).trans (hp _)), fun h => (writes_inj F d) ((hp _).trans (h.trans (hp _).symm))⟩
lemma enroll_fixed (p : Label G d) : enroll F d (fixedPolynomial G d p) = enroll F d p := (enroll_eq _).2 (unchanged _)
lemma fixed_enroll {p q : Label G d} (h : enroll F d p=enroll F d q) : fixedPolynomial G d p = fixedPolynomial G d q := Subtype.ext ((convertPol p.val).trans ((congrArg _ ((enroll_eq _).mp h)).trans (convertPol q.val).symm))
def physicalLabel (d : ℕ) : (Maxwell.freeTable F).Field d →ₗ[ℂ] Label G d := fixedPolynomial G d ∘ₗ (F.level d).coords.symm.toLinearMap ∘ₗ (Maxwell.freeTable F).representative d
@[simp] lemma physical_round (p : (Maxwell.freeTable F).Field d) : enroll F d (physicalLabel F d p) = p := by
  rw [physicalLabel,LinearMap.comp_apply,enroll_fixed]; change (freeTable F).project d ((F.level d).coords ((F.level d).coords.symm _)) = p
  rw [LinearEquiv.apply_symm_apply]; exact Table.rep ..
lemma embed_round (p : Labels.Label G d) : physicalLabel F d (enroll F d p) = fixedPolynomial G d p := by
  unfold physicalLabel
  let q := enroll F d p
  apply fixed_enroll F; exact (show enroll F d ((F.level d).coords.symm ((freeTable F).representative d q)) = q by change (freeTable F).project d ((F.level d).coords ((F.level d).coords.symm _)) = q; rw [LinearEquiv.apply_symm_apply]; exact Table.rep ..)
lemma physical_unit (d : ℕ) : physicalLabel F d ((Maxwell.freeTable F).unit d) = Labels.unit G d := by
  rw [show (Maxwell.freeTable F).unit d = _ from Eq.symm (FreeStress.pin_unit F d), show FreeStress.embed F d = enroll F d from rfl,embed_round]
  exact fixed_unit
lemma physical_real (p : (Maxwell.freeTable F).Field d) (H : (Maxwell.freeTable F).RealSpin) : physicalLabel F d ((Maxwell.freeTable F).conj H d p) = Labels.realBar ((physicalLabel F d) p) := by
  nth_rw 1 [← physical_round F p]; rw [enroll,FreeStress.conjugate_embed, show FreeStress.embed F d = enroll F d from rfl, embed_round, ← fixed_real]
  congr 1; exact Subtype.ext (flat_idem _)
lemma physical_ortho (s : Ortho) (p : (Maxwell.freeTable F).Field d) : physicalLabel F d (rideO F s d p) = Labels.tensor s ((physicalLabel F d) p) := by
  have he : rideO F s d p = enroll F d (Labels.tensor s ((physicalLabel F d) p)) := by
    have hp (Q : Label G d) : writes F d (enroll F d Q)=reduceEq Q.val := by
      rw [show enroll F d Q = (freeTable F).project d ((F.level d).coords Q) from rfl, writes_project]; change observable G d (_) = _
      exact congrArg (fun q : Label G d => reduceEq q.val) ((F.level d).coords.symm_apply_apply Q)
    have hpol := hp (physicalLabel F d p); rw [physical_round] at hpol
    apply writes_inj; rw [show ∀ q, rideO F s d q=ride F s d q from fun _ => rfl,ride_at,hpol,hp]
    exact Eq.symm (watch_rot ..)
  rw [he,embed_round,←fixed_ortho]; exact congrArg _ (Subtype.ext (flat_idem _))
lemma physical_inclusion {W : DiffPlan (Maxwell.freeTable F)} (hW : W.Inclusions (Maxwell.freeTable F)) (w : d≤e) (p : (Maxwell.freeTable F).Field d) : physicalLabel F e (W.rise w p) = Labels.raiseLabel G w ((physicalLabel F d) p) := by
  conv_lhs => rw [← physical_round F p,enroll,FreeStress.rise_embed F _ hW, ← enroll,embed_round]
  rw [fixed_includes]; exact congrArg _ (Subtype.ext (flat_idem _))
end YM.Pert.RawLabels
