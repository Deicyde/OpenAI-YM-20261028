import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# Signed frames for the equation projectors

Check the domain of parameters really carries the action booked at this
point of E. Use only H and ordinary conjugation on coefficients. If the
origin readout map supplied from the cutoff is equivariant, so is our step
projector, with no edge cases on ranks. Not identifying the physical O(4)
action on quotients from this finite statement!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Function Filter Maxwell Labels Source Analysis Tensor
open scoped Topology BigOperators ContDiff

variable {G : Gauge} {j d N p : ℕ} (F : Labels.Frame G d)

section AxisAction

private def sgn (s : Signed) (a : Axis) : ℝ := if s.flip a then -1 else 1

private abbrev sym (s : Signed) := Signed.inclusionO s

private lemma sym_basis (s : Signed) (a : Axis) :
    Ortho.motion (sym s)⁻¹ (basis (s.perm a)) = sgn s a • basis a := by
  rw [← map_inv]
  apply PiLp.ext
  intro i
  rw [Ortho.motion_at, Ortho.move, M4.move_basis]
  change (s⁻¹).matrix _ _ = _
  by_cases h : i = a
  · subst i
    cases hs : s.flip a <;> simp [hs,sgn,Signed.matrix_at]
  cases hs : s.flip a <;> simp [hs,sgn,Signed.matrix_at,h,Ne.symm h]

private lemma perm_jet (s : Signed) (A : Taylor G j) (i : Axis) :
    (Taylor.turn (sym s) A).value (s.perm i) = fun x => sgn s i • A.value i (Ortho.motion (sym s)⁻¹ x) := by
  ext1 x
  rw [Taylor.turn_value]
  rw [Finset.sum_eq_single i]
  · simp only [Ortho.motion_at]
    change s.matrix _ _ • _ = _
    simp only [Signed.matrix_at, ↓reduceIte, sgn]
  · intro b _ hb
    change s.matrix _ _ • _ = _
    simp [Signed.matrix_at,hb]
  · simp

private lemma perm_grad (s : Signed) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (i : Axis) (f : E4 → Z) (hf : Differentiable ℝ f) (c : ℝ) (x : E4) :
    grad (s.perm i) (fun x => c • f (Ortho.motion (sym s)⁻¹ x)) x =
      (c * sgn s i) • grad i f (Ortho.motion (sym s)⁻¹ x) := by
  let L := (Ortho.motion (sym s)⁻¹).toContinuousLinearMap
  unfold grad D
  change fderiv ℝ (c • (f ∘ L)) x _ = (c * sgn s i) • fderiv ℝ f (L x) _
  rw [fderiv_const_smul ((hf.comp L.differentiable) x), fderiv_comp x (hf _) L.differentiableAt,
    ContinuousLinearMap.fderiv]
  change c • fderiv ℝ f (L x) (Ortho.motion (sym s)⁻¹ (basis _)) = _
  rw [sym_basis, map_smul, smul_smul]

private lemma perm_curl (s : Signed) (A : Taylor G j) (a b : Axis) :
    diagonal (takeCurl (Taylor.turn (sym s) A) (s.perm a) (s.perm b)) = fun x =>
    (sgn s a * sgn s b) • diagonal (takeCurl A a b) (Ortho.motion (sym s)⁻¹ x) := by
  ext1 x
  have he i : Differentiable ℝ (A.value i) := (diag_smooth (A.val i) ∞).differentiable (by simp)
  rw [takeCurl_diag, takeCurl_diag]
  simp only [perm_jet, Pi.sub_apply, perm_grad s _ _ (he _), smul_sub, mul_comm (sgn s b)]

private lemma curl_turned (s : Signed) (x : Shell G j) :
    takeCurl (Taylor.turn (sym s) (gaugeJet x)) ∈ onShell G.Color j := by
  let A := gaugeJet x
  refine ⟨closedCurl _,?_⟩
  change ∀ b z, ∑ a : Axis, grad a (diagonal (takeCurl (Taylor.turn (sym s) A) a b)) z = 0
  intro b z
  obtain ⟨i,rfl⟩ := s.perm.surjective b
  rw [← Equiv.sum_comp s.perm]
  have he a : grad (s.perm a) (diagonal (takeCurl (Taylor.turn (sym s) A) (s.perm a) (s.perm i))) z =
      sgn s i • grad a (diagonal (x.val a i)) (Ortho.motion (sym s)⁻¹ z) := by
    rw [perm_curl, show takeCurl A = x.val from match_leg x, perm_grad]
    · congr 1
      dsimp [sgn]; split_ifs <;> ring
    exact (diag_smooth _ ∞).differentiable (by simp)
  simp_rw [he]
  have hz : ∑ a, grad a (diagonal (x.val a i)) (Ortho.motion (sym s)⁻¹ z) = 0 := x.property.2 _ _
  rw [← Finset.smul_sum,hz,smul_zero]

theorem equation_oriented : oriented F (equationSpace F) := by
  intro s x hx
  rw [equation_iff] at hx ⊢
  intro X
  let u := F.coords.symm x
  have hu : F.coords.symm (turn F s x) = tensor (sym s) u := by simp [u,turn,Labels.Frame.act,sym]
  rw [hu]
  change read _ (rotated _ u.val) = 0
  rw [rotated, eval_changed, ← map_inv]
  let Y : TaylorTower G := fun j => ⟨takeCurl (Taylor.turn (sym s⁻¹) (gaugeJet (X j))), curl_turned s⁻¹ _⟩
  have he : changedJet (fun i => Taylor.turn (sym s⁻¹)) (fun i => gaugeJet (X i)) = fun i => gaugeJet (Y i) := by
    ext1 j
    apply potential.injective
    exact Subtype.ext (match_leg (Y j)).symm
  rw [he]; exact hx Y
end AxisAction

theorem equation_realForm : realForm F (equationSpace F) := by
  intro x hx
  rw [equation_iff] at hx ⊢
  intro X
  have he : F.coords.symm (star x) = realBar (F.coords.symm x) := F.coords.injective (by simp)
  rw [he]; change read _ (conjPol _) = _
  rw [conj_value, hx, star_zero]

namespace Packet
variable {C : Family G} (E : Packet C d N p)

/-- Optional equivariant origin-coordinate receipt for . This is
about `.chain (C.ref d)`, not assumed from the covariance of the primary
field factory. -/
structure Oriented : Prop where
  turns (s : Signed) (w : equationSpace (C.labels.level d)) :
    let F := C.labels.level d
    E.reference ⟨turn F s w, equation_oriented F s w w.2⟩ = turn F s (E.reference w)
  real (w : equationSpace (C.labels.level d)) :
    let F := C.labels.level d
    E.reference ⟨star w.val, equation_realForm F w w.2⟩ = star (E.reference w)

variable {E}




end Packet
end YM.Push.CutoffProjectors
