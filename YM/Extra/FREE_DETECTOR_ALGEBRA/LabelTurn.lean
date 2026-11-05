import YM.Extra.FREE_DETECTOR_ALGEBRA.Gaussian


set_option warningAsError false

/-! Check tensor actions on the actual invariant labels. Used before
trying to use the positive Gram (second slot must be an admitted field!). -/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j d : ℕ}

lemma takeTurn (s : Ortho) (P : Taylor G j) : takeCurl (Taylor.turn s P) = carry s (takeCurl P) := by
  ext1 i; ext1 m; ext1 v
  let w := fun l => mov s⁻¹ (v l)
  have hc (m i) : ((Taylor.turn s P).val m).curryLeft (basis i) v = ∑ a : Axis, ∑ b : Axis,
      s.val m a • s.val i b • (P.val a).curryLeft (basis b) w := by
    rw [ContinuousMultilinearMap.curryLeft_apply]
    let F (a : Axis) := s.val m a • ((P.val a).compContinuousLinearMap fun _ ↦ (Ortho.motion s⁻¹).toContinuousLinearMap)
    change (∑ a : Axis, F a) (Fin.cons (basis i) v) = _
    rw [sum_apply]
    apply Finset.sum_congr rfl; intro a _
    have ht : (fun k => mov s⁻¹ (Fin.cons (α:=fun _ : Fin (j+1) => E4) (basis i) v k)) = Fin.cons (α:=fun _ : Fin (j+1) => E4) (mov s⁻¹ (basis i)) w := by
      funext k; refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
    change s.val m a • P.val a (fun k => mov s⁻¹ (Fin.cons (α:=fun _ : Fin (j+1) => E4) (basis i) v k)) = _
    rw [ht,← ContinuousMultilinearMap.curryLeft_apply, mov_inv_decomp,_root_.map_sum,sum_apply, Finset.smul_sum]
    simp only [_root_.map_smul,smul_apply]
  let t := (↑(j+1:ℕ):ℝ)
  let l i m := (P.val m).curryLeft (basis i) w
  rw [carry_eval,bi_eval]
  simp only [takeCurl,smul_apply,sub_apply, hc]
  change t • ((∑ a : Axis, ∑ b : Axis, s.val m a • s.val i b • l b a) - ∑ a : Axis, ∑ b : Axis, s.val i a • s.val m b • l b a) =
    ∑ a : Axis, ∑ b : Axis, s.val i a • s.val m b • t • (l a b - l b a)
  rw [Finset.sum_comm (f := fun a b => s.val m a • s.val i b • l b a)]
  simp_rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  module

theorem radial_turn (s : Ortho) (Q : Sol G.Color j) : gaugeJet (G:=G) (solO s Q) = Taylor.turn s (gaugeJet Q) := by
  apply potential.injective
  apply Subtype.ext; change takeCurl _ = takeCurl _
  rw [takeTurn,match_leg,match_leg]; rfl

lemma watch_rot (P : Labels.Pol G) (s : Ortho) : reduceEq (rotated s P) = pullSol s (reduceEq P) := by
  apply equalPol; intro A
  rw [jet_value,rotated, Labels.eval_changed,pull_eval,jet_value]
  exact congr_arg (fun X => Labels.read X P) (funext fun i => (radial_turn s⁻¹ (A i)).symm)

lemma watch_bar (P : Labels.Pol G) : reduceEq (Labels.conjPol P) = barPol (reduceEq P) := by
  apply equalPol; intro A; rw [jet_value,Labels.conj_value,eval_bar,jet_value]

theorem observe_rot (P : Labels.Label G d) (s : Ortho) : observable G d (Labels.tensor s P)=pullSol s (observable G d P) := watch_rot _ s

theorem observe_bar (P : Labels.Label G d) : observable G d (Labels.realBar P)=barPol (observable G d P) := watch_bar _

def polish (F : Labels.Frames G) (d : ℕ) : (standard F).Ref d →ₗ[ℂ] WickPol G :=
    (shellSector G d).subtype.comp (snap F d)

lemma polish_conj (F : Labels.Frames G) (p : (standard F).Ref d) : polish F d (star p) = barPol (polish F d p) := by
  change observable G d (((standard F).coord d).coords.symm (star p)) = barPol (observable G d _)
  have he := (standard F).geom_conj d p; rw [← he,observe_bar]; rfl

lemma polish_act (F : Labels.Frames G) (p : (standard F).Ref d) (s : Ortho) : polish F d ((F.level d).act s p) = pullSol s (polish F d p) := by
  change observable G d ((F.level d).coords.symm ((F.level d).act s p)) = pullSol s (observable G d ((F.level d).coords.symm p))
  obtain ⟨p,rfl⟩ := (F.level d).coords.surjective p
  rw [Frame.act_coords, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,observe_rot]

lemma polish_unit (F : Labels.Frames G) (d : ℕ) : polish F d ((standard F).scalar d) = 1 := by
  have he : (standard F).scalar d = (F.level d).coords (Labels.unit G d) := by simp [standard,Register.scalar,Register.coord]; exact one_smul _ _
  rw [he]
  change observable G d ((F.level d).coords.symm _) = _
  rw [LinearEquiv.symm_apply_apply]; exact map_one reduceEq

/-- `freeTable` spins; from actual O covariance, not presuming a
correlator property from a Wightman reconstruction. -/
theorem table_spin (F : Labels.Frames G) : (freeTable F).RealSpin := by
  let L := standard F
  let f (p : L.Token) := polish F p.1 p.2
  constructor
  · intro n s x hx v
    change moment G (Points.move _ _) (fun i => f (L.move s (v i))) = moment G x (fun i => f (v i))
    have he (i) : f (L.move s (v i)) = pullSol s.ortho (f (v i)) := polish_act ..
    simp_rw [he]; exact wick_rotate s.ortho hx _
  intro n x hx v
  change moment G x (fun i => f (L.conjugate (v i))) = star (moment G x (fun i => f (v i)))
  have he (i) : f (L.conjugate (v i)) = barPol (f (v i)) := polish_conj ..
  simp_rw [he]; exact wick_bar hx _
end YM.Extra.FD
