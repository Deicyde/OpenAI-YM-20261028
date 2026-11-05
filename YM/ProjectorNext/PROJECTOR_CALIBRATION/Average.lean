import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters
import YM.Push.CUTOFF_PROJECTORS.Bank
import YM.Push.CUTOFF_PROJECTORS.Signed

/-! # Preserve top margin when installing via signed average instead

This concerns a *cutoff initialization*, not how to transform or even match
ANY remainder through a blocking step. No assertions about `Packet.Oriented`
at reference from the symmetrization at N. Orthogonality of the basis F isn't
needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Labels Function Filter Next.Foundations Push Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)

/-- Conjugate and average triangular models (the `H` action convention of Frame). -/
def steer (s : Signed) : equationSpace F →ₗ[ℂ] equationSpace F :=
    ((turn F s).comp (equationSpace F).subtype).codRestrict _ (fun v => equation_oriented F s v v.property)

def swept (T : Model F) (s : Signed) : Model F :=
    (turn F s).toContinuousLinearMap.comp (T.comp (steer F s⁻¹).toContinuousLinearMap)

def share := ((Fintype.card Signed:ℕ):ℂ)⁻¹

def circle (T : Model F) : Model F := share • ∑ s,swept F T s

private lemma preserves (s : Signed) (x : F.Coeff) (i : F.Index) (h : ∀ j : F.Index, (F.grades j).1=(F.grades i).1 → x j = 0) : turn F s x i = 0 := by
  have he : x = ∑ j, x j • F.coords (F.basis j) := by funext k; simp [Finset.sum_apply,Pi.single_apply]
  nth_rw 1 [he,map_sum,Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases ht : (F.grades j).1=(F.grades i).1
  · simp [h j ht]
  rw [map_smul,Pi.smul_apply]
  unfold turn; rw [F.act_coords,F.power_coefficient i (m:=F.grades j) (fun e => ht (congr_arg Prod.fst e)),smul_zero] -- m implicit 
  have hs := gradePart_mem (F.grades j) (tensor (Signed.inclusionO s) (F.basis j)); rwa [gradePart_turn,gradePart_self _ _ (F.pure j)] at hs

theorem circle_triangle (T : Model F) (ht : triangular T) : triangular (circle F T) := by
  intro x i h
  have he (s : Signed) : swept F T s x i = x.val i := by
    let y := steer F s⁻¹ x
    have ha : turn F s y.val=x.val := by change turn F s (turn F s⁻¹ _) = _; rw [← turn_mul,mul_inv_cancel,turn_one]; rfl
    have hz : turn F s (T y - y.val) i = 0 := by
      refine preserves F s _ i (fun j hj => ?_)
      have hv : T y j = y.val j := ht y j (fun b hb => preserves F s⁻¹ _ b fun a hh => h a (by rw [hh,← hj]; exact hb))
      simp [hv]
    rw [map_sub,ha, Pi.sub_apply, sub_eq_zero] at hz; exact hz
  unfold circle
  rw [smul_apply,Pi.smul_apply]
  rw [sum_apply,Finset.sum_apply]; simp_rw [he]
  simp [share,nsmul_eq_mul] -- issue Finite card >0

-- compatibility with actuator Φ etc uses H and jet reorder. Lens transformations at finite bank.
def tilt (s : Signed) (i : Lens G d) : Lens G d :=
  (changedJet (fun _ => Taylor.turn (s.ortho⁻¹)) i.1,i.2)

lemma steering (s : Signed) (i : Lens G d) (x : F.Coeff) :
    probe F i (turn F s x)=probe F (tilt s i) x := by
  rw [probe_eq,probe_eq]
  obtain ⟨p,rfl⟩ := F.coords.surjective x
  change iteratedDeriv i.2.val _ _ = iteratedDeriv i.2.val _ _
  simp_rw [turn,show Signed.inclusionO s=s.ortho from rfl,F.act_coords,F.coords.symm_apply_apply]
  refine congr_arg (fun f : ℝ → ℂ => iteratedDeriv i.2.val f 0) ?_
  funext t
  change Labels.read _ (changed (fun _ => Taylor.turn s.ortho⁻¹) _) = _
  rw [eval_changed]; apply congr_arg (fun J : Jet G => Labels.read J p.val)
  funext j; exact map_smul (Taylor.turn _ (j:=j)) _ _

lemma bills_relit {F : Labels.Frame G d} (T : Model F) (i : Lens G d) (x : equationSpace F) : probe F i (circle F T x) = share * ∑ s : Signed, probe F (tilt s i) (T (steer F s⁻¹ x)) := by
  unfold circle; rw [smul_apply]
  rw [sum_apply,map_smul,map_sum]
  simp_rw [swept]; change _ • ∑ s : Signed,probe F i (turn F s _) = share * ∑ s : Signed,_
  simp_rw [steering]; rfl

end YM.ProjectorNext.Calibration
