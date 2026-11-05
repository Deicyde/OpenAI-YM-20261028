import YM.Push.FINITE_DETECTION.Signed
import YM.Push.FINITE_DETECTION.TwoPoint


/-! The `RealSpin` port needed for using the free pair probes in columns,
on the Maxwell comparator itself. This is not the full RFree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Free.Hyper
open Function Set Filter Maxwell Wick
open scoped BigOperators
variable {G : Gauge} {d n : ℕ}

def movedVar (s : Signed) (a : Slot G) := encode (aspect s (coordinateLeg a))

def changed (s : Signed) : WickPol G →ₐ[ℂ] WickPol G := MvPolynomial.aeval (fun a => ordinary G (movedVar s a))
def pullTower (s : Signed) (A : TaylorTower G) : TaylorTower G := fun i => turn s (A i)
lemma changed_at (s : Signed) (A : TaylorTower G) (p : WickPol G) : probe A (changed s p) = probe (pullTower s A) p := by
  suffices (probe A).comp (changed s) = probe (pullTower s A) by exact DFunLike.congr_fun this p
  ext a
  simp only [changed,movedVar, AlgHom.comp_apply,MvPolynomial.aeval_X,at_encode]; simp [probe,aspect,coordinateLeg,coord,pullTower]

lemma changed_observable (s : Signed) (v : Labels.Label G d) :
    observable G d (Labels.tensor s.ortho v) = changed s (observable G d v) := by
  apply equalPol; intro A
  rw [changed_at]; change probe A (reduceEq (Labels.rotated s.ortho v.val)) = probe _ (reduceEq v.val)
  rw [jet_value,jet_value,Labels.rotated,Labels.eval_changed]; congr 2; exact funext fun i => (gaugeTurn s (A i)).symm
lemma real_observable (v : Labels.Label G d) : observable G d (Labels.realBar v) = barred (observable G d v) := by
  apply equalPol; intro A
  rw [eval_bar]; change probe A (reduceEq (Labels.conjPol _)) = star (probe A (reduceEq _))
  rw [jet_value,jet_value,Labels.conj_value]; rfl

lemma moved_cov (s : Signed) (a b : Slot G) {x y : E4} (h : x ≠ y) :
    tensorMatrix (fun i j => entry i j (Rₛ s x) (Rₛ s y)) (movedVar s a) (movedVar s b) = entry a b x y := by
  have he : Rₛ s x - Rₛ s y ∈ away := sub_ne_zero.mpr ((Rₛ s).injective.ne h)
  simp_rw [movedVar,entry,pairing_encode_at _ _ he]
  change (legKernel _ _ (Rₛ s x - Rₛ s y) : ℂ) = _; rw [← map_sub,leg_invariant _ _ _ (sub_ne_zero.mpr h)]

lemma moment_moves (s : Signed) {x : Points n} (hx : x ∈ conf n) :
    (moment G (Points.move s.ortho x)).compLinearMap (fun _ => (changed s).toLinearMap) = moment G x := by
  refine Module.Basis.ext_multilinear (fun _ => monBasis G) fun W => ?_
  change moment G _ (fun i => changed s ((monBasis G) (W i))) = _
  rw [moment_basis]; simp_rw [← stationed_powers, map_prod, changed,MvPolynomial.aeval_X]
  exact (linear_substitution (W := W) (fun a => movedVar s a.probe) _).trans <| Finset.sum_congr rfl fun P _ => Finset.prod_congr rfl
    fun a _ => moved_cov s _ _ (x := x a.label) (y := x (Occ.partner P a).label) ((show Injective x.ofLp from hx).ne (Occ.different P a).symm)

lemma expands (x : Points n) (p : Fin n → WickPol G) (t : Fin n → Finset (Slot G →₀ ℕ))
    (a : Fin n → (Slot G →₀ ℕ) → ℂ) (h : ∀ i, p i = ∑ j ∈ t i, a i j • monBasis G j) :
    moment G x p = ∑ f ∈ Fintype.piFinset t, (∏ i, a i (f i)) * monomial x f := by
  rw [funext h,MultilinearMap.map_sum_finset (moment G x) (fun i j => a i j • monBasis G j) t]; refine Finset.sum_congr rfl fun f _ => ?_
  exact ((moment G x).map_smul_univ _ (fun i => monBasis G (f i))).trans (congr_arg _ (moment_basis f x))
lemma moment_conj (x : Points n) (v : Fin n → WickPol G) : moment G x (fun i => barred (v i)) = star (moment G x v) := by
  classical
  rw [expands x v _ _ (fun i => as_coeff (v i)),expands x _ _ _ (fun i => barred_sum (v i))]; apply Eq.symm
  simp only [star_sum,star_mul', star_prod]; refine Finset.sum_congr rfl fun f _ => congr_arg _ ?_
  simp [monomial,Occ.graph,Occ.edge,entry]

lemma decodesAt (F : Labels.Frames G) (p : (standard F).Token) :
    let label (p : (standard F).Token) := (F.level p.1).coords.symm p.2
    let w (p : (standard F).Token) := observable G p.1 (label p)
    w ((standard F).conjugate p) = barred (w p) ∧ ∀ s, w ((standard F).move s p) = changed s (w p) := by
  intro label w
  constructor
  · rw [← real_observable]; change observable G p.1 ((F.level _).coords.symm (star p.2)) = _
    rw [show (F.level p.1).coords.symm (star p.2) = _ from ((standard F).geom_conj p.1 p.2).symm]; rfl
  intro s; rw [← changed_observable]; change observable G p.1 ((F.level p.1).coords.symm ((F.level p.1).act s.ortho p.2)) = _
  congr 1; apply (F.level _).coords.injective; rw [LinearEquiv.apply_symm_apply,← (F.level _).act_coords]; unfold label; rw [LinearEquiv.apply_symm_apply]

theorem comparatorSpin (F : Labels.Frames G) : (freeTable F).RealSpin := by
  let w (p : (standard F).Token) := observable G p.1 ((F.level _).coords.symm p.2)
  constructor
  · intro n s x hx v
    change moment G _ _ = _
    change moment G (Points.move s.ortho x) (fun i => w ((standard F).move s (v i))) = _
    simp_rw [show ∀ p, w ((standard F).move s p) = _ from fun p => (decodesAt F p).2 s]; exact MultilinearMap.congr_fun (moment_moves s hx) (fun i => w (v i))
  intro n x hx v
  change moment G x (fun i => w ((standard F).conjugate (v i))) = _
  simp_rw [show ∀ p, w ((standard F).conjugate p) = _ from fun p => (decodesAt F p).1]; exact moment_conj x (fun i => w (v i))
end YM.Push.FiniteDetection.Free.Hyper
