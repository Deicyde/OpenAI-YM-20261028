import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Scale
import YM.Next.FOUNDATIONS.SU2

/-!
# Inverting the calibration at the same actual reference

Two different matrices in this part of E! Packet.topEquation starts in the
*equation space*, has a positive margin for different costs, and even its
rank could be 0. It is NOT this weak-start source matrix. For calculation/
sufficient hypotheses on this E rather than assuming Bkpc see the local
cost modules. For simultaneous application with Packet see the consumers.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Function Lattice Wilson Labels RG Cells Source Filter Extraction
open Push.Corrected Push.CutoffProjectors
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {d m k N p : ℕ}

/-- Finite margin gate in the *source* calibration coordinates for this same
family (plus actual depth conditions). E is the read BEFORE taking `(g/t)^l`;
it reads a v at the **reference** (i.e. the primaryMatrix is already included
on the right). Extra `Commuting` for exact H bookkeeping; NOT inferred from a
near estimate.
-/
structure Contact (B : Series C) (E : Mat C d) (k N p : ℕ) : Prop where
  reaches : C.ref d ≤ B.depth k
  before : B.depth k ≤ N
  pays : Issue.Analyzed C d (B.depth k) N p E.toLinearMap
  moves : Commuting (C.labels.level d) E

private def ofBi (E : Mat C d) (h : Bijective E) : C.label d ≃L[ℂ] C.label d :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective E.toLinearMap h)

/-- `weak` is the E map itself where in use; `pitch` is the full diagonal
in (KCis). Use nice harmless invertible padding otherwise. -/
structure Reader (C : Family G) (d : ℕ) where
  weak : C.label d ≃L[ℂ] C.label d
  pitch : C.label d ≃L[ℂ] C.label d
  weak_move : Commuting (C.labels.level d) weak
  pitch_move : Commuting (C.labels.level d) pitch
  weak_zero : weak (C.refUnit d) = (C.labels.level d).e0
  pitch_zero : pitch (C.labels.level d).e0 = (C.labels.level d).e0

namespace Reader
variable {B : Series C} {E E' : Mat C d}

def whenFit (h : C.Makes) (H : Contact B E k N p) : Reader C d where
  weak := ofBi E (Issue.unique_ h H.reaches H.pays H.before)
  pitch := ofBi (dress B k N p) (dress_bijective B h H.before)
  weak_zero := H.pays.unit
  pitch_zero := (dress_signature B d k N p).1
  weak_move := by
    convert H.moves
    exact ContinuousLinearMap.ext fun _ => rfl
  pitch_move := by
    convert (dress_signature B d k N p).2
    exact ContinuousLinearMap.ext fun _ => rfl

@[simp] theorem fit_weak (h : C.Makes) (H : Contact B E k N p) :
    ((whenFit h H).weak : Mat C d) = E := ContinuousLinearMap.ext fun _ => rfl
@[simp] theorem fit_dose (h : C.Makes) (H : Contact B E k N p) :
    ((whenFit h H).pitch : Mat C d) = dress B k N p := ContinuousLinearMap.ext fun _ => rfl
@[simp] theorem fit_dose_inv (h : C.Makes) (H : Contact B E k N p) :
    ((whenFit h H).pitch.symm : Mat C d) = undress B k N p := by
  ext1 x
  let M := (whenFit h H).pitch
  obtain ⟨x,rfl⟩ := M.surjective x
  change M.symm (M x)= _
  rw [M.symm_apply_apply]
  exact (undress_dress B h H.before x).symm

variable (C d) in
/-- Because `S.a` is actual and positive, use a fixed scalar read at
unavailable (e.g. tiny) cutoffs. No calibration guarantee there. -/
def off : Reader C d :=
  let A := ((C.S.a (C.ref d):ℂ)^d)
  let L := A⁻¹ • ContinuousLinearMap.id ℂ (C.label d)
  have hA : A ≠ 0 := pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  have hi : Injective L := fun x y h => smul_right_injective _ (inv_ne_zero hA) (show A⁻¹ • x=A⁻¹ • y from h)
  { weak := ofBi L ⟨hi,LinearMap.surjective_of_injective (show Function.Injective L.toLinearMap from hi)⟩
    pitch := ContinuousLinearEquiv.refl ℂ _
    weak_zero := by
      change A⁻¹ • (A • (C.labels.level d).e0) = _
      rw [smul_smul, inv_mul_cancel₀ hA, one_smul]
    pitch_zero := rfl
    weak_move := by
      constructor
      · intro s x
        exact ((turn _ s).map_smul A⁻¹ x).symm
      intro x
      change A⁻¹ • star x = star (A⁻¹ • x)
      simp only [star_smul]; simp [A]
    pitch_move := ⟨fun _ _ => rfl, fun _ => rfl⟩ }

open scoped Classical in
def readTape (h : C.Makes) (B : Series C) (k N p : ℕ) (E : Mat C d) : Reader C d :=
  if ht : Contact B E k N p then whenFit h ht else off C d



variable (R : Reader C d)

def xi : C.label d ≃L[ℂ] C.label d := R.pitch.trans R.weak.symm

theorem xi_reads (v) : R.weak (R.xi v) = R.pitch v := R.weak.apply_symm_apply _



theorem identity_of_unit : R.xi (C.labels.level d).e0=C.refUnit d := by
  apply R.weak.injective
  rw [xi_reads, R.pitch_zero,R.weak_zero]

lemma inter : Commuting (C.labels.level d) R.xi := by
  constructor
  · intro s v
    apply R.weak.injective
    change R.weak (R.xi (turn _ s v))=R.weak (turn _ s (R.xi v))
    rw [R.xi_reads, show R.weak (turn _ s _)=_ from R.weak_move.signed s _,
      show R.pitch (turn _ s _)=_ from R.pitch_move.signed s v]
    exact congr_arg (turn _ s) (R.xi_reads v).symm
  intro v
  apply R.weak.injective
  change R.weak (R.xi (star v))=R.weak (star (R.xi v))
  rw [R.xi_reads, show R.weak (star _)=_ from R.weak_move.real _,
    show R.pitch (star _)=_ from R.pitch_move.real v]
  exact congr_arg star (R.xi_reads v).symm



structure Cost (c : ℝ) : Prop where
  pos : 0<c
  weak : ‖(R.weak : Mat C d)‖ ≤ c
  back : ‖(R.weak.symm : Mat C d)‖ ≤ c
  pitch : ‖(R.pitch : Mat C d)‖ ≤ c
  reset : ‖(R.pitch.symm : Mat C d)‖ ≤ c







variable {R} {S : Reader C d} {c : ℝ}
namespace Cost





end Cost


end Reader
end YM.Further.CorrectedLift
