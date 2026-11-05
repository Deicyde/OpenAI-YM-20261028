import YM.Extra.SOURCE_HISTORIES.Play
import YM.Extra.SOURCE_HISTORIES.Stock
import YM.Extra.SOURCE_HISTORIES.Unit

/-!
# Local inputs STILL required

The `AtomStep` hypothesis below is a precise local PUSH_LOCAL_SPLITTING
socket (not supplied in this checkout).

It is **only** a one-block estimate,
on ONE column basis address or ONE remainder address at a time.

Cf.

Uses this history's actual vacuum exponent and
unmarked normalization, kernel with shared choices and probability Haar
conventions, its k,P,cover size and support exponent on input AND output,
its integral push on true representations, including winding entries and
masks with stores and exclusion predicates.

Use possibly bigger pre prices to
account for every signed orientation; the leading prediction Btri socket here
needs uniform scaled estimates below & covariance (at origin); no claim that
deriving these estimates is done or is automatic from `History.Selected` or
`Next.Foundations.split_germ`.

(That readout is one ingredient on the PUSH
producer side.)

Request on the **same** anchor at origin in the centered blocking step. A
local covariant splitter controlling the orbit of each output with these
estimates would suffice. Don't even need a linear choice in the payloads for
our theorem; will prove linear choices for the histories. Sectored-label or
higher-regularity variants behind producing these TRUE `Format`/`remBound`
proofs are the local producer's responsibility, not free variables here. In
particular if a source needs tail/enlargement operations the **output** still
has to have paid the very same budget the next step consumes. The supposition
is speculative even for a Bolt, but mathematical and independently testable
(e.g. on a single remainder address).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge} {d : ℕ}

/-- The regular atom is the FULL cylinder incl its support; here written
with its mask for density use but the derivatives are before the mask. -/
def salary (R : Rep G n) (b : Support n) (f : Config G n → ℂ) (U : Config G n) :=
    (R.eval U:ℂ) * masked R.p.threshold b f U

/-- Forced input atom with its ACTUAL gas profile and multiplier. -/
def fare (R : Rep G n) (i : ℕ) (f : Config G n → ℂ) (U : Config G n) :=
    (Real.exp (R.exponent U):ℂ) * (f U * dressed R i U)

/-- Require the honest null reading. -/
structure RegFit (R : Rep G n) (o : Site n) (d : ℕ) (A : Hol G) (b : Support n) (f : Config G n → ℂ) : Prop where
  smooth : R.p.Regular b f
  anchor : o∈b
  unit_null : f 1=0
  proj : Nonwrapping b o → A.PiVanish d o f

structure Heading (F : Labels.Frame G d) where
  map : F.Coeff ≃ₗ[ℂ] F.Coeff
  core_comm x : map (F.core x) = F.core (map x)
  covariant x m : map (Motion.patch F m x)=Motion.patch F m (map x)
  unit : map F.e0 = F.e0

namespace Heading
variable {F : Labels.Frame G d} (T : Heading F)

/-- Note engineering factor *not* the slot-factor metric. -/
def leads (L : Side) : F.Coeff →ₗ[ℂ] F.Coeff :=
 T.map.toLinearMap.comp ({
    toFun x := vowel F L x
    map_add' x y := by ext; simp [vowel,mul_add]
    map_smul' x y := by ext; simp [vowel]; ring } : F.Coeff →ₗ[ℂ] F.Coeff)

lemma coheres (L : Side) (m : Motion) (v : F.Coeff) : T.leads L (Motion.patch F m v)=Motion.patch F m (T.leads L v) := by
  change T.map (vowel F L _) = Motion.patch F m (T.map _)
  rw [← patch_vowel, T.covariant]; rfl
end Heading

variable {F : Labels.Frame G d} (B : SectionData F) (H : History G) (N p m : ℕ)
variable (A : Hol G)

/-- Fine-to-coarse one-block claim on a single explicitly given input value
with a specified predicted primary lead; error measured in actual coarse
threshold-weighted coordinates. Also give the column versions at every
signed orientation and ordinary conjugation; may be different presentations
on SAME R, x the correspondingly transformed actual readout. -/
def PaidAtom (f : Config G (H.S.side (m+1) p) → ℂ) (lead : F.Coeff) (c t : ℝ) : Prop :=
    let R := H.rep N p m
    ∃ X : F.Coeff, ∀ y : Motion, F.coeffSize (Motion.patch F y X - Motion.patch F y lead) ≤ c ∧
      ∃ P : Coefficient F (H.S.side m p), P.x=Motion.patch F y X ∧ P.Format 0 A R ∧
        P.remBound 0 R (Real.sqrt (H.levels.clock.forcedAllowance m)) t ∧
          P.density 0 B R = dance y (blast H N p m d f)

/-- η here pays BOTH epsilon & q_D, sufficiently small after choosing the
ratio and buying actual delays (numerical target specified at client). C is
the uniform cost anticipating also signed transforms, not growing with p or L
at fixed stage/request. Applied to all nonzero price queries and also zero. -/
structure AtomStep (T : Heading F) (C η : ℝ) : Prop where
  main (i : F.Index) (h : i ≠ 0) :
    let R := H.rep N p (m+1)
    let v := Size.axis F i
    PaidAtom B H N p m A ((primary 0 v).density 0 B R) (T.leads (H.S.block m) v)
      (η * F.coeffSize (F.core v)) (C * F.coeffSize (vowel F (H.S.block m) (F.core v)))
  regular (f : Config G (H.S.side (m+1) p) → ℂ) (b : Support (H.S.side (m+1) p)) (c : ℝ) :
    let R := H.rep N p (m+1)
    let u := η * R.p.mass b c
    RegFit R 0 d A b f → R.p.supBounds 0 b f c → PaidAtom B H N p m A (salary R b f) 0 u u
  forced (f : Config G (H.S.side (m+1) p) → ℂ) (i : ℕ) (c : ℝ) :
    let R := H.rep N p (m+1)
    let u := η * ((R.p.mass (R.activities.forced i).support c) / Real.sqrt (H.levels.clock.forcedAllowance (m+1)))
    SlotFit R 0 i f → 0 ≤ c → (∀ U, ‖f U‖ ≤ c) → PaidAtom B H N p m A (fare R i f) 0 u u
  map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v

/-- Unit atom itself needs NO assumption. -/
theorem paid_one (T : Heading F) (C η : ℝ) (h : H.Selected) (hm : m<N) :
    PaidAtom B H N p m A ((primary 0 F.e0).density 0 B (H.rep N p (m+1))) (T.leads (H.S.block m) F.e0)
      (η * F.coeffSize (F.core F.e0)) (C * F.coeffSize (vowel F (H.S.block m) (F.core F.e0))) := by
  let L := H.S.block m
  let x := (L.val:ℂ)^d
  have hx : T.leads L F.e0=x • F.e0 := by
    change T.map (vowel F L F.e0) = _
    rw [show vowel F L F.e0 = x • F.e0 by
      funext i
      by_cases hi : i=0
      · rw [hi]; simp [x,vowel,F.zero_degree]
      simp [vowel,Frame.e0,Pi.single_eq_of_ne hi],map_smul,T.unit]
  have ht (z : Motion) : scalar z x = x := by unfold x scalar; split <;> simp
  rw [Size.unit_core, show vowel F (H.S.block m) 0 = 0 from funext fun i => by simp [vowel],
    show F.coeffSize 0=0 by simp [Frame.coeffSize], mul_zero,mul_zero]
  rw [show T.leads (H.S.block m) F.e0 = _ from hx]
  refine ⟨x • F.e0,fun z => ⟨by simp [Frame.coeffSize],?_⟩⟩
  have he : 0 < Real.sqrt (H.levels.clock.forcedAllowance m) := Real.sqrt_pos.2 (forcedPos ..)
  refine ⟨primary 0 (x • F.e0),by rw [patch_smul,patch_unit,ht]; rfl,primary_format _,primary_rem _ he,?_⟩
  have hz : blast H N p m d ((primary 0 F.e0).density 0 B (H.rep N p (m+1)))=x • liftVac H N p m := by
    rw [unit_density]; exact blast_vac H N p m d h hm
  rw [hz,show primary (0:Site (H.S.side m p)) (x • F.e0)=stretch x (primary 0 F.e0) by simp [stretch,primary]]
  funext U
  simp only [stretch_density, unit_density, dance, Pi.smul_apply, smul_eq_mul, scalar_mul, ht]
  rw [← dance, vac_dance H N p m h hm.le]; rfl

end YM.Extra.Histories
