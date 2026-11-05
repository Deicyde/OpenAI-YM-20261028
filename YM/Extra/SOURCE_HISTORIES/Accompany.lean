import YM.Extra.SOURCE_HISTORIES.Beside
import YM.Extra.SOURCE_HISTORIES.Song

/-!
# A downstream isolated difference step on PRINTED voices

Though AtomStep doesn't assume linearity on arbitrary
representations, we can rebase also a **single** new source/signed test
along the same columns and get cancellation estimates. Idea: clean its
current column first by the existing calibrated primaries, forming a
residual P at x=0; to any other label just keep the net `a+v` primary
(ON THE SAME addresses, hence an actual signed difference). Transport
this family one step by paying for P with only remainder queries (x=0,
no need to force the entire push to be that of a particular preceding
algorithm), plus for the primary by its known exact transfer. Then *clean*
again paying the additional merging cost below. There is a margin
available for this if local error meets the stronger numeric inequality. All choices common to this one test and its primary corrections; no
joint concurrence/paying of multiple-source estimates claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Relay
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G) (W : Worth) (M : Music F H N p)

structure Solo (F : Labels.Frame G d) (H : History G) (p i : ℕ) where
  a : F.Coeff -- added primary in top-bare coords, from retained Voice
  sil : Coefficient F (H.S.side i p)
  bill : ℝ

namespace Solo
variable {H N p} {i : ℕ} (R : Solo F H p i)

def bar (v : F.Coeff) := beside R.sil ((M.tone i).plays (R.a+v))

def cost (v : F.Coeff) := R.bill+(M.tone i).charge (R.a+v)
end Solo

structure Keyed (i) (Q : Solo F H p i) : Prop where
  format : Q.sil.Format 0 A (H.rep N p i)
  cost : Q.sil.remBound 0 (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)) Q.bill
  key : Q.sil.x = 0


lemma keys {i} {Q : Solo F H p i} (v) (h : Keyed H N p A i Q) (he : Heard B H N p A i (M.tone i)) :
    (Q.bar M v).x=(M.tone i).index (Q.a+v) ∧ (Q.bar M v).Format 0 A (H.rep N p i) ∧
      (Q.bar M v).remBound 0 (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)) (Q.cost M v) := by
  have ht := he.earns (Q.a+v)
  refine ⟨?_,presentation h.format h.cost ht.1 ht.2⟩
  rw [Solo.bar, reckon,h.key,zero_add,he.currents]

-- design companion alone
structure Answers (i : ℕ) (P : Solo F H p (i+1)) (Q : Solo F H p i) : Prop where
  tunes v : direction H W i F ((Q.bar M v).x) ((P.bar M v).x) (Q.cost M v) (P.cost M v)
  debt v : (Q.bar M v).density 0 B (H.rep N p i)=blast H N p i d ((P.bar M v).density 0 B (H.rep N p (i+1)))



end YM.Extra.Histories.Relay
