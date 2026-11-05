import YM.Next.MULTISOURCE.Initialize
import YM.Next.MULTISOURCE.Times

/-!
# Single response already delivered; carry this in the local tangent request
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Single
open RG Wilson Lattice Function Filter Finset MeasureTheory Source Labels AxisShift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {d N j p : ℕ} (H : C.Makes) (v : C.label d)
include H

omit H in
lemma initialized (o : Site (C.side N p)) : one C N v o=(cache C v o).birth (C.path.rep N p N) := by simp only [one, dif_pos]

lemma one_credit (o : Site (C.side j p)) (hj : j<N) (he : C.ref d ≤ j)
    (hx : Maquette.room (C.localSection d) ≤ C.path.levels.clock.coverSize j) :
    Credit (C.path.rep N p j).p 0 (money C.path.levels j) {o}
      (one C N v o) (tariff C N p j v) := by
  unfold one; rw [dif_neg hj.ne, show ({o}: Finset (Site (C.side j p))) = roots o {0} by simp [roots]]
  exact funded o (origin_price H v he hj.le hx _)

lemma first_line (o : Site (C.side j p)) (hj : j≤N) (he : C.ref d ≤ j) :
    tangent (C.path.rep N p j) (one C N v o) =
      (coeff C N p j v).density 0 (C.localSection d) (C.path.rep N p j) ∘ translate o := by
  let P := C.path.rep N p j
  have hl := H.calibrated d N p (he.trans hj)
  by_cases hu : j=N
  · subst j; funext U
    rw [initialized,birth_tangent _ _ (H.wilson.represents N p N le_rfl).good.labels (cache_weight H o v),cache_full H o he]
    let M := C.factory d N p
    let c := M.terminal.symm v
    have Hf := hl.encode c (translate o U)
    change (P.eval U:ℂ)*(_*_)=(M.entries N c).density 0 _ P _
    rw [Hf]
    have e : (C.path.rep N p N).eval (translate o U) = P.eval U := congr_fun (chosen_shift H.wilson hj o) U
    rw [e]
    have hx : initial (C.localSection d) C.path N p c 0 (translate o U)= C.O N p v o U := calc
      _ = C.O N p v (0+o) U := C.translation 0 o v U
      _ = _ := by rw [zero_add]
    rw [hx]; ring
  unfold one; rw [dif_neg hu,transported hj H.wilson]
  rw [BranchOne.present (coeff C N p j v) _ _ (H.wilson.represents N p j hj).good (hl.cap j he hj _)]

lemma higher (o : Site (C.side j p)) (hj : j<N) (he : C.ref d ≤ j) :
    let S := C.path.levels.clock.op j p
    tangent (C.path.rep N p j) (one C N v o) =
      ((C.S.block j).val:ℂ)^d • S.push (C.path.β N p (j+1))
        (tangent (C.path.rep N p (j+1)) (one C (j:=j+1) N v (S.ratio.embed o))) := by
  intro S
  have ht : C.ref d ≤ j+1 := he.trans (Nat.le_succ _)
  rw [first_line H _ _ hj.le he, first_line H _ _ hj ht]
  obtain Hh := H.calibrated d N p (ht.trans hj)
  unfold S; rw [commute_tr, coeff, Hh.unnormalized j he hj]
  · rfl
  exact TransferData.density_int H.wilson Hh _ _ ht hj
end YM.Multi.Single
