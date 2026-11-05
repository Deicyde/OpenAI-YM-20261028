import YM.Extra.MULTISOURCE_TRAJECTORIES.Signals
/-!
# Literal C.O insertions and their replicated or signed copies

Allow an independent permitted weight, input point and cutoff pull (including
optional value conjugation for tilings) in each slot. Use the stored factory's
one terminal map at this cutoff. Physical equality and transported full top
stencil, including inversely oriented edges; no auxiliary smoothness/linearity
assumption on a re-tuned label field. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Lattice Wilson RG Source Labels Function
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {V : Type} {N p : ℕ} {n : Side}

def pullM (s : Signed) (b : Site n) (M : Field G n) : Field G n := fun e => readM ((posDir e.2).rotate s) (affine s b e.1) M
lemma pullM_smooth (s : Signed) (b : Site n) : ContDiff ℝ ∞ (pullM (G:=G) s b) :=
  contDiff_pi.mpr fun _ => readM_smooth _ _
lemma field_pull (s : Signed) (b : Site n) (U : Config G n) : pullM s b (matrixField U) = matrixField (pull s b U) := by
  funext i; dsimp only [pullM, readM, matrixField, comp_apply, pull, Step.read]; split <;> rfl

def atom {S : Finset Cover} (o : Site n) (A : Field G n) (k : Source.Index G S) :=
  let z := (expandAt o A k.1.val) k.2.1 k.2.2.1
  if k.2.2.2 then star z else z

lemma atom_smooth {S : Finset Cover} (o : Site n) (k : Source.Index G S) : ContDiff ℝ ∞ (fun A => atom o A k) := by
  let i := k.2.1; let j := k.2.2.1
  have h : ContDiff ℝ ∞ (fun A : Field G n => (expandAt o A k.1.val) i j) :=
    (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff.comp (contDiff_apply ℝ _ _)
  unfold atom; split
  · exact (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp h
  exact h

private lemma polynomial_smooth {S : Finset Cover} (o : Site n) (Q : Source.Formula G S) :
    ContDiff ℝ ∞ (fun A : Field G n => MvPolynomial.aeval (atom o A) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using! (contDiff_const (𝕜:=ℝ) (E:=Field G n) (n:=∞) (c:=c))
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul,MvPolynomial.aeval_X]; exact hp.mul (atom_smooth o i)

def observable (C : Family G) (N p : ℕ) {d : ℕ} (z : C.label d) (o : Site (C.side N p)) (A : Field G (C.side N p)) : ℂ :=
  ((C.S.a N : ℂ)^d)⁻¹ * MvPolynomial.aeval (atom o A) ((C.localSection d).evalC (((C.labels.level d).scaled
    (C.path.levels.clock.threshold N)⁻¹) ((C.factory d N p).terminal.symm z)))
lemma observable_smooth (C : Family G) (N p d : ℕ) (z : C.label d) (o : Site (C.side N p)) :
    ContDiff ℝ ∞ (observable C N p z o) := contDiff_const.mul (polynomial_smooth o _)
lemma observable_field (C : Family G) (N p d : ℕ) (z : C.label d) (o : Site (C.side N p)) (U) :
    observable C N p z o (matrixField U) = C.O N p z o U := rfl

structure Probes (C : Family G) (V : Type) (N p : ℕ) where
  d : V → ℕ
  z (i : V) : C.label (d i)
  point : V → Site (C.side N p)
  signed : V → Signed
  offset : V → Site (C.side N p)
  reflect : V → Prop

private lemma affine_step (s : Signed) (b : Site n) (e : Edge (Site n)) :
    affine s b (e.1 + Lattice.step e.2) = affine s b e.1 + ((posDir e.2).rotate s).vec := by
  rw [Step.vec_rotate,affine,affine,s.act_add,Step.vec_pos]; abel

private lemma pull_gauge_eq (s : Signed) (b : Site n) (k : Site n → G.El) (U : Config G n) :
    pull s b (gauge k U) = gauge (k ∘ affine s b) (pull s b U) := by
  funext e
  unfold Lattice.gauge pull
  simp only [comp_apply]; rw [affine_step]
  exact Step.gauge_read ..

private lemma agrees_pull (s : Signed) (b : Site n) (S : Support n) (U W : Config G n)
    (h : Agrees (S.image (affine s b)) U W) : Agrees S (pull s b U) (pull s b W) := by
  intro e hi hj
  have h₁ := Finset.mem_image_of_mem (affine s b) hi
  have h₂ := Finset.mem_image_of_mem (affine s b) hj
  rw [affine_step] at h₂
  let D := (posDir e.2).rotate s
  change D.read U _ = D.read W _
  have he : U (D.used (affine s b e.1))= W (D.used (affine s b e.1)) := by
    change affine s b e.1 + D.vec ∈ _ at h₂
    unfold Step.used
    split
    next ht => exact h _ (by simpa [sub_eq_add_neg,Step.vec,ht] using h₂) (by simpa using h₁)
    next ht => exact h _ h₁ (by simpa [Step.vec,ht] using h₂)
  unfold Step.read; rw [he]

namespace Probes
variable (Q : Probes C V N p)

def place (i : V) := affine (Q.signed i) (Q.offset i) (Q.point i)
def footprint (i : V) : Support (C.side N p) := ((C.localSection (Q.d i)).footprint (Q.point i)).image (affine (Q.signed i) (Q.offset i))

def eval (i : V) (U : Config G (C.side N p)) :=
    let x := C.O N p (Q.z i) (Q.point i) (pull (Q.signed i) (Q.offset i) U)
    if Q.reflect i then star x else x

def toInsertions : Insertions C.path V N p where
  load := Q.d
  field i A :=
    let x := observable C N p (Q.z i) (Q.point i) (pullM (Q.signed i) (Q.offset i) A)
    if Q.reflect i then star x else x
  smooth i := by
    let h := (observable_smooth C N p (Q.d i) (Q.z i) (Q.point i)).comp (pullM_smooth (Q.signed i) (Q.offset i))
    dsimp only; split
    · exact (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp h
    exact h
lemma physical (i : V) : Q.toInsertions.uses i = Q.eval i := by funext x; simp [eval,Insertions.uses,toInsertions,field_pull,observable_field]
lemma symmetric (h : C.Makes) : Q.toInsertions.Symmetric := by
  intro i; rw [Q.physical]; intro k U
  simp only [eval,pull_gauge_eq, C.invariant h N p _ (Q.z i) (Q.point i) (k ∘ affine (Q.signed i) (Q.offset i))]
lemma visible (i : V) : LocalOn (Q.footprint i) (Q.eval i) := by
  intro U W h
  rw [eval,eval,C.localO N p (Q.d i) _ (Q.point i) _ _ (agrees_pull _ _ _ U W h)]
lemma marked (h : C.Makes) (i : V) : Q.place i ∈ Q.footprint i :=
    Finset.mem_image_of_mem _ (by
      simpa only [SectionData.footprint, map_zero, zero_add] using Finset.mem_image_of_mem (fun x => wrap (C.side N p) x + Q.point i) (h.sections (Q.d i)).anchored)

/-- The precise Story array (actual star copies, common label). -/
def center {d m : ℕ} (C : Family G) (p : ℕ) (h : m≤N) (v : C.label d) : Probes C (Site (C.side m p)) N p where
  d _ := d
  z _ := v
  point _ := 0
  signed := (Cells.center C.S p h 0).omega
  offset := (Cells.center C.S p h 0).translateBy
  reflect := (Cells.center C.S p h 0).hand

lemma center_eq {d m : ℕ} (C : Family G) (p : ℕ) (h : m≤N) (v : C.label d) (i : Site (C.side m p)) :
    (center C p h v).eval i = (Cells.center C.S p h 0).copy i (C.O N p (d:=d) v 0) := rfl
lemma center_place {d m : ℕ} (C : Family G) (p : ℕ) (h : m≤N) (v : C.label d) (i : Site (C.side m p)) :
    (center C p h v).place i = Mix.camp C p m N i := by
  rw [Mix.camp,dif_pos h]; exact (Cells.copy_home C.S h 0 i).trans (zero_add _)
end Probes
end YM.Extra.Trajectories
