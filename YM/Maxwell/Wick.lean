import YM.Analysis.Multilinear
import YM.Maxwell.Bilinear

/-!
# Free Maxwell Wick polynomials evaluated only on separated configurations

`correlation` acts on the actual polynomial labels (it restricts to shell and
invariant sector). `moment` on any Wick polynomial, useful algebraically and in detector proofs.
Both only use different insertions for pairings. Stars on reflected legs must be
supplied separately. No sign representation from any fermionic grading.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Wick
open Function Set Filter
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {n : ℕ}

abbrev Powers (G : Gauge) (n : ℕ) := Fin n → Slot G →₀ ℕ

def monBasis (G : Gauge) := MvPolynomial.basisMonomials (Slot G) ℂ

def entry (p q : Slot G) (x y : E4) : ℂ := (legKernel (coordinateLeg p) (coordinateLeg q) (x-y) : ℂ)

theorem entry_smooth (p q : Slot G) {x : E4 × E4} (h : x.1 ≠ x.2) :
    ContDiffAt ℝ ∞ (fun z : E4 × E4 => entry p q z.1 z.2) x  := by
  have hw : ContDiffAt ℝ ∞ (fun y : E4 × E4 => y.1-y.2) x := contDiffAt_fst.sub contDiffAt_snd
  have he := (kernel_smooth (coordinateLeg p) (coordinateLeg q) (sub_ne_zero.mpr h)).comp x hw
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x he

theorem entry_symmetric (p q : Slot G) {x y : E4} (h : x ≠ y) : entry p q x y = entry q p y x := by
  unfold entry
  rw [← neg_sub (a := x) (b := y)]
  exact congr_arg (fun x : ℝ => (x : ℂ)) (exchange (coordinateLeg p) (coordinateLeg q) (sub_ne_zero.mpr h))

/-- Individual occurrences/distinguishable copies. -/
def Occ (W : Powers G n) := {p : Fin n × Slot G × ℕ // p.2.2 < W p.1 p.2.1}

namespace Occ
variable {W : Powers G n}
def label (p : Occ W) : Fin n := Subtype.val p |>.1
def probe (p : Occ W) : Slot G := Subtype.val p |>.2.1
def index (p : Occ W) : ℕ := Subtype.val p |>.2.2

theorem legit (p : Occ W) : index p < W p.label p.probe := Subtype.property p

def atSlot (i : Fin n) (v : Slot G) (k : ℕ) (h : k < W i v) : Occ W := ⟨(i,v,k),h⟩

@[simp] theorem pos_at (i : Fin n) (v : Slot G) (k : ℕ) (h : k < W i v) : (atSlot i v k h).label = i := rfl
@[simp] theorem probe_at (i : Fin n) (v : Slot G) (k : ℕ) (h : k < W i v) : (atSlot i v k h).probe = v := rfl
@[simp] theorem index_at (i : Fin n) (v : Slot G) (k : ℕ) (h : k < W i v) : (atSlot i v k h).index = k := rfl
@[simp] theorem eta (p : Occ W) : atSlot p.label p.probe p.index p.legit = p := rfl

@[ext] theorem ext {p q : Occ W} (h : label p = label q) (w : probe p = probe q) (k : index p = index q) : p=q := by
  apply Subtype.ext
  exact Prod.ext h (Prod.ext w k)

instance : DecidableEq (Occ W) := Classical.decEq _

instance : Fintype (Occ W) := by
  classical
  let A := (i : Fin n) × (v : (W i).support) × Fin (W i v.val)
  have he (p : Occ W) : p.probe ∈ (W p.label).support := by
    have := p.legit
    apply Finsupp.mem_support_iff.mpr; omega
  let e : Occ W ≃ A :=
    { toFun p := ⟨p.label,⟨p.probe,he p⟩,p.index,p.legit⟩
      invFun p := atSlot p.1 p.2.1 p.2.2 p.2.2.isLt
      left_inv _ := rfl
      right_inv _ := rfl }
  exact Fintype.ofEquiv A e.symm

/-- No internal pairings. -/
def Matching (W : Powers G n) :=
  {s : Equiv.Perm (Occ W) // s*s = 1 ∧ ∀ v, (s v).label ≠ v.label}

instance : Fintype (Matching W) := by
  classical
  unfold Matching
  infer_instance
instance : DecidableEq (Matching W) := Classical.decEq _

def partner (P : Matching W) : Equiv.Perm (Occ W) := Subtype.val P

@[simp] theorem turn (P : Matching W) (v : Occ W) : partner P (partner P v) = v :=
  DFunLike.congr_fun (show partner P * partner P = 1 from (Subtype.property P).1) v

theorem different (P : Matching W) (v : Occ W) : (partner P v).label ≠ v.label :=
  (Subtype.property P).2 _

def edge {W : Powers G n} (x : Points n) (v w : Occ W) := entry v.probe w.probe (x v.label) (x w.label)

def corners (P : Matching W) : Finset (Occ W) := {p | p.label < (partner P p).label}

theorem orientation (P : Matching W) (v : Occ W) : partner P v ∈ corners P ↔ v ∉ corners P := by
  have h := different P v
  simp only [corners, Finset.mem_filter, Finset.mem_univ,true_and,turn, not_lt]
  exact ⟨fun H => H.le, fun H => lt_of_le_of_ne H h⟩

/-- One copy of each pair, orienting by slot number. -/
def graph {W : Powers G n} (x : Points n) (P : Matching W) := ∏ p ∈ corners P, edge x p (partner P p)

end Occ
open Occ

def monomial (x : Points n) (W : Powers G n) : ℂ := ∑ v : Occ.Matching W, Occ.graph x v

lemma monomial_smooth (W : Powers G n) {x : Points n} (hx : x ∈ conf n) :
    ContDiffAt ℝ ∞ (fun x => monomial x W) x := by
  classical
  unfold monomial
  apply ContDiffAt.sum
  intro P _
  unfold Occ.graph
  refine contDiffAt_prod ?_
  intro a ha
  have hs (i : Fin n) : ContDiffAt ℝ ∞ (fun y : Points n => y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ => E4) i).contDiff.contDiffAt
  have he := (entry_smooth a.probe ((partner P a).probe) (x := (x a.label, x (partner P a).label)) (show x a.label ≠ x (partner P a).label from
    (show Injective x.ofLp from hx).ne (different P a).symm)).comp x
      ((hs a.label).prodMk (hs (partner P a).label))
  exact he

/-- Sum over all monomials (& over all cross pairings). n=0 permitted. -/
def moment (G : Gauge) {n : ℕ} (x : Points n) : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
  Multilabel.ofBasis (fun _ => monBasis G) (monomial x)

theorem moment_basis (W : Powers G n) (x : Points n) :
    moment G x (fun i => monBasis G (W i)) = monomial x W :=
  Multilabel.applyBasis _ _ _

theorem sumFormula (x : Points n) (v : Fin n → WickPol G) :
    moment G x v = ∑ e ∈ Fintype.piFinset (fun i => ((monBasis G).repr (v i)).support),
      (∏ i, (monBasis G).repr (v i) (e i)) * monomial x e := by
  rw [Multilabel.expansion (fun _ => monBasis G)]
  simp only [moment_basis, smul_eq_mul]

theorem moment_smooth (v : Fin n → WickPol G) {x : Points n} (hx : x ∈ conf n) :
    ContDiffAt ℝ ∞ (fun y => moment G y v) x := by
  simp_rw [sumFormula]
  exact ContDiffAt.sum fun _ _ => contDiffAt_const.mul (monomial_smooth _ hx)

/-- Free separated hierarchy on gauge-labelled polynomials before quotient. -/
def correlation (G : Gauge) {n : ℕ} (x : Points n) (d : Fin n → ℕ) :
    MultilinearMap ℂ (fun i => Labels.Label G (d i)) ℂ :=
  (moment G x).compLinearMap fun i => observable G (d i)

theorem kills_equation (x : Points n) (d : Fin n → ℕ) (v : (i : Fin n) → Labels.Label G (d i)) (i : Fin n)
    (h : v i ∈ equationIdeal G (d i)) : correlation G x d v = 0 := (moment G x).map_coord_zero i h

theorem smooth (d : Fin n → ℕ) (v : (i : Fin n) → Labels.Label G (d i)) :
    ContDiffOn ℝ ∞ (fun x => correlation G x d v) (conf n) := fun _ hx =>
  (moment_smooth (fun i => observable G (d i) (v i)) hx).contDiffWithinAt
end YM.Maxwell.Wick
