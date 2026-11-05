import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Next.RANK.Matrices
import YM.Next.RANK.Mountain


/-!
# Source record before projection

Read canonical section components on their actual old mask. The unit is a global entry
separate from those components. Remainders at original mask; classify SMALL by the
true Stencil, not by winding of the leading pol terms (and classify budget before calibration).
Terms and budgets in unnormalized physical units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter RG Source Labels Wilson Lattice Normal MvPolynomial Asymptotics MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} (C : Family G) {k d N p m : ℕ}
variable (v : C.label d)

def parcel (d k N p : ℕ) (v : C.label d) := (C.factory d N p).entries k ((C.factory d N p).terminal.symm v)
def pinHat (C : Family G) (d k : ℕ) := ((C.S.a k:ℂ)^d)⁻¹
lemma pinReal (d k : ℕ) : star (pinHat C d k)=pinHat C d k := by simp [pinHat]

abbrev LA (d : ℕ) := Unit ⊕ (C.labels.level d).Index
def select (k N p : ℕ) (i : (C.labels.level d).Index) :=
    ((C.labels.level d).scaled ((C.path.rep N p k).p.threshold)⁻¹ ((C.labels.level d).core (parcel C d k N p v).x)) i
-- before multiplying. at all-good global occurrence.
def verseW (k N p : ℕ) : LA C d→ℂ := Sum.elim (fun _=> (parcel C d k N p v).x 0) (fun i => select C v k N p i)
def verseX (d k p : ℕ) : LA C d→ Support (C.side k p) := Sum.elim (fun _=>{0}) (fun _=> (C.localSection d).footprint 0)
def verseA (d k p : ℕ) : LA C d → Config G (C.side k p) → ℂ := Sum.elim (fun _ _ => 1) (fun i => (C.localSection d).places (Pi.single i 1) 0)

def smalls (i k N p : ℕ) (v : C.label d) (w : ℕ) := coverNumber (C.path.rep N p k).p.B ((parcel C d k N p v).support w) ≤ i
abbrev nearIndex (v : C.label d) (i k N p : ℕ) := LA C d ⊕ {w // smalls C i k N p v w}
abbrev wideIndex (v : C.label d) (i k N p : ℕ) := {w // ¬ smalls C i k N p v w}

def nearX (i k N p) : nearIndex C v i k N p → Support (C.side k p) := Sum.elim (verseX C d k p) (fun s => (parcel C d k N p v).support s.val)
def nearA (i k N p) : nearIndex C v i k N p → Config G (C.side k p)→ℂ := Sum.elim (verseA C d k p) (fun s => (parcel C d k N p v).regular s.val)
def nearW (i k N p) : nearIndex C v i k N p → ℂ := (pinHat C d k) • (Sum.elim (verseW C v k N p) (fun _=>1))
def wideX (i k N p) : wideIndex C v i k N p → Support (C.side k p) := fun j => (parcel C d k N p v).support j.val
def wideA (i k N p) : wideIndex C v i k N p → Config G (C.side k p) → ℂ := fun j => (parcel C d k N p v).regular j.val
def wideW (i k N p) : wideIndex C v i k N p → ℂ :=fun _=>pinHat C d k

def nearHol (i k N p) (U : Config G (C.side k p)) := ∑' a,(nearW C v i k N p a)*(nearA C v i k N p a U)
def wideHol (i k N p) (U : Config G (C.side k p)) := ∑' a,wideW C v i k N p a * wideA C v i k N p a U

def paid (d k N p) (v : C.label d) := (C.labels.level d).coeffSize (Price.awake C d k N p v)
lemma paid_pos (d k N p) (v : C.label d) : 0 ≤ paid C d k N p v := Work.G08.size_nonneg _ _
def moneys (d k N p) (v : C.label d) := (C.path.levels.params k).columns * paid C d k N p v
lemma money_nn (d k N p) (v : C.label d) : 0 ≤ moneys C d k N p v := mul_nonneg
    (zero_le_one.trans (C.path.levels.params k).columns_ge) (paid_pos C ..)

lemma zeroLoan {n : Side} (o : Site n) (p : BudgetPoint) (F : Support n) : p.Regular F (fun _ : Config G n => (1:ℂ)) ∧ p.supBounds o F (fun _ : Config G n => (1:ℂ)) 1 := by
  let f (_ : Config G n) := (1:ℂ)
  have he (l U) : leftDerivs f l U=if l=[] then 1 else 0 := by
    induction l generalizing U with
    | nil => simp only [↓reduceIte];rfl
    | cons i l H => simp only [leftDerivs,H, List.cons_ne_nil, ↓reduceIte]; exact deriv_const _ _
  refine ⟨⟨fun _ _ _ => rfl,measurable_const,fun _ _=>rfl,fun _ _=>contDiffAt_const,fun U hu A l h=>?_⟩,zero_le_one,fun U hu l hl ht => ?_⟩
  · change HasDerivAt (fun t : ℝ=> leftDerivs f l (increment U (t • A))) _ _
    change HasDerivAt _ (leftDerivs f (A::l) U) _; simp only [he,List.cons_ne_nil,↓reduceIte]; exact hasDerivAt_const ..
  change ‖leftDerivs f _ _‖≤_; rw [he]; split<;>simp

lemma rotate_core (F : Frame G d) (v : F.Coeff) : F.coeffSize (F.core v) ≤ F.coeffSize v := by
  unfold Frame.coeffSize; apply Finset.sum_le_sum; intro i _
  change ‖Function.update v 0 0 i‖ ≤ _; by_cases H : i=0 <;> simp [H]

variable (i : ℕ) (h : C.Makes) (h₁ : C.ref d≤k) (h₂ : k≤N)

structure Wrapper {ι : Type*} (p : BudgetPoint) {n : Side} (X : ι → Support n) (A : ι → Config G n → ℂ) (f : ι→ℂ) (Q : ℝ) : Prop where
  pays : ∃ e : ι→ℝ, (∀ i,p.Regular (X i) (A i) ∧ p.supBounds 0 (X i) (A i) (e i)) ∧ SumBudget (fun i=> ‖f i‖*e i) Q
  anchored i : 0∈X i

def expCut (P : BudgetPoint) (m : ℕ) := Real.exp (-P.supportExponent * m)
include h h₁ h₂

lemma receipts (v : C.label d) (p : ℕ) :
    let P' := C.path.rep N p k; let L:= moneys C d k N p v
    Wrapper P'.p (nearX C v i k N p) (nearA C v i k N p) (nearW C v i k N p) (3*L) ∧
      Wrapper P'.p (wideX C v i k N p) (wideA C v i k N p) (wideW C v i k N p) (expCut P'.p i * L) := by
  let F:= C.labels.level d
  let P:= parcel C d k N p v
  intro W L; let Z:= W.p; let R:= C.path.levels
  have hz:= (C.path.levels.params k).columns_ge
  let X:= P.x
  let r:= pinHat C d k
  let c:= (C.path.levels.params k).columns
  have hc : 1 ≤ c:= hz
  have hX : L = ‖r‖* (c*F.coeffSize X) := by
    change c*(∑ i,‖(r • X) i‖)= ‖r‖*(c*∑ i,‖X i‖)
    simp_rw [Finset.mul_sum, Pi.smul_apply,norm_smul]; exact Finset.sum_congr rfl fun i _=>mul_left_comm ..
  have hy := (h.wilson.represents N p k h₂).vac
  have hb := h.calibrated d N p (h₁.trans h₂)
  obtain ⟨a,b,ha,hb',hab,he,e,hh,-⟩:=hb.cap k h₁ h₂ ((C.factory d N p).terminal.symm v)
  have H : P.Format 0 _ W:= hb.format k h₁ h₂ _
  rcases e with ⟨e,hE,hv⟩
  have hv' (j) := hv j |>.1
  have hS : Summable e := hE.2.1.of_nonneg_of_le hv' fun i=> Z.loMass (P.support i) _ (hv' i)
  have hE' : ∑' i,e i ≤ c*F.coeffSize X := by
    -- W shadows
    apply (le_trans (hS.tsum_le_tsum (fun i=> W.p.loMass (P.support i) (e i) (hv' i)) hE.2.1) hE.2.2).trans
    exact (le_trans (le_add_of_nonneg_right hb') hab).trans (mul_le_mul_of_nonneg_left (rotate_core F ..) (zero_le_one.trans hc))
  let B:= LA C d; let M i:= Z.mass (P.support i) (e i)
  let s:= {j // smalls C i k N p v j}; let x:= wideIndex C v i k N p
  have hw : Summable fun i : x=> M i.val:= hE.2.1.subtype _
  have heM : (∑' j : x,M j.val) ≤ c* F.coeffSize X := by
    apply (le_trans (hE.2.1.tsum_subtype_le M (setOf fun j => ¬ smalls C i k N p v j) (hE.1)) hE.2.2).trans
    exact (le_trans (le_add_of_nonneg_right hb') hab).trans (mul_le_mul_of_nonneg_left (rotate_core F ..) (zero_le_one.trans hc))
  have hNear : Summable fun i : s => e i.val := hS.subtype _
  have hQ : (∑' j : s, e j.val) ≤ c * F.coeffSize X := by
    exact (hS.tsum_subtype_le e (setOf (smalls C i k N p v)) hv').trans hE'
  let S:= C.localSection d
  let f : B → ℝ := Sum.elim (fun _=>1) (fun i : F.Index=> c * Z.threshold^(F.grades i).2)
  have hP (j : B) : Z.Regular (verseX C d k p j) (verseA C d k p j) ∧ Z.supBounds 0 (verseX C d k p j) (verseA C d k p j) (f j) := by
    cases j with
    | inl j=> exact zeroLoan ..
    | inr j=>
      change Z.Regular _ _ ∧ Z.supBounds _ _ _ (c * Z.threshold^(F.grades j).2)
      -- priced at original k independent of N
      rw [show Z=_ from hy]; exact h.priced d k p h₁ 0 j
  have hB : (∑ i : B, ‖r * verseW C v k N p i‖* f i)≤ 2*L := by
    let s:= Z.threshold; have ht : 0<s:=Z.threshold_pos
    have he (i : F.Index) : ‖r * F.scaled s⁻¹ (F.core X) i‖* (c * s^(F.grades i).2)=‖r‖*(c*‖F.core X i‖) := by
      rw [Frame.scaled_apply,norm_mul,norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; rw [inv_pow]; field_simp
    unfold B LA; rw [Fintype.sum_sum_type, Fintype.sum_unique]; change ‖r*X 0‖*(1:ℝ)+(∑ i : F.Index, ‖r*F.scaled s⁻¹ (F.core X) i‖* (c*s^(F.grades i).2)) ≤ _
    simp_rw [he, ← Finset.mul_sum]
    rw [mul_one,norm_mul]
    have hv : ‖X 0‖ ≤ c * F.coeffSize X := (le_trans (Finset.single_le_sum (f:=fun i=> ‖X i‖) (fun _ _=> norm_nonneg _) (Finset.mem_univ 0))
      (le_mul_of_one_le_left (Work.G08.size_nonneg _ _) hz))
    have hj := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rotate_core F X) (zero_le_one.trans hc)) (norm_nonneg r)
    rw [hX]; change ‖r‖*_+‖r‖*(c*F.coeffSize (F.core X)) ≤ _; linarith only [hj,mul_le_mul_of_nonneg_left hv (norm_nonneg r)]
  refine ⟨⟨?_,fun j=>?_⟩,⟨⟨fun j=> e j.val,fun j=>⟨H.smooth _,hv _⟩,fun j=> mul_nonneg (norm_nonneg _) (hv' _),(hS.subtype _).mul_left ‖r‖,?_⟩,fun j=> H.origin _⟩⟩
  · let f':s→ℝ := fun j=>e j.val
    have hA (j : B⊕s) : Z.Regular (nearX C v i k N p j) (nearA C v i k N p j) ∧ Z.supBounds 0 (nearX C v i k N p j) (nearA C v i k N p j) (Sum.elim f f' j) := by
      cases j with | inl q => exact hP _ | inr q => exact ⟨H.smooth _,hv _⟩
    let J : B⊕s → ℝ := fun x=> ‖nearW C v i k N p x‖ * Sum.elim f f' x
    have hx (y : s) : J (Sum.inr y)=‖r‖* f' y := by change ‖r*1‖*_=_; rw [mul_one];rfl
    have hs : Summable fun y : s => J (Sum.inr y) := (hNear.mul_left ‖r‖).congr (fun z=>(hx z).symm)
    have HJ₁ : Summable (J ∘ Sum.inl) := (hasSum_fintype _).summable
    have HJ₂ : Summable (J ∘ Sum.inr) := hs
    have hz' : Summable J := Summable.sum _ HJ₁ HJ₂
    refine ⟨Sum.elim f f',hA,fun x=>mul_nonneg (norm_nonneg (nearW C v i k N p x)) ((hA x).2.1),hz',?_⟩
    change ∑' i,J i ≤ _
    rw [Summable.tsum_sum HJ₁ HJ₂,tsum_fintype]; simp_rw [hx]
    rw [tsum_mul_left]; change (∑ i:B, ‖r*verseW C v k N p i‖* f i)+‖r‖*(∑' i,f' i) ≤ 3*L
    rw [← show 2*L+L=3*L by ring]; apply add_le_add hB; rw [hX]; exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
  · rcases j with (j|j)|j
    · exact Finset.mem_singleton_self _
    · change (0:Site (C.side k p)) ∈ S.stencil.image (fun x=> wrap _ x + 0); exact Finset.mem_image.mpr ⟨0,(h.sections d).anchored, by rw [map_zero,zero_add]⟩
    exact H.origin _
  · let T:= expCut Z i
    change (∑' j : x,‖r‖*e j.val)≤ _
    rw [tsum_mul_left]
    have ht : 0 ≤ T:=(Real.exp_pos _).le
    have hv (j : x): e j.val ≤ T * M j.val := by
      change e _ ≤ Real.exp _ * (Real.exp _ * e _); rw [← mul_assoc,← Real.exp_add]; refine le_mul_of_one_le_left (hv' _) (Real.one_le_exp ?_)
      have hx := Nat.lt_of_not_ge j.property
      change i<coverNumber Z.B (P.support j.val) at hx
      have hf := mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ) |>.mpr hx.le) Z.exponent_pos.le; linarith only [hf]
    rw [hX]; apply (mul_le_mul_of_nonneg_left ((hS.subtype _).tsum_le_tsum hv (hw.mul_left T)) (norm_nonneg r)).trans
    rw [tsum_mul_left]; change _ ≤ T*_; rw [mul_left_comm T]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heM ht) (norm_nonneg _)
end YM.Next.Rank.Spindle
