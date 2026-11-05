import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Series
import YM.Next.BOUNDARY.Core

/-!
# Local determinant chain alphabet

Use physical real component keys, one for every link-color pair, incl
repetitions. Support assigned later. `n` starts at zero for *both*
alphabets; one off-window jump even at n=0 in the integrated alphabet,
and the correction alphabet (no shift integral) starts with tr(S). Do not
sum away intermediate indices before asking for absolute price. Log changes
use both actual addresses at the same ordered indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix MeasureTheory FreeResolvent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section roads
variable {ι : Type} {n : ℕ} (P S : Square ι)

/-- Start with P, followed by n copies of S along x; n=0 is direct P. -/
def road : {n : ℕ} → (P S : Square ι) → ι → ι → (Fin n → ι) → ℝ
  | 0, P, _, i,j,_ => P i j
  | k+1,P,S,i,j,x => P i (x 0) * road (n:=k) S S (x 0) j (Fin.tail x)

lemma road_succ (i j m : ι) (x : Fin n → ι) : road P S i j (Fin.cons m x) = P i m * road S S m j x := by
  rw [road,Fin.cons_zero,Fin.tail_cons]

/-- The geometry of the jumps is kept separately; assigning zero
coefficients for invalid jumps is measure-independent. -/
def jumps (Q : ι → ι → Prop) : {n : ℕ} → ι → ι → (Fin n→ι) → Prop
  | 0, i,j,_ => Q i j
  | k+1,i,j,x => Q i (x 0) ∧ jumps Q (n:=k) (x 0) j (Fin.tail x)

variable {Q : ι→ι→Prop}

lemma road_drop (hp : ∀ i j, ¬ Q i j → P i j=0) (hs : ∀ i j, ¬ Q i j → S i j=0) (i j)
    (x : Fin n → ι) (h : ¬ jumps Q i j x) : road P S i j x = 0 := by
  induction n generalizing i P with
  | zero => exact hp i j h
  | succ n ih =>
    rw [road]
    by_cases he : Q i (x 0)
    · rw [ih S hs _ _ (show ¬ jumps Q (x 0) j _ from fun hh => h ⟨he,hh⟩),mul_zero]
    rw [hp _ _ he,zero_mul]

lemma road_pos (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i j, 0 ≤ S i j) (i j) (x : Fin n → ι) :
    0 ≤ road P S i j x := by
  induction n generalizing i P with
  | zero => exact hp i j
  | succ n ih => exact mul_nonneg (hp ..) (ih S hs _ _)

lemma road_major {α β : ℝ} (ha : 0 ≤ α) (hb : 0 ≤ β) (R : Square ι) (hr : ∀ i j, 0 ≤ R i j)
    (hp : ∀ i j, |P i j| ≤ α*R i j) (hs : ∀ i j, |S i j| ≤ β*R i j)
    (i j) (x : Fin n → ι) : |road P S i j x| ≤ α*β^n*road R R i j x := by
  induction n generalizing i P α with
  | zero => rw [pow_zero,mul_one,road,road]; exact hp ..
  | succ n ih =>
    rw [road,abs_mul,road,pow_succ]
    exact (mul_le_mul (hp ..) (ih S hb hs _ _) (abs_nonneg _) (mul_nonneg ha (hr ..))).trans_eq (by ring)

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma sum_cons (g : (Fin (n+1) → ι) → ℝ) : (∑ x,g x)=∑ m,∑ x : Fin n → ι, g (Fin.cons m x) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => ι)) g,Fintype.sum_prod_type]; rfl

lemma sums_road (n : ℕ) (i j) : (∑ x : Fin n → ι, road P S i j x)=(P*S^n) i j := by
  induction n generalizing P i with
  | zero => simp [road]
  | succ n ih =>
    rw [sum_cons]
    simp_rw [road_succ, ← Finset.mul_sum, ih]
    rw [pow_succ',Matrix.mul_apply]

end roads

section letters
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

abbrev Letter (ι : Type) (spacing : ℕ) := (n : ℕ) × (ι × (Fin (n+spacing) → ι))

/-- With shift integral from the replacement of A's inverse. -/
def scroll (W : ι → Set ι) (A : Square ι) (i : ι) (x : Fin (n+1) → ι) (u : ℝ) :=
  - road (pie W A u) (-defect W A u) i i x

def page (W : ι → Set ι) (A : Square ι) (z : Letter ι 1) := ∫ u in Ioi 0, scroll W A z.2.1 z.2.2 u

/-- Covariance correction. -/
def errata (W : ι → Set ι) (A : Square ι) (z : Letter ι 0) :=
  let S := excess W A;
  -(road (-S) (-S) z.2.1 z.2.1 z.2.2) / ((z.1:ℝ)+1)

lemma scroll_cont (W : ι → Set ι) (A : Square ι) (hw : ∀ i, i ∈ W i) (h : A.PosDef) (i : ι) (x : Fin (n+1) → ι) :
    ContinuousOn (scroll W A i x) (Ioi 0) := by
  intro u hu
  have hh (m : ℕ) (p : ℝ → Square ι) (hp : ContinuousAt p u) (i j) (x : Fin m → ι) :
      ContinuousAt (fun v : ℝ => road (p v) (-defect W A v) i j x) u := by
    induction m generalizing p i with
    | zero => simp only [road]; exact ((continuous_id (X:=Square ι)).matrix_elem _ _).continuousAt.comp hp
    | succ m ih =>
      simp only [road]
      exact (((continuous_id (X:=Square ι)).matrix_elem _ _).continuousAt.comp hp).mul
        (ih _ (defect_cont h hw hu.out.le).neg _ _)
  exact (hh _ _ (pie_cont h hw hu.out.le) i i x).neg.continuousWithinAt

lemma unwind (W : ι → Set ι) (A : Square ι) (i n u) :
    term W A i n u = ∑ x, scroll W A (n:=n) i x u := by
  unfold term scroll; rw [Finset.sum_neg_distrib,sums_road]

open SectorNext.Vacuum in
lemma unspool (W : ι → Set ι) (A : Square ι) (i n) :
    Round.ripple (excess W A) n i i = ∑ x : Fin n → ι, errata W A ⟨n,i,x⟩ := by
  unfold errata; dsimp only
  simp_rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [sums_road, Round.ripple,pow_succ']

end letters

section weights
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type*} {D : Cost X} {p : ι→X} {v C q : ℝ}
  {W : ι → Set ι} {A : Square ι}

def fares (D : Cost X) (p : ι → X) (v : ℝ) : Square ι := Matrix.of fun i j => D.weight (-v) (p i) (p j)

omit [DecidableEq ι] [Fintype ι] in
lemma fares_nn (i j : ι) (D : Cost X) (p : ι → X) (v : ℝ) : 0 ≤ fares D p v i j := D.weight_nn ..

omit [DecidableEq ι] in
lemma sum_fares (hv : 0 ≤ v) {L : ℝ} (hl : 0 ≤ L) (h : D.Volume p v L) (n i j) :
    let J := fares D p v
    (∑ x : Fin n → ι, road J J i j x) ≤ L^n := by
  intro J
  induction n generalizing i with
  | zero => simpa only [J,road,fares,pow_zero,of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin,nsmul_eq_mul, Nat.cast_one,one_mul,D.weight_zero] using
        ((D.weight_mono (neg_nonpos.mpr hv) (p i) (p j)).trans_eq (D.weight_zero ..))
  | succ n ih =>
    rw [sum_cons]; simp_rw [road_succ, ← Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ih _) (D.weight_nn (-v) (p i) (p x)))
    rw [← Finset.sum_mul,pow_succ']
    exact mul_le_mul_of_nonneg_right (h.bound _) (by positivity)

omit [DecidableEq ι] in
lemma road_fares {P S : Square ι} {α β : ℝ} {n : ℕ} (hp : D.Schur p p v α P) (hs : D.Schur p p v β S)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (i j : ι) (x : Fin n → ι) :
    let J := fares D p v
    |road P S i j x| ≤ α*β^n*road J J i j x :=
  road_major _ _ ha hb _ (fun _ _ => D.weight_nn ..) (fun i j => (hp.rows.point i j).trans_eq (mul_comm ..))
    (fun i j => (hs.rows.point i j).trans_eq (mul_comm ..)) i j x

namespace Priced
variable (b : Priced D p W A v C q)
include b
lemma scroll_paid (z : Letter ι 1) :
    let J := fares D p v; let i:=z.2.1; let x:=z.2.2
    let B := C*q^(z.1+1)*road J J i i x
    IntegrableOn (scroll W A i x) (Ioi 0) ∧ (∫ u in Ioi 0, |scroll W A i x u|) ≤ B ∧ |page W A z| ≤ B := by
  intro J i x B
  apply integral_price (scroll_cont _ _ b.root b.gram i x) (C:=B)
  intro u hu
  have hv := attenuation_pos hu.out.le
  have hm : 0<C := zero_lt_one.trans_le b.paid
  have he := b.coupon
  have hn : 0 ≤ road J J i i x := road_pos _ _ (fun _ _ => D.weight_nn ..) (fun _ _ => D.weight_nn ..) _ _ _
  have hh := road_fares (b.columns u hu.out.le) (b.shift u hu.out.le).neg (by positivity) (by positivity) i i x
  unfold scroll; rw [abs_neg]
  apply hh.trans
  have hy : attenuation u ^ (z.1+1) ≤ attenuation u := by rw [pow_succ]; exact mul_le_of_le_one_left hv.le (pow_le_one₀ hv.le (attenuation_le hu.out.le))
  calc
    C*attenuation u*(q*attenuation u)^(z.1+1)*_ ≤ C*attenuation u*(q^(z.1+1)*attenuation u)*road J J i i x := by
      rw [mul_pow]; gcongr
    _ = B*_ := by unfold B; ring

lemma errata_paid (z : Letter ι 0) :
    let J := fares D p v; let i:=z.2.1; let x:=z.2.2
    |errata W A z| ≤ q^(z.1+1)*road J J i i x := by
  intro J i x
  unfold errata; dsimp only
  rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ)<z.1+1),pow_succ']
  exact (div_le_self (abs_nonneg _) (by simp)).trans (road_fares b.mix.neg b.mix.neg b.coupon b.coupon i i x)

lemma scroll_entry (hq : q<1) (i : ι) :
    HasSum (fun n => ∑ x : Fin (n+1) → ι,page W A ⟨n,i,x⟩) (logKernel A i i-letterBase W A i) := by
  have he (n : ℕ) : ∫ u in Ioi 0, term W A i n u = ∑ x : Fin (n+1) → ι,page W A ⟨n,i,x⟩ := by
    simp_rw [unwind W A i n]
    exact integral_finsetSum Finset.univ fun x _ => (b.scroll_paid ⟨n,i,x⟩).1
  have hh := b.log_tail hq i
  simp_rw [he] at hh; exact hh

/-- For using in full sector change. `s` is already a correction, not the
whole covariance log. Even for repeated colors/indices use ALL tuples, not
just nonzero or Gaussian-active ones. -/
lemma labeled (hq : q<1) (hC : (Next.SectorChange.Schur.clouded W A).PosDef) :
    Real.log A.det = ∑ i, (letterBase W A i + ∑' n, ∑ x : Fin (n+1)→ι,page W A ⟨n,i,x⟩) ∧
      Real.log (1 + excess W A).det = ∑ i, (∑' n, ∑ x : Fin n → ι, errata W A ⟨n,i,x⟩) ∧
      (∀ i, Summable (fun n => ∑ x : Fin (n+1)→ι,page W A ⟨n,i,x⟩)) ∧
      ∀ i, Summable (fun n => ∑ x : Fin n→ι, errata W A ⟨n,i,x⟩) := by
  obtain ⟨-, -, h, H⟩ := (b.chains hq hC)
  have hj i := (H i).2
  simp_rw [unspool] at h hj
  refine ⟨?_,h,fun i => (b.scroll_entry hq i).summable,hj⟩
  rw [log_trace b.gram]
  apply Finset.sum_congr rfl
  intro i _
  rw [(b.scroll_entry hq i).tsum_eq]; abel
end Priced
end weights
end YM.AnalyticBridge.RelativeLogdet
