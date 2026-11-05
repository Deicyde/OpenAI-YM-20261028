import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Local log convention: Agreement and ordinary exponential

Over general real algebras (including marked nilpotent extensions). Normalized
constant `1`. Distinct from positivity/analyticity of a denominator at
nonzero coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Classical BigOperators
open Finset PowerSeries
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] {p q r s : PowerSeries A} {n d : ℕ}

def Steps (n : ℕ) (p q : PowerSeries A) := ∀ i<n, coeff i p=coeff i q
namespace Steps
omit [Algebra ℝ A] in
lemma mul (hp : Steps n p q) (hr : Steps n r s) : Steps n (p*r) (q*s) := by
  intro i hi; rw [coeff_mul,coeff_mul]; exact sum_congr rfl fun j hj=> by
    have hh := mem_antidiagonal.mp hj; rw [hp j.1 (by omega),hr j.2 (by omega)]
omit [Algebra ℝ A] in
lemma add (hp : Steps n p q) (hr : Steps n r s) : Steps n (p+r) (q+s) := fun i hi=> by rw [map_add,map_add,hp i hi,hr i hi]
omit [Algebra ℝ A] in
lemma neg (hp : Steps n p q) : Steps n (-p) (-q) := fun i hi=> by rw [map_neg, map_neg,hp i hi]
omit [Algebra ℝ A] in
lemma self : Steps n p p := fun _ _=>rfl
omit [Algebra ℝ A] in
lemma powers (hp : Steps n p q) (r : ℕ) : Steps n (p^r) (q^r) := by induction r with
    | zero => simp only [pow_zero]; exact self
    | succ i ih => simp only [pow_succ]; exact ih.mul hp
omit [Algebra ℝ A] in
lemma small (hp : Steps d p q) (he : n≤d) : Steps n p q := fun i hi=> hp i (hi.trans_le he)
lemma scale (hp : Steps n p q) (r : ℝ) : Steps n (r • p) (r • q) := fun i hi=> by rw [coeff_smul,coeff_smul,hp i hi]
end Steps
-- lift coeffwise operation
def parallel (L : A→ₗ[ℝ]B) : PowerSeries A→ₗ[ℝ]PowerSeries B where
  toFun p := PowerSeries.mk (fun i=> L (coeff i p))
  map_add' x y:= by ext1 i; simp
  map_smul' r x:= by ext1 i; simp
lemma coeff_parallel (L : A→ₗ[ℝ]B) (p : PowerSeries A) (i : ℕ) : coeff i (parallel L p)=L (coeff i p) := by simp [parallel]
lemma parallel_C (L : A→ₗ[ℝ]B) (r : A) : parallel L (C r)= C (L r) := by ext1 i; rw [coeff_parallel,coeff_C, coeff_C]; split <;> simp
lemma parallel_agree (hn : Steps n p q) (L : A→ₗ[ℝ]B) : Steps n (parallel L p) (parallel L q) := fun i hi => by rw [coeff_parallel,coeff_parallel, hn i hi]
lemma parallel_by (L : A→ₐ[ℝ]B) : ⇑(parallel L.toLinearMap)= ⇑(PowerSeries.map L.toRingHom) := by
  ext1 x; ext1 i; rw [coeff_parallel,coeff_map]; rfl

def parallelD (D : Derivation ℝ A A) : Derivation ℝ (PowerSeries A) (PowerSeries A) where
  toLinearMap:= parallel D.toLinearMap
  map_one_eq_zero' := by
    change parallel D.toLinearMap 1=0; rw [show (1:PowerSeries A)=C (1:A) from (map_one _).symm, parallel_C, show D.toLinearMap 1=0 from D.map_one_eq_zero, map_zero]
  leibniz' p q:= by
    ext1 n; rw [coeff_parallel, map_add]; simp only [smul_eq_mul]; rw [mul_comm q]; simp only [coeff_mul,coeff_parallel,map_sum]
    -- swap second term by commutativity at SERIES level before expansion (see above)
    rw [← sum_add_distrib]; exact sum_congr rfl fun i hi=> ((D.leibniz (coeff i.1 p) (coeff i.2 q)).trans (by simp only [smul_eq_mul]; rw [mul_comm (coeff i.2 q)]; rfl))
lemma parallel_D (p : PowerSeries A) (D : Derivation ℝ A A) (i : ℕ) : coeff i (parallelD D p)=D (coeff i p) := by exact coeff_parallel D.toLinearMap p i
lemma D_leib (D : Derivation ℝ A A) (p q : A) : D (p*q)= D p*q + p*D q := by simp only [D.leibniz, smul_eq_mul]; ring

-- exponential of positive order series, full coefficient policy
abbrev allot (n : ℕ) (p : PowerSeries A) := ((n.factorial:ℝ)⁻¹ • p^n : PowerSeries A)
abbrev budget (n : ℕ) (p : PowerSeries A) := ∑ i∈range (n+1), allot i p
def tide (p : PowerSeries A) := PowerSeries.mk (fun i=> coeff i (budget i p))
-- normalization (later char unit)
lemma tide_const (p : PowerSeries A) : constantCoeff (tide p)=1 := by simp [tide,budget,allot]
lemma tide_unit (p : PowerSeries A) : IsUnit (tide p) := isUnit_iff_constantCoeff.mpr (by rw [tide_const]; exact isUnit_one)
lemma allot_empty (hp : constantCoeff p=0) (h : n < d) : coeff n (allot d p)=0 := by
  rw [allot,coeff_smul,X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hp) d) n h, smul_zero]
lemma tide_full (hp : constantCoeff p=0) (n : ℕ) : Steps (n+1) (tide p) (budget n p) := by
  intro i hi; unfold tide; simp only [coeff_mk,budget, map_sum]
  apply sum_subset (range_mono (by omega)) (fun _ _ h=>allot_empty hp (by rw [mem_range] at h; omega))
lemma tide_agree (hp : Steps n p q) : Steps n (tide p) (tide q) := by
  intro i hi; simp only [tide,coeff_mk,budget,map_sum]; exact sum_congr rfl fun v _=> ((hp.powers v).scale _) i hi
lemma tide_map (F : A →ₐ[ℝ] B) (p : PowerSeries A) : parallel F.toLinearMap (tide p)=tide (parallel F.toLinearMap p) := by
  ext1 n; rw [coeff_parallel]; simp only [tide,budget,coeff_mk,map_sum]
  refine sum_congr rfl fun i _=>?_; rw [allot,allot, coeff_smul,coeff_smul,map_smul,parallel_by, ← map_pow, coeff_map]; rfl

lemma allot_succ' (i : ℕ) (p : PowerSeries A) (D : Derivation ℝ (PowerSeries A) (PowerSeries A)) :
    D (allot (i+1) p) = allot i p * D p := by
  unfold allot; rw [D.map_smul, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_eq_mul, Nat.factorial_succ,Nat.add_one_sub_one]; simp_rw [smul_mul_assoc,smul_smul]; congr 1; push_cast; field_simp
lemma budget_succ' (i : ℕ) (p : PowerSeries A) (D : Derivation ℝ (PowerSeries A) (PowerSeries A)) :
    D (budget (i+1) p)= budget i p * D p := by
  unfold budget; rw [map_sum,sum_range_succ',sum_mul]; simp_rw [allot_succ']; simp [allot]
-- lift to all degrees
lemma differentiating (D : Derivation ℝ A A) (hp : constantCoeff p=0) : parallelD D (tide p) = tide p * parallelD D p := by
  ext1 i
  calc _ = coeff i (parallelD D (budget (i+1) p)) := parallel_agree (tide_full hp (i+1)) D.toLinearMap i (by omega)
       _ = coeff i (budget i p*parallelD D p) := congr_arg _ (budget_succ' i p (parallelD D))
       _ = _ := ((Steps.mul (r:=parallelD D p) (s:=parallelD D p) (tide_full hp i) Steps.self) i (by omega)).symm
-- formal coupling derivative, preserve agreement with larger order
-- need IsScalarTower ℝ A PowerSeries A? likely
def clockD (A : Type) [CommRing A] [Algebra ℝ A] : Derivation ℝ (PowerSeries A) (PowerSeries A) := (PowerSeries.derivative A).restrictScalars ℝ
lemma clock_coeff (p : PowerSeries A) (n : ℕ) : coeff n (clockD A p) = ((n+1:ℕ):ℝ) • coeff (n+1) p := by
  change coeff n (PowerSeries.derivative A p)=_
  rw [coeff_derivative, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ,mul_comm]
lemma Steps.clock (hp : Steps (n+1) p q) : Steps n (clockD A p) (clockD A q) := fun i hi=> by rw [clock_coeff,clock_coeff,hp (i+1) (by omega)]
lemma differentiate_time (hp : constantCoeff p=0) : clockD A (tide p)= tide p* clockD A p := by
  ext1 i
  calc _ = coeff i (clockD A (budget (i+1) p)) := (tide_full hp (i+1)).clock i (by omega)
       _ = coeff i (budget i p*clockD A p) := congr_arg _ (budget_succ' i p _)
       _ = _ := ((Steps.mul (r:=clockD A p) (s:=clockD A p) (tide_full hp i) Steps.self) i (by omega)).symm
lemma clock_unique (p q : PowerSeries A) (hp : constantCoeff p=constantCoeff q) (he : clockD A p=clockD A q) : p=q := by
  ext1 i; cases i with
  | zero => simpa only [coeff_zero_eq_constantCoeff] using hp
  | succ i => exact smul_right_injective _ (show ((i+1:ℕ):ℝ) ≠0 by positivity) ((clock_coeff p i).symm.trans ((congr_arg (fun p:PowerSeries A=>coeff i p) he).trans (clock_coeff q i)))
lemma tide_injective (hp : constantCoeff p=0) (hq : constantCoeff q=0) (h : tide p=tide q) : p=q := by
  refine clock_unique p q (hp.trans hq.symm) ?_
  apply (tide_unit p).mul_right_inj.mp -- inspect
  rw [← differentiate_time hp,h,differentiate_time hq]
end YM.WilsonBulk
