import YM.Next.FREE_KERNELS.Dispatch
import YM.Next.FREE_KERNELS.Lifts
import YM.Work.F06.Energy
import YM.Work.F06.Phase
import YM.Work.F07.MatrixRoot




/-!
# Uniform positive rows from the tape

Do not use L² operator-norm conventions for any non-fixed dimension
here without paying the dimension. Real covariance comparisons use the
Counting quadratic price `pairingRe`; all p in prices are physical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate

variable {ι n k : Type*} {m : Type} [Fintype m] [Fintype n] [Fintype k]

lemma paid_after (A : Matrix m n ℂ) (B : Matrix m k ℂ) (x : n → ℂ) (y : k → ℂ) :
    pairingRe (Aᴴ*B) x y = pairingRe B (A*ᵥx) y := by
  unfold pairingRe; rw [← Matrix.mulVec_mulVec,dotProduct_mulVec,Matrix.star_mulVec]
lemma price_unit [DecidableEq m] (x : m → ℂ) : pairingRe (1 : Matrix m m ℂ) x x=sqLength x := by unfold pairingRe sqLength; rw [Matrix.one_mulVec]

structure Warm (f : ι → Row m m) : Prop where
  stock : Stock (α:=fun _=>m) (β:=fun _=>m) (fun _ : ι => 1) f
  /-- Include k and stage family constants in callers. No one-period pocket. -/
  funds : ∃ v C : ℝ, 0<v ∧ 0<C ∧ ∀ i, Funds (f i) v C

-- For varying number of *output* coords (e.g. high alias or residue).
lemma growth_price (A : Matrix n m ℂ) {C : ℝ} (hc : 0 ≤ C) (h : ∀ i j, ‖A i j‖≤C) (x : m → ℂ) :
    sqLength (A*ᵥx) ≤ (Fintype.card n:ℝ) * ((Fintype.card m:ℝ) * C)^2 * sqLength x := by
  let X := Real.sqrt (sqLength x)
  have he : X^2=sqLength x := Real.sq_sqrt (Work.F06.sqLength_nonneg _)
  let B := (Fintype.card m:ℝ) * (C*X)
  have hh (i : n) : ‖(A*ᵥx) i‖ ≤ B := by
    apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun _ => C*X) ?_).trans ?_
    · intro j _; rw [norm_mul]; exact mul_le_mul (h i j) (Work.F06.component_le_length _ _) (norm_nonneg _) hc
    simp [B]
  rw [Work.F06.sqLength_apply]
  refine (Finset.sum_le_sum (g:=fun _ => B^2) (fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hh i) _)).trans ?_
  simp; rw [← he]; unfold B; exact le_of_eq (by ring)

lemma safe_lower_gives (A : ι → Row m m) (hA : Stock (α:=fun _=>m) (β:=fun _=>m) (fun _ => 1) A) (v : ℝ) (hp : 0<v)
    (ha : ∀ i p, physical p → IsHermitian ((A i).read p) ∧ ∀ x, v*sqLength x ≤ pairingRe ((A i).read p) x x) : Warm A := by
  refine ⟨hA,?_⟩
  obtain ⟨σ,C,he,hC,h⟩ := hA.uniform; simp only [mul_one] at h
  let B := countCeil m; have hb : 0<B := Work.F06.countCeil_pos _
  refine ⟨v,B^2*C,hp,by positivity,fun i p hh => ⟨(ha i p hh).1,fun x => ⟨(ha i p hh).2 x,?_⟩⟩⟩
  have hg (a b) := Work.F06.row_entry_le (h i) he.le p hh a b
  exact (le_abs_self (pairingRe ((A i).read p) x x)).trans (Work.F06.pairingRe_diag _ hC.le hg x)

-- Spectral helpers with fixed type; translate F07 Hermitian matrix budget.
variable [DecidableEq m]
lemma band_bill {X : Matrix m m ℂ} (hh : X.IsHermitian) {v A : ℝ} (hX : Band X v A) (hp : 0<v) (ha : 0<A) :
    v^(Fintype.card m) ≤ ‖X.det‖ ∧ (IsHermitian X⁻¹ ∧ Band X⁻¹ A⁻¹ v⁻¹) := by
  obtain ⟨y,s,hs⟩ := (show ∃ (y : Holder.U m) (s : m → ℝ), X=y.val*Holder.D s*y.valᴴ from ⟨_,_,Holder.spectral_diag hh⟩)
  rw [hs] at hX
  have hx := (Work.F07.unitaryBand y s _ _).mp hX
  have hm (i) := hp.trans_le (hx i).1
  have hb : X⁻¹=y.val*Holder.D (fun i => (s i)⁻¹)*y.valᴴ := by
    apply inv_eq_left_inv
    have hu : Holder.D (fun i => (s i)⁻¹)*Holder.D s=1 := by
      rw [Holder.D,Holder.D,diagonal_mul_diagonal]; ext i j; by_cases h : i=j <;> simp [h,Matrix.one_apply,(hm j).ne']
    rw [hs]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc _ y.val, Holder.united,one_mul,← Matrix.mul_assoc (Holder.D _), hu,one_mul, Holder.united']
  have hd : X.det=∏ i,s i := by
    have hy : (y.valᴴ).det*y.val.det=1 := by rw [← Matrix.det_mul,Holder.united,Matrix.det_one]
    rw [hs, Matrix.det_mul,Matrix.det_mul]; rw [show y.val.det*_*(y.valᴴ).det = (Holder.D s).det*((y.valᴴ).det*y.val.det) by ring, hy,mul_one, Holder.D, det_diagonal]; simp
  constructor
  · rw [hd,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg fun i _ => (hm i).le)]
    calc
      _ = ∏ _ : m, v := (by simp)
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hp.le) fun i _ => (hx i).1
  rw [hb]; refine ⟨Work.F07.unitaryHerm _ _, (Work.F07.unitaryBand _ _ _ _).mpr (fun i => ⟨(inv_le_inv₀ ha (hm i)).mpr (hx i).2,(inv_le_inv₀ (hm i) hp).mpr (hx i).1⟩)⟩

/-- Weighted rows positive everywhere invert uniformly, before any L. -/
def oppositeRow (A : Row m m) := record (fun p => (A.read p)⁻¹)

omit [Fintype m] [DecidableEq m] in
lemma price_reads {A : ι → Row m m} (h : Stock (α:=fun _=>m) (β:=fun _=>m) (fun _ => 1) A) : Pay (fun _ => 1) fun i p => (A i).read p := by
  obtain ⟨σ,C,he,hC,h⟩ := h.uniform; simp only [mul_one] at h
  refine ⟨fun _ => zero_le_one,fun i j => ⟨σ/2,C,by positivity,hC,fun a => ?_⟩⟩
  have hh := Row.constant_strip (A a) (h a) i j
  exact ⟨fun p hx => (Work.F07.readDeriv hh (by linarith) (by linarith) hx.1).1,
    fun p hx => (hh.estimate p (fun i => le_of_lt (lt_trans (hx.1 i) (by linarith)))).trans_eq (mul_one _).symm⟩

lemma Pay.determinant {A : ι → Momentum → Matrix m m ℂ} (h : Pay (fun _ : ι => 1) A) : Moderate (fun _ : ι => 1) fun i p => (A i p).det := by
  simp only [Matrix.det_apply]
  apply Moderate.sum _ _ (fun _ => zero_le_one)
  intro e he
  have hb := Pay.pockets (s:=Finset.univ) (fun i _ => h.tap (e i) i)
  simp only [one_pow] at hb
  rcases Int.units_eq_one_or e.sign with hm|hm
  · simpa only [hm,one_smul] using hb
  simpa only [hm,Units.neg_smul,one_smul] using hb.neg
lemma Pay.adj {A : ι → Momentum → Matrix m m ℂ} (h : Pay (fun _ : ι => 1) A) : Pay (fun _ : ι => 1) fun i p => (A i p).adjugate := by
  refine ⟨h.site,fun i j => ?_⟩; simp only [Matrix.adjugate_apply]
  apply Pay.determinant; refine ⟨h.site,fun a b => ?_⟩
  by_cases he : a=j
  · simp only [he,Matrix.updateRow_self]; exact Moderate.const _
  simp only [Matrix.updateRow_ne he]; exact h.tap a b

lemma heated {A : ι → Row m m} (h : Warm A) :
    Warm (fun i => oppositeRow (A i)) ∧
    ∀ i : ι, (Corresponds (oppositeRow (A i)) (fun p => ((A i).read p)⁻¹)) ∧
      ∀ c : Side,(oppositeRow (A i)).acts c*(A i).acts c=1 := by
  obtain ⟨v,B,hv,hB,ha⟩ := h.funds
  have he i p (hp : physical p) := band_bill ((ha i p hp).1) (show Band ((A i).read p) v B from (ha i p hp).2) hv hB
  let f := fun i p => ((A i).read p)⁻¹
  have hPay : Pay (fun _ : ι => 1) f := by
    have hh := price_reads h.stock
    have ht : Firm (fun _ : ι => 1) (fun i p => ((A i).read p).det) := by refine ⟨1,v^(Fintype.card m),one_pos,pow_pos hv _,fun i p hp => (?_)⟩; rw [mul_one]; exact (he i p hp.1).1
    have hm := hh.adj.scale (hh.determinant.inv ht fun _ => one_pos)
    unfold f; simpa only [mul_one,inv_one,Matrix.inv_def,Ring.inverse_eq_inv'] using hm
  have hh (i) (p : Momentum) (x : Cover) : f i (p+reciprocal x)=f i p := by unfold f; rw [Row.periods]
  have hf (i p) (hp : physical p) : (f i (-p)).map star=f i p := by
    have he := Row.conjugate (A i) p; rw [show star p=p from hp] at he
    unfold f; rw [he]
    rw [show ∀ x : Matrix m m ℂ, x.map star=(xᴴ).transpose from fun _ => rfl, show ∀ x : Matrix m m ℂ, x.map star=(xᴴ).transpose from fun _ => rfl]
    rw [← Matrix.transpose_nonsing_inv,← Matrix.conjTranspose_nonsing_inv]; ext i j; simp
  have hg (i p) (hp : physical p) : (oppositeRow (A i)).read p=f i p := by
    obtain hy := record_eq hPay one_pos i (fun i p _ x _ => hh i p x) (fun i p h => hf i p h.1) (inside_base hp)
    rw [show p=(inside p)+reciprocal (-relift p) by rw [inside,reciprocal_negate]; abel]
    rw [Row.periods,hh]; exact hy
  have hw : Stock (fun _ : ι => 1) (α:=fun _=>m) (β:=fun _=>m) fun i => oppositeRow (A i) :=
    ⟨fun _ => zero_le_one,matrix_cover hPay one_pos fun _ _ _ _ _ => hh ..⟩
  constructor
  · refine ⟨hw,B⁻¹,v⁻¹,inv_pos.mpr hB,inv_pos.mpr hv,fun i p hx => ?_⟩
    rw [hg i p hx]; exact (he i p hx).2
  refine fun i => ⟨⟨(hw.whole i).safe,fun p hp => hg i p hp.1⟩,fun c => ?_⟩
  let U := oppositeRow (A i)
  rw [← (hw.whole i).acts (h.stock.whole i) c,← acts_unit (n:=c)]
  apply Whole.eq_on ((hw.whole i).prod (h.stock.whole i)) (Whole.coin _)
  intro p hp; rw [(hw.whole i).read (h.stock.whole i) hp.1,hg i p hp.1, read_unit]
  have hm := norm_pos_iff.mp ((pow_pos hv _).trans_le (he i p hp.1).1)
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm)
end YM.Next.Free
