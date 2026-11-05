import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import YM.Analysis.Polydisc
import YM.Complex.Holder
import YM.Pressure.Seeds

/-!
# Legitimate ordered trace-log of sector covariance correction

Physical real matrices. Even when AC isn't symmetric. Use Gram positivity,
symmetry of C and Schur bound on S=AC-I (one named sufficient condition,
no assuming the determinant/log identity). Works including inactive
identity completion. Thus when using log(det C) split out **exactly**
log(det(I+S)) without dropping that density-ratio factor. Doesn't bound
or identify `b` or analytic correlations. Also supplies a per-anchor,
ordered chain exponential envelope under spatial row-sum version.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Precision Matrix Function Unitary
open scoped Matrix.Norms.Frobenius BigOperators Topology ComplexOrder ENNReal Classical
namespace Round
variable {J : Type*} [Fintype J] [DecidableEq J]
abbrev Wall (J : Type*) := Matrix J J ℝ
local notation "eye" => (1:Wall J)

def rowRate (q : ℝ) (S : Wall J) := ∀ i, ∑ j, |S i j| ≤ q
omit [DecidableEq J] in
lemma rows_norm (S : Wall J) {q : ℝ} (h : rowRate q S) (x : J→ℝ) : ‖S*ᵥx‖ ≤ q*‖x‖ := by
  cases isEmpty_or_nonempty J with
  | inl hI => rw [Subsingleton.elim x 0]; simp
  | inr hN =>
    have hq : 0≤q := (Finset.sum_nonneg fun i _=> abs_nonneg _).trans (h (Classical.choice hN))
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg _))).mpr (fun i=> ?_)
    rw [Real.norm_eq_abs]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    simp only [abs_mul]
    refine le_trans (Finset.sum_le_sum (fun j (_:j∈Finset.univ) => mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg (S i j)))) ?_
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
omit [DecidableEq J] in
lemma ride (S T : Wall J) {q k : ℝ} (h : rowRate q S) (ht : rowRate k T) (hp : 0≤k) : rowRate (q*k) (S*T) := by
  intro i; simp only [Matrix.mul_apply]; apply le_trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs ..))
  rw [Finset.sum_comm]; simp_rw [abs_mul,← Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum (fun j (_:j∈Finset.univ)=> mul_le_mul_of_nonneg_left (ht j) (abs_nonneg (S i j))))
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h i) hp

def ripple (S : Wall J) (n : ℕ) (i j : J) := - ((-S) ^ (n+1)) i j / (n+1:ℝ)
def wave (S : Wall J) (n : ℕ) := ∑ i : J,ripple S n i i
private lemma ripple_bounds {q : ℝ} (S : Wall J) (h : rowRate q S) (ht : 0≤q) (k : ℕ) (i j : J) :
    ‖ripple S k i j‖ ≤ q ^ (k+1) := by
  have he : rowRate q (-S) := fun i => by simpa [rowRate,Matrix.neg_apply] using h i
  have hh (k) : rowRate (q^k) ((-S)^k) := by
    induction k with
    | zero => intro i; simp [Matrix.one_apply,abs_ite]
    | succ k ih => rw [pow_succ,pow_succ]; exact ride _ _ ih he ht
  unfold ripple; rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (by positivity : (0:ℝ)<k+1)]
  refine (div_le_self (abs_nonneg _) (by simp)).trans ((Finset.single_le_sum (f:=fun j => |((-S)^(k+1)) i j|) (fun k _=>abs_nonneg _) (Finset.mem_univ j)).trans (hh _ _))

def traceLog (S : Wall J) := ∑' k : ℕ,wave S k
def onLine (S : Wall J) (i : J) := ∑' k : ℕ,ripple S k i i

theorem lineSummable {q : ℝ} (S : Wall J) (h : rowRate q S) (hq : 0≤q) (ht : q<1) (i j : J) : Summable fun k=>ripple S k i j := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hq ht).mul_right q)
  intro k; rw [← pow_succ]; exact ripple_bounds S h hq k i j
lemma lines {q : ℝ} (S : Wall J) (h : rowRate q S) (hq : 0≤q) (ht : q<1) : traceLog S=∑ i,onLine S i := by
  unfold traceLog onLine wave; exact Summable.tsum_finsetSum fun i _=>lineSummable S h hq ht i i

/-- Put the correction in Hermitian form using actual Gram metric
positivity. Expose similarity matrices; no denominators when J empty. -/
theorem twins {A C : Wall J} (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ M N B : Wall J, M*N=1 ∧ N*M=1 ∧ B.IsHermitian ∧ A*C=M*B*N := by
  let V := hA.1.eigenvectorUnitary
  let T := conjStarAlgAut ℝ _ V
  let Y := fun j=> Real.sqrt (hA.1.eigenvalues j)
  let M := T (diagonal Y)
  let N := T (diagonal fun j=> (Y j)⁻¹)
  have hm i : (Y i)^2 = hA.1.eigenvalues i := Real.sq_sqrt (hA.eigenvalues_pos i).le
  have hh i : 0<Y i := Real.sqrt_pos.mpr (hA.eigenvalues_pos _)
  have he : M*M=A := by
    unfold M; rw [←map_mul,diagonal_mul_diagonal,hA.1.spectral_theorem]; congr; ext i; simpa only [← pow_two, Function.comp_apply] using! hm i
  have hl : M*N=1 := by
    unfold M N; rw [←map_mul,diagonal_mul_diagonal]; simp [((hh _).ne')]
  have hr : N*M=1 := mul_eq_one_comm.mp hl
  have hM : Mᴴ=M := by
    change star (T (diagonal Y))= _
    rw [← map_star]; congr 1; ext i j; by_cases hi : i=j; subst j; simp;  simp [hi,Ne.symm hi,diagonal]
  refine ⟨M,N,M*C*M,hl,hr,?_,?_⟩
  · unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hC.eq,hM]; exact (mul_assoc ..).symm -- check
  · rw [← he]; simp only [mul_assoc,hl,mul_one]

theorem twin_log (S A C M N B : Wall J) (_hA : A.PosDef) (_hC : C.IsHermitian) (he : S=A*C-1)
    (h : M*N=1) (hl : N*M=1) (hB : B.IsHermitian) (hp : A*C=M*B*N) {q : ℝ} (hq : rowRate q S) (ht : q<1) :
    0<(eye+S).det ∧ traceLog S=Real.log (eye+S).det := by
  have hS : eye+S = M*B*N := by rw [he,hp]; abel
  have hd : (eye+S).det = ∏ i, hB.eigenvalues i := by
    rw [hS,Matrix.det_mul,Matrix.det_mul,show M.det*B.det*N.det = (M.det*N.det)*B.det by ring,
      ← Matrix.det_mul,h,Matrix.det_one,one_mul]; exact hB.det_eq_prod_eigenvalues
  have hx (i : J) : |hB.eigenvalues i-1| ≤ q := by
    let v : J→ℝ := ⇑(hB.eigenvectorBasis i)
    let y := M*ᵥv
    have hb : B *ᵥ v = (hB.eigenvalues i) • v := hB.mulVec_eigenvectorBasis i
    have hy : S*ᵥy=(hB.eigenvalues i-1) • y := by
      have hr : S*ᵥy=(eye+S) *ᵥ y-y := by rw [Matrix.add_mulVec,Matrix.one_mulVec,add_sub_cancel_left]
      rw [hr,hS,←mulVec_mulVec,show N*ᵥy=v by unfold y; rw [mulVec_mulVec,hl,Matrix.one_mulVec],←mulVec_mulVec,hb,Matrix.mulVec_smul,sub_smul,one_smul]
    have hy' : 0<‖y‖ := by
      rw [norm_pos_iff]; intro H
      have hv : v=0 := by rw [← Matrix.one_mulVec v,← hl,← mulVec_mulVec,(show M *ᵥ v = 0 from H),Matrix.mulVec_zero]
      exact (hB.eigenvectorBasis).orthonormal.ne_zero i (by ext k; exact congr_fun hv k)
    have hk := rows_norm S hq y; rw [hy,norm_smul,Real.norm_eq_abs] at hk
    exact le_of_mul_le_mul_right hk hy'
  have hh (i) : 0 < hB.eigenvalues i := by have h := abs_le.mp (hx i); linarith
  have h0 : 0 < ∏ i, hB.eigenvalues i := Finset.prod_pos fun i _=>hh i
  rw [hd]; refine ⟨h0,?_⟩
  have hm (i : J) := Real.hasSum_pow_div_log_of_abs_lt_one (show |1-hB.eigenvalues i|<1 by rw [abs_sub_comm]; exact (hx _).trans_lt ht)
  simp_rw [show ∀ (i : J),1-(1-hB.eigenvalues i)=hB.eigenvalues i from fun _=>by ring] at hm
  have hz (i) := (hm i).neg
  have hw := hasSum_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ)=>hz i)
  rw [Real.log_prod (fun i _=>(hh i).ne')]
  unfold traceLog
  simp only [neg_neg] at hw
  rw [←hw.tsum_eq]
  apply tsum_congr; intro n
  unfold wave ripple; simp only [neg_div,← Finset.sum_div,Finset.sum_neg_distrib]; congr 1
  change ((-S)^(n+1)).trace / _ = _
  congr 1
  have hs (i : ℕ) : (-S)^i=M*(eye-B)^i*N := by
    have HH : -S=M*(eye-B)*N := by rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,h,← hS]; abel
    induction i with
    | zero => rw [pow_zero,pow_zero,Matrix.mul_one,h]
    | succ i ih => rw [pow_succ,pow_succ,ih,HH]; simp only [mul_assoc]; rw [← mul_assoc N,hl]; simp
  let V := hB.eigenvectorUnitary
  let T := conjStarAlgAut ℝ _ V
  have hh : B = T (diagonal fun i => hB.eigenvalues i) := hB.spectral_theorem
  let z := diagonal (fun i => 1-hB.eigenvalues i)
  have hI : eye-B = (T z) := by
    have ht : z=eye-diagonal (fun i => hB.eigenvalues i) := by ext i j; by_cases h : i=j <;> simp [z,h,diagonal]
    rw [ht,map_sub,map_one,←hh]
  have hg i : T (z^i)=V.val*z^i*V.valᴴ := rfl
  rw [hs,hI,← map_pow,hg,Matrix.trace_mul_comm,← Matrix.mul_assoc,hl,Matrix.one_mul,
    Matrix.trace_mul_comm,← Matrix.mul_assoc, show V.valᴴ*V.val=1 from V.prop.1,Matrix.one_mul,diagonal_pow,trace_diagonal]; rfl




lemma exact_trace {A C : Wall J} (hA : A.PosDef) (hC : C.IsHermitian) (S : Wall J) (he : S=A*C-1) {q : ℝ} (hq : rowRate q S)
    (hp : 0≤q) (ht : q<1) : 0<C.det ∧ 0 < (eye+S).det ∧ Summable (wave S) ∧ traceLog S=Real.log (eye+S).det := by
  obtain ⟨M,N,B,h,hl,hb,hM⟩ := twins hA hC
  have H := twin_log S A C M N B hA hC he h hl hb hM hq ht
  refine ⟨?_,H.1,summable_sum (fun i (_ : i∈Finset.univ)=> lineSummable S hq hp ht i i),H.2⟩
  apply pos_of_mul_pos_right (a:=A.det) _ hA.det_pos.le
  rw [← det_mul, ← (show eye+ S=A*C from by rw [he]; abel)]; exact H.1

-- ordered chain norms (absolute even within polynomial multiplication).
variable {T : Type*} (δ : T → T → ℕ) (label : J → T)



def walks (S : Wall J) : ℕ→Wall J
  | 0 => eye
  | k+1 => of fun i j => ∑ b, |S i b| * walks S k b j






end Round
end YM.SectorNext.Vacuum
