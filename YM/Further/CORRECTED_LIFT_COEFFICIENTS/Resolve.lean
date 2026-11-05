import YM.Next.FREE_KERNELS.Ground
import YM.Push.CORRECTED_COLUMNS.Program
import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# E(KPcol) on the actual periodic curl space

Price finite period coefficient entries of Copper using the canonical pre-ordered
floor inputs. Polar isn't on a gauge-fixed tree. Include harmonic frequency
with 0 contribution, EVEN ties. Use precision from `Floor` h and `Present`,
not an assumption about the entries. Counts real with `Runs` normalization;
not the same as coset-lift Schur covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Resolve
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops
open Work Matrix Laurent Bloch Metric Exterior Precision Next.Free
open scoped Topology Matrix.Norms.Frobenius BigOperators ComplexConjugate
variable {G : Gauge} {m n : Side} {A : Bed} {V : Clip} {η D : ℝ} {j : ℕ}

variable (h : Floor A V n η D) (he : 0 < η)
abbrev charge (A : Bed) (n : Side) := Precision.K (A.metric.acts n)
local notation "S" => charge A n
local notation "L" => Exterior.d 1 n
include h
lemma charge_sym : (S).transpose=S := by unfold charge Precision.K; simp only [Matrix.transpose_mul,transpose_transpose,Matrix.mul_assoc,h.symmetric.1]
lemma energy (x : form 1 n) : η*dotProduct (L*ᵥx) (L*ᵥx) ≤ dotProduct x (S*ᵥx) := by
  unfold charge Precision.K; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,dotProduct_mulVec x,vecMul_transpose]; exact (h.uniform.1 _).1
include he
lemma nothing {x : form 1 n} : S *ᵥ x = 0 ↔ L *ᵥ x = 0 := by
  constructor
  · intro hx; have hh := energy h x
    rw [hx,dotProduct_zero] at hh; rw [← dotProduct_self_eq_zero]; apply le_antisymm
    · exact le_of_mul_le_mul_left (hh.trans_eq (mul_zero η).symm) he
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  intro hx; unfold charge Precision.K; rw [← Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero]
private lemma charge_image : LinearMap.range (S).mulVecLin = LinearMap.range (L).transpose.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_le
  · unfold charge Precision.K; rw [Matrix.mul_assoc,Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range ..
  have hp : LinearMap.ker (S).mulVecLin=LinearMap.ker (L).mulVecLin := by ext x; exact nothing h he
  have hx := LinearMap.finrank_range_add_finrank_ker (S).mulVecLin; rw [hp] at hx
  have hm := LinearMap.finrank_range_add_finrank_ker (L).mulVecLin
  rw [show Module.finrank ℝ (LinearMap.range (L).transpose.mulVecLin)= Module.finrank ℝ (LinearMap.range (L).mulVecLin) from Matrix.rank_transpose _]
  exact (Nat.add_right_cancel (hm.trans hx.symm)).le

lemma solves : ∃ X : Matrix (Body 1 n) (Body 2 n) ℝ, S*X=(L).transpose := by
  have hh (i : Body 2 n) : (L).transpose *ᵥ (Pi.single i 1)∈LinearMap.range (S).mulVecLin := by rw [charge_image h he]; exact ⟨_,rfl⟩
  choose x hx using hh
  refine ⟨Matrix.of fun i j => x j i,?_⟩; ext i j
  change S i ⬝ᵥ _ = _
  have hm : (S*ᵥ x j) i = ((L).transpose*ᵥ Pi.single j 1) i := congr_fun (hx j) i
  exact hm.trans (by simp)

def field := (solves h he).choose
theorem hinge : S * field h he = (L).transpose := (solves h he).choose_spec

def screenP := L * field h he

theorem quadratic : screenP h he = (field h he).transpose*S*field h he := by
  unfold screenP; rw [show (field h he).transpose*S= L from ?_]; rw [← charge_sym h,← Matrix.transpose_mul,hinge h he,Matrix.transpose_transpose]
lemma balanced : (screenP h he).transpose=screenP h he := by rw [quadratic]; simp only [Matrix.transpose_mul,transpose_transpose,charge_sym h,Matrix.mul_assoc]




/- Construct directly the SYMBOL check without selecting zero prescription
for a potential. Because we read in curls, `rotor_before` is enough. -/
local notation "H₁" => rotations n (TypeFace 1)
local notation "H₂" => rotations n (TypeFace 2)
omit h he in
private lemma waves {r : ℝ} (hr : 0 < r) (j : ℕ) (v : Train j) :
    let F := solo n (signal 1 1)
    let T := solo n (rotor 1 r v)
    let D := solo n (fieldD 1 r v)
    F * D * T=F := by
  intro F T D
  unfold F D T solo; rw [fiber_mult,fiber_mult]; refine congr_arg fiber (funext fun i => ?_)
  let p := mon i
  by_cases hh : p=0
  · change signal 1 1 p*_*_= signal 1 1 p; rw [hh]; simp
  change signal 1 1 p*_*_=signal 1 1 p; rw [Matrix.mul_assoc,rotor_before _ r hr v (base_subset_realCube zone_pos (mon_mem n i)) hh,
    Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc, signal_chain 1 0 p]; simp

omit he in
lemma bespoke {r l : ℝ} (v : Train j) (e : Defined r l v A) : S=Precision.K ((pink r v).acts n) := by
  unfold charge Precision.K; rw [← e.diag,Matrix.mul_assoc, h.same, Matrix.mul_assoc]

theorem circuit (hj : 4 ≤ j) {r : ℝ} (hr : 0 < r) (v : Train j) (l : ℝ) (e : Defined r l v A) :
    Runs H₂ H₂ (screenP h he) (solo n fun p => signal 1 1 p*fieldD 1 r v p*(signal 1 1 p)ᴴ) := by
  let F := solo n (signal 1 1); let C := solo n (rotor 1 r v)
  let X := field h he; let W := solo n (fieldD 1 r v)
  have hh : Runs H₁ H₁ S C := by rw [bespoke h v e]; exact runs_rotor r hr hj v n
  have hx : Runs H₂ H₁ L F := (cobound_true 1).coarse n
  have hu : approached ((L).transpose)*H₂=H₁*Fᴴ := by
    have hz := hx.back (rotations_crew n _) (rotations_crew n _); rw [div_self (stage_ne n),one_smul] at hz; exact hz
  have hm : S*X=(L).transpose := hinge h he
  have hU := (rotations_crew n (TypeFace 1))
  let Z := (stageVolume n)⁻¹ • (H₁ᴴ*(approached X*H₂))
  have ha : approached X*H₂=H₁ * Z := by
    unfold Z; rw [Matrix.mul_smul,← Matrix.mul_assoc,hU.2.1,Matrix.smul_mul,Matrix.one_mul,smul_smul,inv_mul_cancel₀ (stage_ne n),one_smul]
  have ht : C*Z=Fᴴ := by
    have hg : H₁*(C*Z)=H₁*Fᴴ := by rw [← Matrix.mul_assoc, show H₁*C= _ from Eq.symm hh, Matrix.mul_assoc, ← ha,← Matrix.mul_assoc, ← prom_mul,hm,hu]
    apply smul_right_injective _ hU.1
    have hi := congr_arg (H₁ᴴ * ·) hg; rw [← Matrix.mul_assoc,hU.2.2,← Matrix.mul_assoc H₁ᴴ,hU.2.2,Matrix.smul_mul,Matrix.smul_mul,Matrix.one_mul, Matrix.one_mul] at hi; exact hi
  have hy := hx.product (show Runs H₁ H₂ X Z from ha)
  change Runs _ _ _ (F*Z) at hy
  have hS : F*Z=F*W*Fᴴ := by nth_rw 1 [← show F*W*C=F from waves (n:=n) hr j v]; rw [Matrix.mul_assoc,ht]
  rw [hS] at hy
  unfold F W solo at *; simp only [fiber_mult,fiber_H] at hy
  exact hy
end YM.Further.CorrectedLift.Resolve
