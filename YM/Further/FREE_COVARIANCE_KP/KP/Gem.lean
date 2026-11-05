import Mathlib.Analysis.Calculus.SmoothSeries
import YM.Further.FREE_COVARIANCE_KP.KP.Weight
import YM.PREC.Stacks
import YM.Work.F06.Energy

/-! # Matrix perturbation with price for every mixed derivative -/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Matrix Work.F06 Exterior Precision Bloch Lattice Laurent
open scoped Topology ContDiff Matrix.Norms.Elementwise BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η : ℝ} {k l : ℤ}
variable {m n b I : Type*} {U : Window}

abbrev ArrayM (I m n : Type*) := I→ E4 → Matrix m n ℂ
def Value (U : Window) (k : ℤ) (f : ArrayM I m n) := ∀ i j, Weight U k (fun a p => f a p i j)
namespace Value
variable {f g : ArrayM I m n}
lemma joint (hf : Value U k f) (hg : Value U k g) : Value U k (fun i p => f i p+g i p) := fun i j => (hf i j).sum (hg i j)
lemma remove (hf : Value U k f) (hg : Value U k g) : Value U k (fun i p => f i p-g i p) := fun i j => (hf i j).diff (hg i j)
lemma starM (hf : Value U k f) : Value U k (fun i p => (f i p)ᴴ) := fun i j => (hf j i).conjugated
lemma priced {a : I→ E4 → ℂ} (ha : Weight U l a) (hf : Value U k f) : Value U (l+k) (fun i p => a i p • f i p) := fun i j => ha.times (hf i j)
lemma product [Fintype n] (hf : Value U k f) {D : ArrayM I n b} (h : Value U l D) : Value U (k+l) (fun i p => f i p * D i p) := fun i j =>
  Weight.sum_finite Finset.univ _ (fun a _ => (hf i a).times (h a j))
lemma switched (h : Value U k f) (he : ∀ i, EqOn (f i) (g i) U.look) : Value U k g := fun i j => (h i j).stay (fun a _ hp => congr_fun (congr_fun (he a hp) i) j)

/-- first surplus rule ab-a'b' = a(b-b') + (a-a')b' -/
lemma wedge_cost [Fintype n] (hf : Value U k f) (hs : Value U (k+1) (fun i p => f i p-g i p))
    {D E : ArrayM I n b} (he : Value U l E) (hx : Value U (l+1) (fun i p => D i p-E i p)) :
    Value U (k+l+1) (fun i p => f i p*D i p-g i p*E i p) := by
  have ht := hf.product hx; have hd := hs.product he
  rw [← add_assoc] at ht; rw [add_right_comm] at hd
  apply (ht.joint hd).switched; intro i p hp; dsimp; rw [Matrix.mul_sub, Matrix.sub_mul]; abel

section Square
variable {A : ArrayM I n n} [Fintype n] [DecidableEq n] (h : Value U 0 A)
lemma det (h : Value U 0 A) : Weight U 0 (fun i p => (A i p).det) := by
  have hv (u : n ≃ n) (S : Finset n) : Weight U 0 (fun i p => ∏ j∈S,A i p (u j) j) := by
    induction S using Finset.induction_on with
    | empty => simpa using (Weight.spare U 1)
    | insert a S ha ih => simpa [ha] using (h _ a).times ih
  simp_rw [Matrix.det_apply]
  refine Weight.sum_finite Finset.univ _ fun i _ => ?_
  change Weight U 0 (fun a p => ((Equiv.Perm.sign i).val :ℤ) • _)
  simp only [zsmul_eq_mul]; exact (hv i _).scale _
lemma switch_cost (h : Value U 0 A) {a : ℝ} (ha : 0<a) (he : ∀ i,∀ p:E4,p∈U → a≤‖(A i p).det‖) : Value U 0 (fun i p => (A i p)⁻¹) := by
  have ht := Value.det h |>.reverse a ha he
  intro i j
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv, Matrix.smul_apply,smul_eq_mul,Matrix.adjugate_apply]
  refine ht.times (Value.det (A:=fun a p => (A a p).updateRow j (Pi.single i 1)) ?_)
  intro i' j'; by_cases hs : j=i'
  · subst i'; simp only [updateRow_self]; exact Weight.spare _ _
  simp only [updateRow_ne (Ne.symm hs)]; exact h _ _
lemma det_unit {H : Matrix n n ℂ} {a : ℝ} (ha : 0<a)
    (hf : ∀ x, a*sqLength x≤pairingRe H x x) : IsUnit H.det := by
  rw [← Matrix.isUnit_iff_isUnit_det,←Matrix.mulVec_injective_iff_isUnit]
  intro v w he; apply sub_eq_zero.mp
  have hk := hf (v-w); rw [pairingRe,Matrix.mulVec_sub, sub_eq_zero.mpr he] at hk
  have hK : sqLength (v-w)≤0 := nonpos_of_mul_nonpos_right (by simpa using hk) ha
  funext i; change (v-w) i=0
  rw [← norm_eq_zero]; exact le_antisymm ((component_le_length ..).trans_eq (Real.sqrt_eq_zero_of_nonpos hK)) (norm_nonneg _)
lemma paid_inv (h : Value U 0 A) {a : ℝ} (ha : 0<a) (he : ∀ i,∀ p:E4,p∈U → ∀ x,a*sqLength x≤pairingRe (A i p) x x) : Value U 0 (fun i p => (A i p)⁻¹) := by
  choose B hB H using fun i j => (h i j).quotes 0
  let b := ∑ ij : n×n,B ij.1 ij.2
  let Q (g : Matrix n n ℂ) := ∀ x,a*sqLength x≤pairingRe g x x
  let K := closedBall (0:Matrix n n ℂ) b ∩ {g | Q g}
  have ht : IsCompact K := by
    apply (isCompact_closedBall ..).inter_right
    rw [show {g | Q g}=⋂ x : n→ℂ, {g : Matrix n n ℂ| a*sqLength x≤pairingRe g x x} from by ext; simp [Q]]
    refine isClosed_iInter fun i => isClosed_le continuous_const ?_; unfold pairingRe dotProduct Matrix.mulVec; fun_prop
  have hK (i : I) (p : E4) (hp : p∈U) : A i p∈K := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_,he i p hp⟩
    have hb : 0≤b := Finset.sum_nonneg (fun j _ => hB _ _)
    rw [Matrix.norm_def]; apply pi_norm_le_iff_of_nonneg hb |>.mpr; intro j; apply pi_norm_le_iff_of_nonneg hb |>.mpr; intro k
    apply (show ‖A i p j k‖≤B j k by simpa using H j k i p hp).trans
    exact Finset.single_le_sum (a:=(j,k)) (f:=fun l : n×n => B l.1 l.2) (fun i _ => hB _ _) (Finset.mem_univ _)
  rcases K.eq_empty_or_nonempty with hh|hh
  · apply switch_cost h zero_lt_one fun i p hp => ?_; have := hK i p hp; rw [hh] at this; exact this.elim
  obtain ⟨M,hM,hb⟩ := ht.exists_isMinOn hh (continuous_id.matrix_det.norm.continuousOn)
  exact switch_cost h (norm_pos_iff.mpr (det_unit ha hM.2).ne_zero) fun i p hp => hb (hK i p hp)
end Square
end Value
end YM.Further.FreeCovariance.KP
