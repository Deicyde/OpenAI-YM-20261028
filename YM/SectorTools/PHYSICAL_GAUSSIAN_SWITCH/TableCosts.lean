import YM.Next.MULTISOURCE.Curves
import YM.Next.ROTATIONS.Mass
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Elliptic

/-!
# Absolute table costs and a hybrid engine

Elementary Schur-price projection to uniform elliptic & L1 coefficient
costs. One reason for also keeping the latter: a localized change of
ordered columns can make an inverse correction whose precision
support is the entire (interacting through C!) counting space, but
whose total entry mass is small and pays only for the changed columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.TableCosts
open Function Filter Matrix Lattice
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Wisps Next.SectorChange.Schur
open AnalyticBridge.GaussianFieldAlignment.Relative (symPart sym_of_sub sym_pours)
open scoped Topology BigOperators
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I] {A D B : Covar I}
variable {c : Side} {o : I → Site c} {s K δ : ℝ}

section pours

omit [DecidableEq I] in
lemma pours_exist (A : Covar I) (o : I → Site c) (s : ℝ) : ∃ K : ℝ, Pours A o o s K := by
  let f := fun i j => rate s (separation (o i) (o j)) * |A i j|
  have hf i j : 0 ≤ f i j := mul_nonneg (rate_pos ..).le (abs_nonneg _)
  refine ⟨∑ i,∑ j,f i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hf i j)),
    fun i => Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hf i j)) (Finset.mem_univ _), fun i => ?_⟩
  rw [Finset.sum_comm]
  exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hf j i)) (Finset.mem_univ _)

omit [DecidableEq I] in
lemma pour_neg (h : Pours A o o s K) : Pours (-A) o o s K := by simpa using h.scale (-1)

omit [DecidableEq I] in
lemma row_budget (h : Pours A o o s K) (hs : 0 ≤ s) (i : I) : ∑ j, |A i j| ≤ K := by
  simpa only [rate,zero_mul,Real.exp_zero,one_mul] using (h.weaker hs le_rfl).row i
omit [DecidableEq I] in
lemma col_budget (h : Pours A o o s K) (hs : 0 ≤ s) (j : I) : ∑ i, |A i j| ≤ K := row_budget h.turn hs j

omit [DecidableEq I] in
lemma quad_schur (h : Pours A o o s K) (hs : 0 ≤ s) (x : Vec I) : |quad A x| ≤ K*(x ⬝ᵥ x) := by
  refine (estimate (h.weaker hs le_rfl) x x).trans ?_
  rw [sumSq_dot]; linarith

lemma from_pours (hA : A.PosDef) (h : Pours A o o s K) (hi : Pours A⁻¹ o o s K) (hs : 0≤s) (hk : 1≤K) : Elliptic K A := by
  have ht : (A⁻¹)⁻¹=A := nonsing_inv_nonsing_inv A (unit_det hA)
  refine ⟨hk,symm_pos hA, fun x => ⟨?_, (le_abs_self (quad A _)).trans (quad_schur h hs x)⟩⟩
  exact ht ▸ inverse_lower hA.inv (by linarith : 0<K) (fun x => (le_abs_self (quad A⁻¹ _)).trans (quad_schur hi hs x)) x

omit [Fintype I] [DecidableEq I] in
lemma symm_sym (A : Covar I) : (symPart A).IsSymm := by
  unfold Matrix.IsSymm symPart; rw [transpose_smul,transpose_add,transpose_transpose,add_comm]

/-- Pay A's inverse at the SAME s for small perturbations from D. `pours_exist`
needs only hold separately on each finite volume; the conclusion is uniform
when the earlier K and δ prices are. -/
lemma inverse_perturb (hA : A.PosDef) (hD : D.PosDef) (hd : Pours D⁻¹ o o s K) (he : Pours (A-D) o o s δ)
    (hs : 0 ≤ s) (hh : K * δ ≤ 1/2) : Pours A⁻¹ o o s (2*K) := by
  have hu := unit_det hA; have hv := unit_det hD
  have ha : -(D⁻¹*(A-D)*A⁻¹)=A⁻¹-D⁻¹ := by
    rw [Matrix.mul_sub,Matrix.sub_mul,D.nonsing_inv_mul hv, Matrix.one_mul,Matrix.mul_assoc,A.mul_nonsing_inv hu,Matrix.mul_one,neg_sub]
  have ho {t : ℝ} (ht : Pours A⁻¹ o o s t) : Pours A⁻¹ o o s (K+1/2*t) := by
    have hy := pour_neg ((hd.fuse he hs).fuse ht hs); rw [ha] at hy
    have hx := hd.bind hy; rw [add_sub_cancel] at hx
    exact hx.weaker le_rfl (add_le_add_right (mul_le_mul_of_nonneg_right hh ht.pos) K)
  obtain ⟨t,ht⟩ := pours_exist A⁻¹ o s
  have hf : 0 ≤ K := hd.pos; have hg := ht.pos
  let v (n : ℕ) := 2*K+(1/2:ℝ)^n*t
  have hb (n) : Pours A⁻¹ o o s (v n) := by
    induction n with
    | zero => exact ht.weaker le_rfl (by unfold v; simp; linarith)
    | succ n ih => exact (ho ih).weaker le_rfl (by unfold v; rw [pow_succ]; ring_nf; rfl)
  have hT : Tendsto v atTop (𝓝 (2*K)) := by
    unfold v
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_const t).const_add (2*K)
  exact ⟨by positivity, fun i => le_of_tendsto_of_tendsto' tendsto_const_nhds hT fun n => (hb n).row i,
    fun i => le_of_tendsto_of_tendsto' tendsto_const_nhds hT fun n => (hb n).col i⟩

end pours
section mass
-- counting L1 matrix cost #ALL entries (can later be far smaller
-- than K times volume for perturbations). Use both row and col
-- norms along products on either side of the small insertion.
def mass (A : Covar I) := ∑ i, ∑ j, |A i j|
def load (A : Covar I) (i : I) := ∑ j, |A i j|
omit [DecidableEq I] in
lemma load_nonneg (A : Covar I) (i : I) : 0 ≤ load A i := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
omit [DecidableEq I] in
lemma mass_transpose (A : Covar I) : mass A.transpose = mass A := Finset.sum_comm
omit [DecidableEq I] in
lemma mass_neg (A : Covar I) : mass (-A) = mass A := by unfold mass; simp
omit [DecidableEq I] in
lemma mass_add (A B : Covar I) : mass (A+B) ≤ mass A + mass B := by
  unfold mass; simp_rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => abs_add_le ..
omit [DecidableEq I] in
lemma mass_scale (A : Covar I) (c : ℝ) : mass (c•A) = |c| * mass A := by
  unfold mass; simp_rw [Finset.mul_sum,Matrix.smul_apply,smul_eq_mul,abs_mul]

omit [DecidableEq I] in
lemma mass_sym (A : Covar I) : mass (symPart A) ≤ mass A := by
  rw [symPart,mass_scale, abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))]
  have he := mass_add A A.transpose; rw [mass_transpose] at he; linarith

omit [DecidableEq I] in
lemma mass_right (hB : ∀ i, load B i ≤ K) (A : Covar I) : mass (A*B) ≤ K*mass A := by
  have hi i : load (A*B) i ≤ K*load A i := by
    unfold load
    apply (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs (f:=fun k => A i k * B k j) _)).trans
    rw [Finset.sum_comm]; simp_rw [abs_mul, ← Finset.mul_sum]; rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)).trans_eq (mul_comm ..)
  unfold mass; rw [Finset.mul_sum]; exact Finset.sum_le_sum fun _ _ => hi _

omit [DecidableEq I] in
lemma mass_left (hA : ∀ j, load A.transpose j ≤ K) (B : Covar I) : mass (A*B) ≤ K*mass B := by
  simpa only [← transpose_mul,mass_transpose] using mass_right hA B.transpose

/-- Total trace/row displacement cost after a covariance change charged
both per row and in total. -/
theorem precision_costs (hA : A.PosDef) (hD : D.PosDef) (hd : Pours D⁻¹ o o s K) (he : Pours (A-D) o o s δ)
    (hs : 0 ≤ s) (hh : K*δ ≤ 1/2) {b : ℝ} (hm : mass (A-D) ≤ b) :
    Pours (A⁻¹-D⁻¹) o o s (2*K^2*δ) ∧ mass (A⁻¹-D⁻¹) ≤ 2*K^2*b := by
  have hu := inverse_perturb hA hD hd he hs hh
  have ha : A⁻¹-D⁻¹= -(D⁻¹*(A-D)*A⁻¹) := by
    rw [Matrix.mul_sub,Matrix.sub_mul,D.nonsing_inv_mul (unit_det hD), Matrix.one_mul,Matrix.mul_assoc,A.mul_nonsing_inv (unit_det hA),Matrix.mul_one,neg_sub]
  rw [ha,mass_neg]; have hk := hd.pos
  refine ⟨(by convert! pour_neg ((hd.fuse he hs).fuse hu hs) using 1; ring),?_⟩
  apply (mass_right (B:=A⁻¹) (row_budget hu hs) _).trans
  have hv : mass (D⁻¹ * (A-D)) ≤ K*b := (mass_left (A:=D⁻¹) (col_budget hd hs) _).trans (mul_le_mul_of_nonneg_left hm hk)
  nlinarith only [mul_le_mul_of_nonneg_left hv hk]

/-- Keep *columns*; these are the centers in 's ordered Π. -/
def columns (X : Finset I) (A : Covar I) : Covar I := Matrix.of fun i j => if j∈X then A i j else 0
lemma columns_pour (X : Finset I) (h : Pours A o o s K) : Pours (columns X A) o o s K := by
  have ht i j : rate s (separation (o i) (o j))*|columns X A i j|≤rate s (separation (o i) (o j))*|A i j| := by
    apply mul_le_mul_of_nonneg_left _ (rate_pos ..).le
    by_cases j∈X <;> simp [columns, *]
  exact ⟨h.pos,fun i => (Finset.sum_le_sum (fun j _ => ht i j)).trans (h.row i),fun j => (Finset.sum_le_sum (fun i _ => ht i j)).trans (h.col j)⟩
lemma mass_columns (X : Finset I) (h : Pours A o o s K) (hs : 0≤s) : mass (columns X A) ≤ X.card*K := by
  unfold mass columns; simp only [Matrix.of_apply, apply_ite abs, abs_zero]; rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem,Finset.univ_inter]
  simpa using (Finset.sum_le_sum (s:=X) (g:=fun _ => K) fun i _ => col_budget h hs i)

end mass
end YM.SectorTools.PhysicalGaussianSwitch.TableCosts
