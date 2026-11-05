import YM.Push.LOOP_COEFFICIENT.Paths.Domination
import YM.Work.F07.Read

/-!
# Anchored local analytic functions with literal cover addresses
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Set Matrix Lattice Laurent Bloch Exterior RG Complex Metric
open scoped Topology ContDiff BigOperators
variable {ι a b : Type} {n : Side} {k : ℕ}

structure Reader (a : Type) where
  shape : Type
  [range : Fintype shape]
  leaf : shape → a
  offset : shape → Cover
  sizeBound : ℕ
  near i : size (offset i) ≤ sizeBound
  value : CSpace shape → ℂ
attribute [instance] Reader.range
namespace Reader
variable [Fintype a] (M : Reader a) [Fintype b] [DecidableEq a] (A : Grid n b a)

def location (x : Site n) (i : M.shape) := A.symm (x+wrap n (M.offset i),M.leaf i)

def gather (x : Site n) : CSpace b →L[ℂ] CSpace M.shape := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (M.location A x i)

def insertions (p : Momentum) : CSpace a →L[ℂ] CSpace M.shape := ContinuousLinearMap.pi fun i => mode p (M.offset i) • ContinuousLinearMap.proj (M.leaf i)

omit [DecidableEq a] [Fintype a] in
lemma gather_norm (x : Site n) (v : CSpace b) : ‖M.gather A x v‖ ≤ ‖v‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => norm_le_pi_norm v (M.location A x i))

omit [DecidableEq a] in
lemma insertions_norm {η : ℝ} (hη : 0≤η) (p : Momentum) (hp : Within η p) : ‖M.insertions p‖ ≤ Real.exp (η*M.sizeBound) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le; intro x
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  change ‖mode _ _ * x _‖ ≤ _
  rw [norm_mul]; exact mul_le_mul ((reward _ _ _ hp).trans (by gcongr; exact M.near _)) (norm_le_pi_norm ..) (norm_nonneg _) (Real.exp_pos _).le

def distributed (u : CSpace b) := ∑ x, M.value (M.gather A x u)

def monomial (M : Reader a) (p : Fin k → Momentum) : CSpace a [×k]→L[ℂ] ℂ := (iteratedFDeriv ℂ k M.value 0).compContinuousLinearMap fun i => M.insertions (p i)

omit [Fintype b] in
lemma gather_wave {p : Momentum} {i : Site n} (hi : Matches p i) (x : Site n) (v : CSpace a) : M.gather A x (plane A i *ᵥ v) = cell i x • (M.insertions p v) := by
  ext1 j; change (plane A i *ᵥ v) (M.location A x j) = cell i x * (mode _ _ * _)
  rw [plane_apply, location,A.apply_symm_apply,hi.read,cell_add]; exact mul_assoc ..
omit [Fintype a] [DecidableEq a] in
lemma jet_total (hM : ContDiff ℂ ω M.value) (v : Fin k → CSpace b) : iteratedFDeriv ℂ k (M.distributed A) 0 v = ∑ x, iteratedFDeriv ℂ k M.value 0 fun i => M.gather A x (v i) := by
  rw [show M.distributed A = (∑ x,M.value ∘ M.gather A x) by ext; simp [distributed], iteratedFDeriv_sum_apply
    (fun x _ => (hM.comp (M.gather A x).contDiff |>.contDiffAt.of_le le_top))]; simp [ContinuousLinearMap.iteratedFDeriv_comp_right _ hM _ (le_top (a:=(k:WithTop ℕ∞))), ContinuousMultilinearMap.compContinuousLinearMap_apply]

lemma prod_cell (x : Site n) (r : Fin k → Site n) : ∏ i, cell (r i) x = cell (∑ i,r i) x := by
  simp_rw [cell_duality _ x]; induction k with
  | zero => simp
  | succ k ih => rw [Fin.sum_univ_succ,Fin.prod_univ_succ,cell_add,← ih]
lemma jet_plane (hM : ContDiff ℂ ω M.value) {r : Fin k → Site n} {p : Fin k → Momentum} (hr : ∀ i, Matches (p i) (r i)) (v : Fin k → CSpace a) :
    iteratedFDeriv ℂ k (M.distributed A) 0 (fun i => plane A (r i) *ᵥ v i) = if ∑ i,r i=0 then (n.val:ℂ)^4 • M.monomial p v else 0 := by
  rw [jet_total M A hM]; simp_rw [fun i x => M.gather_wave A (hr i) x, ContinuousMultilinearMap.map_smul_univ, ← Finset.sum_smul,prod_cell]
  split
  next h => rw [h]; simp only [cell,mon_zero,mode_constant,Finset.sum_const,Finset.card_univ,site_card,nsmul_eq_mul,Nat.cast_pow,mul_one]; rfl
  next h => rw [sum_cell h,zero_smul]

omit [DecidableEq a] [Fintype a] in
lemma insertion_diff (v : CSpace a) : ContDiff ℂ ω (fun p => M.insertions p v) := contDiff_pi.mpr fun j => show ContDiff ℂ ω (fun p : Momentum => mode p (M.offset j) * v (M.leaf j)) by unfold mode; fun_prop

omit [Fintype a] [DecidableEq a] in
lemma monomial_diff (v : Fin k → CSpace a) : ContDiff ℂ ω (fun p => M.monomial p v) := by
  unfold monomial; simp_rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply ContinuousMultilinearMap.contDiff _ |>.comp (f:=fun (p : Fin k → Momentum) i => M.insertions (p i) (v i))
  exact contDiff_pi.mpr fun i => (M.insertion_diff (v i)).comp (contDiff_apply ℂ _ i)
omit [DecidableEq a] [Fintype a] in
lemma monomial_period (v : Fin k → Cover) (p : Fin k → Momentum) : M.monomial (fun i => p i+ Laurent.reciprocal (v i)) = M.monomial p := by simp only [monomial,insertions,mode_phase,mode_periodic,mul_one]
end Reader

variable [Fintype a] [DecidableEq a] [Fintype b] {A : Grid n b a} (M : ι → Reader a)

def total (A : Grid n b a) (x : CSpace b) := ∑' i,(M i).distributed A x

def source (p : Fin k → Momentum) := ∑' i, (M i).monomial p

structure Damped (M : ι → Reader a) (η ρ C : ℝ) : Prop where
  width : 0<η
  radius : 0<ρ
  smooth i : ContDiff ℂ ω (M i).value
  bill : ∃ g : ι → ℝ, SumBudget g C ∧ ∀ i x, ‖x‖ ≤ ρ → ‖(M i).value x‖ * Real.exp (η*(M i).sizeBound) ≤ g i
namespace Damped
variable {M} {η ρ C : ℝ} (h : Damped M η ρ C)
include h
omit [Fintype a] [DecidableEq a] in
lemma nonneg : 0≤C := by obtain ⟨_,hb,-⟩ := h.bill; exact (tsum_nonneg hb.1).trans hb.2.2
omit [Fintype a] [DecidableEq a] in
lemma field_budget (A : Grid n b a) : ∃ g : ι → ℝ, Summable g ∧ ∀ i, ∀ z∈ball (0:CSpace b) ρ, ‖(M i).distributed A z‖ ≤ g i := by
  obtain ⟨g,hg,H⟩ := h.bill
  refine ⟨fun i => Fintype.card (Site n) * g i,hg.2.1.mul_left _,fun i z hz => ?_⟩; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => g i) fun x _ => (le_mul_of_one_le_right (norm_nonneg _)
    (Real.one_le_exp (mul_nonneg h.width.le (by positivity)))).trans (H i _ ?_)).trans_eq (by simp))
  exact ((M i).gather_norm A _ _).trans (by simpa using (ball_subset_closedBall hz))
omit [Fintype a] [DecidableEq a] in
lemma distributed_diff (A : Grid n b a) (i : ι) : ContDiff ℂ ω ((M i).distributed A) := ContDiff.sum fun _ _ => (h.smooth i).comp ((M i).gather A _).contDiff
omit [Fintype a] [DecidableEq a] in
lemma total_diff : ContDiffAt ℂ ω (total M A) 0 := by obtain ⟨_,hg,H⟩ := h.field_budget A; exact (Work.F02.analytic_series _ h.radius (fun i => (h.distributed_diff A i).differentiable (by simp)) hg H).contDiffAt
omit [Fintype a] [DecidableEq a] in
lemma total_jets (v : Fin k → CSpace b) : HasSum (fun i => iteratedFDeriv ℂ k ((M i).distributed A) 0 v) (iteratedFDeriv ℂ k (total M A) 0 v) := by obtain ⟨_,hg,H⟩ := h.field_budget A; exact (ContinuousMultilinearMap.apply ℂ _ _ v).hasSum (iteratedFDeriv_hasSum h.radius k (h.distributed_diff A) hg H)

omit [DecidableEq a] h in
lemma freq_budget {η ρ} (hη : 0<η) (hρ : 0<ρ) (d : ℕ) : ∃ e D : ℝ,0<e ∧ e ≤ η ∧ 0<D ∧ ∀ {ι : Type} {M : ι → Reader a} {C} (_h : Damped M η ρ C), ∃ g : ι → ℝ, SumBudget g (D*C) ∧
    ∀ {k}, k≤d → ∀ p : Fin k → Momentum, (∀ j, Within e (p j)) → ∀ i, ‖(M i).monomial p‖ ≤ g i := by
  let e := η/(d+1)
  have he : 0<e := by unfold e; positivity
  obtain ⟨r,D,hr,hr',hD,H⟩ := degree_bound hρ d
  refine ⟨e,D,he,div_le_self hη.le (by simp),hD,fun {ι M C} h => ?_⟩
  obtain ⟨g,hg,hB⟩ := h.bill
  refine ⟨_,⟨fun i => mul_nonneg hD.le (hg.1 i), hg.2.1.mul_left _, by rw [tsum_mul_left]; gcongr; exact hg.2.2⟩,fun hk p hp i => ?_⟩
  let r := (M i).sizeBound
  have hx := H (h.smooth i) (C:=g i/Real.exp (η*r)) (x:=0) (fun z hz => (le_div_iff₀ (Real.exp_pos _)).mpr (hB i z (by simpa using (ball_subset_closedBall hz)))) (0:CSpace (M i).shape) (by simp [hr]) _ hk
  have ht : (∏ j, ‖(M i).insertions (p j)‖) ≤ Real.exp (η*r) := by
    apply (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => (M i).insertions_norm he.le _ (hp j)).trans
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; apply Real.exp_monotone
    rw [← mul_assoc]; gcongr; unfold e; rw [mul_div_assoc',div_le_iff₀ (by positivity)]; have := Nat.cast_le (α:=ℝ) |>.mpr hk; nlinarith
  have hb := hg.1 i
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_mul hx ht (by positivity) (by positivity)).trans_eq (by rw [mul_assoc,div_mul_cancel₀ _ (Real.exp_ne_zero _)]))

omit [DecidableEq a] in
lemma matched_summable {p : Fin k → Momentum} (hr : ∀ i,star (p i)=p i) : Summable fun i => (M i).monomial p := by
  obtain ⟨e,D,he,_,_,H⟩ := freq_budget (a:=a) h.width h.radius k
  obtain ⟨g,hg,H⟩ := H h
  exact .of_norm_bounded hg.2.1 (H le_rfl p fun i j => (Work.F07.realStrip _ he (hr i) j).le)

lemma total_plane {r : Fin k → Site n} {p : Fin k → Momentum} (hr : ∀ i, Matches (p i) (r i)) (v : Fin k → CSpace a) :
    iteratedFDeriv ℂ k (total M A) 0 (fun i => plane A (r i) *ᵥ v i) = if ∑ i,r i=0 then (n.val:ℂ)^4 • source M p v else 0 := by
  rw [← (h.total_jets ..).tsum_eq]; simp_rw [fun i => Reader.jet_plane (M i) A (h.smooth i) hr v]; split <;> simp [*,source, tsum_mul_left, ContinuousMultilinearMap.tsum_eval (h.matched_summable (fun i => (hr i).bar))]
end Damped
end YM.Push.Loops.Paths
