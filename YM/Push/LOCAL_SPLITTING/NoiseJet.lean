import YM.Push.LOCAL_SPLITTING.Marginal
import YM.Work.G07.Stencil

/-!
# Absolute one-step perturbation budgets on observed edges

No high-temperature or tree-locality input. Pointwise relative control of
all ordered derivatives of the observed noise (and hence the exact
shared-tag integral) by the vacuum integrand. Pay the displayed cardinality
and direction bounds only on the edges observed. Constants pre-side for fixed
observation count. Taking full observation here need not respect a local source budget as the
torus grows; no decay in distance or cancellation in these estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source Next.Foundations MeasureTheory Work.G07
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

def score (β : ℝ) (J : Edges c) (Q V : Config G c) := (-β*S.kernel.penalty) * ∑ i ∈ J, G.price (V i*(Q i)⁻¹)

theorem noisy_exp (β : ℝ) (J : Edges c) (Q V : Config G c) : noisy S β J Q V = (S.penaltyZ β G)⁻¹^J.card * Real.exp (score S β J Q V) := by
  simp only [noisy,Finset.prod_mul_distrib,Finset.prod_const,StepData.penaltyWeight,score,Finset.mul_sum,Real.exp_sum]

theorem noisy_pos (β : ℝ) (J : Edges c) (Q V : Config G c) : 0 < noisy S β J Q V :=
  Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)

private def row (β : ℝ) (g : G.El) : G.Mat →L[ℝ] ℝ := (β*S.kernel.penalty) • (pairing ∘L (ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat g⁻¹))

private theorem linearScore (β : ℝ) (J : Edges c) (Q : Config G c) : score S β J Q = (fun _ => -β*S.kernel.penalty*J.card) + ∑ i∈J,(row S β (Q i) ∘ fun V => G.mat (V i)) := by
  funext V
  simp only [Pi.add_apply,Finset.sum_apply, score,paired,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul, mul_one, mul_sub,comp_apply,row,Finset.mul_sum, neg_mul]; simp [sub_eq_add_neg]; rfl

private theorem chart_link (V : Config G c) (i : Edge (Site c)) (k : ℕ) : Chart k (fun W => G.mat (W i)) V :=
  ((((G.exp_jet.of_le le_top).comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)

private theorem chart_row (β : ℝ) (V Q : Config G c) (k : ℕ) (i : Edge (Site c)) : Chart k (row S β (Q i) ∘ fun W => G.mat (W i)) V := (row S β (Q i)).contDiff.contDiffAt.comp _ (chart_link V i k)

theorem chart_score (β : ℝ) (J : Edges c) (Q V : Config G c) (k : ℕ) : Chart k (score S β J Q) V := by
  rw [linearScore]; exact contDiffAt_const.add (by
    simp only [comp_def,Finset.sum_apply]; exact ContDiffAt.sum fun i _ => chart_row S β V Q k i)

theorem chart_noisy (β : ℝ) (J : Edges c) (Q V : Config G c) (k : ℕ) : Chart k (noisy S β J Q) V := by
  rw [funext (noisy_exp S β J Q)]; exact contDiffAt_const.mul (chart_score S β J Q V k).exp

def pairingNorm (G : Gauge) := (pairing (G:=G)).opNorm

theorem pairingNorm_nonneg (G : Gauge) : 0 ≤ pairingNorm G := pairing.opNorm_nonneg

/-- Uses a common *absolute* bound r ≥ 0 on the norm of each varying color
at observed links only. No hypothesis on paths, other directions, |β|,
minimum side etc.; Frobenius convention in G.colorScale & pairing.
-/
def scorePrice (G : Gauge) (u : ℝ) (k j : ℕ) (r : ℝ) := 1 + (j:ℝ) * (|u| * pairingNorm G * (‖(1:G.Mat)‖ * (1+G.colorScale*r)^k))

theorem scorePrice_ge (G : Gauge) (u : ℝ) (k j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ scorePrice G u k j r := le_add_of_nonneg_right (by positivity [G.colorScale_pos,pairingNorm_nonneg G])

theorem score_jet (β : ℝ) (J : Edges c) (Q V : Config G c) (l : List (Directions G c)) {k : ℕ} {r : ℝ}
    (h : l.length ≤ k) (hl : l ≠ []) (hr : 0 ≤ r) (H : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) :
    ‖leftDerivs (score S β J Q) l V‖ ≤ scorePrice G (β*S.kernel.penalty) k J.card r := by
  let a := β*S.kernel.penalty
  have hk : 1 ≤ 1+G.colorScale*r := le_add_of_nonneg_right (mul_nonneg G.colorScale_pos.le hr)
  let g (i : Edge (Site c)) := (row S β (Q i) ∘ fun W : Config G c => G.mat (W i))
  have hg i : Chart k (g i) V := chart_row S β V Q k i
  have hsum : Chart k (∑ i∈J,g i) V := by unfold Chart; simp only [comp_def,Finset.sum_apply]; exact ContDiffAt.sum (fun i _ => hg i)
  rw [linearScore, left_add (g:=∑ i∈J, g i) l contDiffAt_const hsum h, left_const,if_neg hl,zero_add,left_sum _ _ _ _ (fun i _ => hg i) h]
  refine (norm_sum_le ..).trans (le_trans ?_ (le_add_of_nonneg_left zero_le_one))
  have he i (hi : i∈J) : ‖leftDerivs (g i) l V‖ ≤ |a| *pairingNorm G * (‖(1:G.Mat)‖*(1+G.colorScale*r)^k) := by
    rw [show leftDerivs (g i) l V = _ from left_linear (row S β (Q i)) l (chart_link V i k) h, left_link, row, smul_apply, norm_smul,Real.norm_eq_abs,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    refine (pairing.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (pairingNorm_nonneg G))
    change ‖linkPrefix i l * G.mat (V i) * G.mat (Q i)⁻¹‖ ≤ _
    rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star _),Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
    apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk h) (norm_nonneg (1:G.Mat)))
    clear h hl; induction l with
    | nil => simp [linkPrefix]
    | cons A l ih =>
      rw [linkPrefix_cons, List.length_cons,pow_succ,← mul_assoc]; apply (norm_mul_le ..).trans
      exact mul_le_mul (ih (fun v hv => H v (by simp [hv]))) ((G.colorMat_norm _).trans_le ((mul_le_mul_of_nonneg_left (H A (by simp) i hi) G.colorScale_pos.le).trans (le_add_of_nonneg_left zero_le_one))) (norm_nonneg _) (by positivity)
  simpa [a] using Finset.sum_le_sum he

private theorem noisy_first (β : ℝ) (J : Edges c) (Q : Config G c) (A : Directions G c) :
    leftDerivs (noisy S β J Q) [A] = noisy S β J Q * leftDerivs (score S β J Q) [A] := by
  funext V; rw [funext (noisy_exp S β J Q)]
  have he := ((left_has A (l:=[]) (by simp) (chart_score S β J Q V 1)).exp.const_mul ((S.penaltyZ β G)⁻¹^J.card)).deriv
  simpa only [show increment V ((0:ℝ) • A) = V by simp [at_zero_increment],leftDerivs,Pi.mul_apply,mul_assoc] using he

def noiseFactor (G : Gauge) (u : ℝ) (k j : ℕ) (r : ℝ) := 2^k*scorePrice G u k j r

theorem noiseFactor_ge (G : Gauge) (u : ℝ) (k j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ noiseFactor G u k j r := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (scorePrice_ge _ _ _ _ hr)

theorem noisy_bound (β : ℝ) (J : Edges c) (Q V : Config G c) {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (l : List (Directions G c))
    (hl : l.length ≤ k) (H : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) :
    ‖leftDerivs (noisy S β J Q) l V‖ ≤ noiseFactor G (β*S.kernel.penalty) k J.card r ^ l.length * noisy S β J Q V := by
  let C := scorePrice G (β*S.kernel.penalty) k J.card r
  let K := noiseFactor G (β*S.kernel.penalty) k J.card r
  have hp := noisy_pos S β J Q V
  induction he : l.length using Nat.strong_induction_on generalizing l with
  | h j ih =>
    induction l using List.reverseRecOn with
    | nil => simpa only [← he,List.length_nil,leftDerivs,pow_zero,one_mul] using (Real.norm_of_nonneg hp.le).le
    | append_singleton s A _ =>
      rw [left_append, noisy_first]
      have hs (l : List (Directions G c)) (hle : l.length ≤ s.length) (hl' : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) : ‖leftDerivs (noisy S β J Q) l V‖ ≤ K^s.length * noisy S β J Q V := by
        have hx := ih l.length (by simp at he; omega) l (by simp at hl; omega) hl' rfl
        exact hx.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (noiseFactor_ge _ _ _ _ hr) hle) hp.le)
      have hA (l : List (Directions G c)) (hle : l.length ≤ s.length) (hl' : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) : ‖leftDerivs (leftDerivs (score S β J Q) [A]) l V‖ ≤ C := by
        rw [← left_append]; exact score_jet S β J Q V _ (by simp at hl ⊢; omega) (by simp) hr (by intro v hv; rcases List.mem_append.mp hv with hv|hv; exact hl' v hv; exact H v (List.mem_append_right _ hv))
      have hb := left_mul_bound (chart_noisy S β J Q V s.length) (leftDerivs_chart [A] s.length (chart_score S β J Q V _)) hs hA s le_rfl (fun v hv => H v (by simp [hv]))
      apply hb.trans; simp only [List.length_append,List.length_singleton] at he
      rw [← he, pow_succ]
      refine (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (n:=k) (by norm_num) (by simp at hl; omega)) (by positivity [scorePrice_ge G (β*S.kernel.penalty) k J.card hr,noiseFactor_ge G (β*S.kernel.penalty) k J.card hr] : 0 ≤ K^s.length * noisy S β J Q V*C)).trans_eq ?_
      unfold K noiseFactor C; ring

section Pass
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bound_pass (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (V : Config G c) {k : ℕ} {r a : ℝ} {D : Config G f → ℝ} {F : Config G f → E}
    (hr : 0 ≤ r) (hf : Integrable F (prior G f)) (hd : Integrable D (prior G f)) (hF : ∀ U, ‖F U‖ ≤ a*D U)
    (l : List (Directions G c)) (hl : l.length ≤ k) (H : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) :
    ‖leftDerivs (pass S β J F) l V‖ ≤ (noiseFactor G (β*S.kernel.penalty) k J.card r ^ k * a) * pass S β J D V := by
  let C := noiseFactor G (β*S.kernel.penalty) k J.card r ^ k
  have he U : ‖weights S U (fun Q => leftDerivs (noisy S β J Q) l V)‖ ≤ C*pdf S β J U V := by
    unfold pdf weights; rw [Finset.mul_sum]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum
    intro t _; rw [norm_mul,Real.norm_of_nonneg (S.likelihood_pos ..),mul_left_comm]; exact mul_le_mul_of_nonneg_left ((noisy_bound S β J _ V hr l hl H).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (noiseFactor_ge _ _ _ _ hr) hl) (noisy_pos S β J _ V).le)) (S.likelihood_pos ..)
  rw [left_pass S β J h hf V l,pass,← integral_const_mul]; apply norm_integral_le_of_norm_le ((pdf_integrable S β J h V hd).const_mul _)
  exact .of_forall fun U => (norm_smul ..).trans_le ((mul_le_mul (he U) (hF U) (norm_nonneg _) ((norm_nonneg _).trans (he _))).trans_eq (by unfold C; ring))
end Pass
end YM.Push.Local.Kernel
