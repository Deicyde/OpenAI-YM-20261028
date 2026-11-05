import YM.Planned.ATOM_REGULAR_ESTIMATE.Degree
/-! Degree calculus for testing radial connections on a whole link (both ends).
A shorthand `diagonal` is used in translations; `slot` derivatives below
initialize using actual `SolvesLink`, not endpoint fitting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Tensor MeasureTheory Next.Foundations
open scoped Topology BigOperators ContDiff Classical

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {n j m : ℕ}

namespace Degree

def twist (A : T E F n) (v : E) (t : ℕ) (x : E) :=
    ∑ s : Finset (Fin n) with s.card=t,A (fun i => if i∈s then v else x)

lemma twist_degree (A : T E F n) (v : E) (t : ℕ) : Degree (n-t) (twist A v t) := by
  let y (s : Finset (Fin n)) : E → F := fun x => A (fun i => if i∈s then v else x)
  rw [show twist A v t = ∑ i : Finset (Fin n) with i.card=t, y i from funext fun x => by rw [Finset.sum_apply]; rfl]
  refine Degree.sum _ (fun i hi => ?_)
  have h : i.card=t := (Finset.mem_filter.mp hi).2
  apply Degree.of_hom
  · refine (A.contDiff.contDiffAt.comp 0 (f:=fun x : E => (fun a => if a∈i then v else x)) (contDiffAt_pi.mpr (fun j => ?_)))
    by_cases hj : j∈i
    · simp only [if_pos hj]; exact contDiffAt_const
    simp only [if_neg hj]; exact contDiffAt_id
  intro x s; unfold y
  rw [show (fun j => if j ∈ i then v else s • x) = fun j => (if j∈i then 1 else s) • (if j∈i then v else x) from funext fun j => by split <;> simp [*], A.map_smul_univ,Finset.prod_ite]
  congr 1
  rw [show (Finset.univ.filter (fun x => ¬ x ∈ i)) = iᶜ by ext; simp]; simp [Finset.card_compl,h]

lemma twist_expansion (A : T E F n) (v x : E) (u : ℝ) :
    diagonal A (x+u • v) = ∑ i ∈ Finset.range (n+1), u^i • twist A v i x := by
  rw [add_comm]
  change A ((fun _ => u • v)+(fun _ => x)) = _
  rw [A.map_add_univ]
  simp_rw [twist, Finset.smul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hv : s.card ∈ Finset.range (n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ s).trans_eq (Fintype.card_fin n)))
  rw [Finset.sum_eq_single s.card,if_pos rfl, show s.piecewise (fun _ => u • v) (fun _ => x) =
      fun j => (if j ∈ s then u else 1) • (if j∈s then v else x) from funext fun j => by by_cases h : j∈s <;> simp [h], A.map_smul_univ, Finset.prod_ite]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  exact fun H => False.elim (H hv)

lemma twist_zero (A : T E F n) (v x : E) : twist A v 0 x = diagonal A x := by
  classical simp [twist, Finset.sum_filter, diagonal]

lemma monojet (v : F) (t m : ℕ) : iteratedDeriv m (fun u : ℝ => u^t • v) 0 =
    if m=t then (m.factorial:ℝ) • v else 0 := by
  have hp : ContDiffAt ℝ m (fun u : ℝ => u^t) 0 := by fun_prop
  rw [iteratedDeriv_smul_const hp,iteratedDeriv_pow]
  rcases lt_trichotomy t m with H|H|H
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr H, H.ne']
  · rw [H]; simp [Nat.descFactorial_self]
  simp [H.ne, tsub_pos_iff_lt.mpr H |>.ne']

/-- Only at positive degree (putative `n ≥ 1`). -/
lemma twist_first (A : T E F (n+1)) (v x : E) :
    twist A v 1 x = Analysis.D v (diagonal A) x := by
  let f (t : ℕ) (u : ℝ) := u^t • twist A v t x
  let d (u : ℝ) := x+u • v
  have hg : diagonal A ∘ d = ∑ i∈Finset.range (n+1+1),f i := funext fun u => by
    rw [Finset.sum_apply]; exact twist_expansion ..
  have h : d 0=x := by simp [d]
  have ht : HasDerivAt d v 0 := by unfold d; simpa using! (((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x)
  have hd : iteratedDeriv 1 (diagonal A ∘ d) 0 = Analysis.D v (diagonal A) x := by
    rw [iteratedDeriv_one]; unfold Analysis.D
    exact ((((diag_smooth A 1).differentiable (by simp) x).hasFDerivAt).comp_hasDerivAt_of_eq 0 ht h.symm).deriv
  have he (i : ℕ) : ContDiffAt ℝ ((1:ℕ):WithTop ℕ∞) (f i) 0 := by unfold f; fun_prop
  rw [← hd, hg,iteratedDeriv_sum (fun i _ => he i)]
  unfold f; simp only [monojet]; rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; rw [if_neg hb.symm]
  simp

protected lemma translate {k : ℕ} (h : Degree k f) (v : E) : Degree k (fun y => f (y+v)) := by
  obtain ⟨a,ha⟩ := h
  have he (y : E) : f (y+v) = ∑ i∈Finset.range (k+1),∑ j∈Finset.range (i+1), twist (a i) v j y := by
    rw [ha,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _ => by simpa using twist_expansion (a i) v y 1
  rw [show (fun y => f (y+v)) = ∑ i∈Finset.range (k+1),∑ j∈Finset.range (i+1), twist (a i) v j from funext fun y => by simp_rw [Finset.sum_apply]; rw [he]]
  refine Degree.sum _ (fun i hi => Degree.sum _ fun j _ => (twist_degree _ _ _).mono ?_)
  exact (Nat.sub_le i j).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

lemma diagonal_difference (A : T E F n) (v : E) : Degree (n-1) (fun x => diagonal A (x+v) - diagonal A x) := by
  rw [show (fun x => diagonal A (x+v) - diagonal A x) = ∑ i∈Finset.range n, twist A v (i+1) from funext fun x => by
    have he := twist_expansion A v x 1; rw [Finset.sum_range_succ'] at he; simpa [sub_eq_iff_eq_add,Finset.sum_apply,twist_zero] using he]
  exact Degree.sum _ (fun i _ => (twist_degree _ _ _).mono (by omega))

protected lemma difference (h : Degree n f) (v : E) : Degree (n-1) (fun x => f (x+v) - f x) := by
  obtain ⟨a,ha⟩ := h
  rw [show (fun x => f (x+v) - f x) = ∑ i∈Finset.range (n+1), (fun x => diagonal (a i) (x+v) - diagonal (a i) x) from funext fun x => by simp [ha,Finset.sum_apply,Finset.sum_sub_distrib]]
  refine Degree.sum _ fun i hi => (diagonal_difference ..).mono ?_
  have := Finset.mem_range.mp hi; omega

lemma diagonal_rest (A : T E F (n+1)) (v : E) :
    Degree (n-1) (fun x => diagonal A (x+v) - diagonal A x - Analysis.D v (diagonal A) x) := by
  rw [show (fun x => _) = ∑ i∈Finset.range n, twist A v (i+2) from funext fun x => by
    have he := twist_expansion A v x 1; rw [Finset.sum_range_succ',Finset.sum_range_succ'] at he; simpa [sub_eq_iff_eq_add,Finset.sum_apply,twist_zero,twist_first] using he]
  refine Degree.sum _ fun i _ => (twist_degree ..).mono (by omega)

lemma diagonal_exact_one (A : T E F 1) (v : E) : ∀ x,
    diagonal A (x+v) - diagonal A x = Analysis.D v (diagonal A) x := fun x =>
  sub_eq_iff_eq_add.mpr (by
    have he := twist_expansion A v x 1
    simpa [Finset.sum_range_succ,twist_zero, twist_first (n:=0),add_comm] using he)

lemma integrated_degree [CompleteSpace F] (A : T E F n) (v : E) : Degree (n-1) (fun x =>
    (∫ t : ℝ in 0..1, diagonal A (x+t • v))-diagonal A x) := by
  let c (i : ℕ) := (∫ t : ℝ in 0..1,t^(i+1))
  have he x : (∫ t : ℝ in 0..1, diagonal A (x+t • v)) = (∑ i∈Finset.range n, c i • twist A v (i+1) x) + diagonal A x := by
    simp_rw [twist_expansion A v x]
    rw [intervalIntegral.integral_finsetSum (fun i _ => (show Continuous fun t : ℝ => t^i • twist A v i x by fun_prop).intervalIntegrable ..)]
    rw [Finset.sum_range_succ']; simp_rw [intervalIntegral.integral_smul_const]
    simp only [pow_zero, intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,one_smul,twist_zero]; rfl
  rw [show (fun x => (∫ t : ℝ in 0..1, diagonal A (x+t • v)) - _) = ∑ i∈Finset.range n, c i • twist A v (i+1) from
    funext fun x => by simp only [he,add_sub_cancel_right,Pi.smul_apply,Finset.sum_apply]]
  exact Degree.sum _ (fun i _ => Degree.smul ((twist_degree ..).mono (by omega)) _)
end Degree
end
end YM.Planned.AtomRegular
