import YM.Labels.Jet
import YM.Analysis.Homogeneous

/-!
# Ordinary curvature jets modulo linear Bianchi

Use *Taylor coefficients*. Identify with actual label
reference jets, with no trace condition until the equation space.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Labels Tensor Analysis ContinuousMultilinearMap WithLp
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff

variable {G : Gauge} {j : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Axis derivative. -/
def grad (i : Axis) := @D E4 F _ _ _ _ (basis i)

theorem grad_smooth {f : E4 → F} {m n : WithTop ℕ∞} {x} (i) (hf : ContDiffAt ℝ n f x) (h : m+1 ≤ n) :
    ContDiffAt ℝ m (grad i f) x := dSmooth hf (basis i) h

theorem grad_comm {f : E4 → F} {x} (hf : ContDiffAt ℝ 2 f x) (a b : Axis) :
    grad a (grad b f) x = grad b (grad a f) x := commuteD hf ..

abbrev compAxis (i : Axis) : E4 →L[ℝ] ℝ := EuclideanSpace.proj i

theorem grad_self (A : Axis → T E4 F j) (i : Axis) (x : E4) :
    grad i (fun z : E4 => ∑ k : Axis, z k • diagonal (A k) z) x =
    diagonal (A i) x + ∑ k : Axis, x k • grad i (diagonal (A k)) x := by
  have H (k : Axis) := ((diag_smooth (A k) ∞).differentiable (by simp) x)
  have L (k : Axis) : HasFDerivAt (fun y : E4 => y k) (compAxis k) x :=
    (compAxis k).hasFDerivAt
  have W (k) := (L k).smul (H k).hasFDerivAt
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => W k).fderiv
  change fderiv ℝ (fun z : E4 => ∑ k : Axis, z k • diagonal (A k) z) x = _ at h
  rw [grad,D,h,sum_apply]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply]
  change ∑ k : Axis, (x k • grad i (diagonal (A k)) x + (basis i k) • diagonal (A k) x) = _
  simp [Finset.sum_add_distrib, ite_smul, add_comm,grad]

theorem grad_euler (A : T E4 F j) (h : Sym A) (x : E4) :
    ∑ k : Axis, x k • grad k (diagonal A) x = (j : ℝ) • diagonal A x := by
  have he : ∑ k : Axis, x k • basis k = x := by
    apply PiLp.ext; intro i; simp
  rw [← Tensor.Euler A h]
  conv_rhs => arg 2; rw [← he]
  rw [_root_.map_sum]; simp only [map_smul]; rfl

/-- A homogeneous two-tensor with j inputs. -/
abbrev TwoJet (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) := Axis → Axis → T E4 F j

/-- Closed differential two-forms with values in physical color coordinates. -/
structure ClosedJet (A : TwoJet F j) : Prop where
  coeffSym : ∀ i l, Sym (A i l)
  antisymmetric : ∀ i l, A i l = - A l i
  closed : ∀ a b c : Axis, ∀ x : E4,
    grad a (diagonal (A b c)) x + grad b (diagonal (A c a)) x + grad c (diagonal (A a b)) x = 0

variable (F j) in
def formSpace : Submodule ℝ (TwoJet F j) where
  carrier := {A | ClosedJet A}
  zero_mem' := by
    constructor
    · simp [Tensor.Sym]
    · simp
    intro a b c x
    change grad a (fun _ => (0:F)) x + grad b (fun _ => (0:F)) x + grad c (fun _ => (0:F)) x = _
    simp [grad,D]
  add_mem' := by
    rintro x y (hx : ClosedJet _) (hy : ClosedJet _)
    refine ⟨fun i l r s => ?_, fun i l => ?_, fun a b c z => ?_⟩
    · simp [hx.coeffSym i l r s, hy.coeffSym i l r s]
    · simp only [Pi.add_apply]; nth_rw 1 [hx.antisymmetric i l]; nth_rw 1 [hy.antisymmetric i l]; abel
    have he (i l k) : grad k (diagonal ((x+y) i l)) z =
        grad k (diagonal (x i l)) z + grad k (diagonal (y i l)) z := by
      change fderiv ℝ (diagonal (x i l)+diagonal (y i l)) z _ = _
      rw [fderiv_add ((diag_smooth _ ∞).differentiable (by simp) _)
        ((diag_smooth _ ∞).differentiable (by simp) _)]
      rfl
    rw [he b c, he c a, he a b, show 0 = (0 : F) + 0 by simp]
    nth_rw 1 [← hx.closed a b c z]; nth_rw 1 [← hy.closed a b c z]; abel
  smul_mem' := by
    rintro t x (hx : ClosedJet _)
    refine ⟨fun i l r s => ?_,fun i l => ?_,fun a b c z => ?_⟩
    · simp [hx.coeffSym i l r s]
    · simp only [Pi.smul_apply]; nth_rw 1 [hx.antisymmetric i l]; simp
    have he (i l k) : grad k (diagonal ((t • x) i l)) z = t • grad k (diagonal (x i l)) z := by
      change fderiv ℝ (t • (diagonal (x i l))) z _ = _
      rw [fderiv_const_smul ((diag_smooth _ ∞).differentiable (by simp) _)]
      rfl
    simp_rw [he, ← smul_add, hx.closed, smul_zero]

def takeCurl (A : Labels.Taylor G j) (i l : Axis) : T E4 G.Color j :=
  ((j+1 : ℕ) : ℝ) • ((A.val l).curryLeft (basis i) - (A.val i).curryLeft (basis l))

theorem takeCurl_diag (A : Labels.Taylor G j) (i l : Axis) :
    diagonal (takeCurl A i l) = grad i (A.value l) - grad l (A.value i) := by
  funext x
  simp only [Pi.sub_apply, grad, D, takeCurl]
  unfold Taylor.value
  rw [differential_diagonal _ (A.property.1 i), differential_diagonal _ (A.property.1 l)]
  simp only [diagonal, Nat.cast_smul_eq_nsmul, smul_apply, sub_apply, smul_sub]

theorem closedCurl (A : Labels.Taylor G j) : ClosedJet (takeCurl A) := by
  constructor
  · intro i l r s
    simp only [takeCurl, smul_apply, sub_apply, freeze_sym _ (A.property.1 i) _ r s,
      freeze_sym _ (A.property.1 l) _ r s]
  · intro i l; simp [takeCurl, ← smul_neg]
  intro a b c x
  have hs (i) (m) (z) : ContDiffAt ℝ m (A.value i) z := (diag_smooth (A.val i) _).contDiffAt
  have h (a b i) : DifferentiableAt ℝ (grad a (A.value b)) i := (grad_smooth _ (hs b ∞ i)
    (m := ∞) (by simp)).differentiableAt (by simp)
  have he (a b c) : grad a (diagonal (takeCurl A b c)) x =
      grad a (grad b (A.value c)) x - grad a (grad c (A.value b)) x := by
    rw [takeCurl_diag]
    change (fderiv ℝ (grad b (A.value c) - grad c (A.value b)) x) (basis a) = _
    rw [fderiv_sub (h b c x) (h c b x)]
    rfl
  rw [he a b c, he b c a, he c a b]
  nth_rw 1 [grad_comm (hs c 2 x) a b]
  nth_rw 1 [grad_comm (hs b 2 x) a c]
  nth_rw 1 [grad_comm (hs a 2 x) b c]
  abel

def contracted {Q : TwoJet G.Color j} (h : ClosedJet Q) : Labels.Taylor G j :=
  ⟨fun i => (↑(j+2 : ℕ) : ℝ)⁻¹ • ∑ k, added (Q k i) (compAxis k), by
  constructor
  · intro i v s
    simp only [smul_apply, sum_apply, added_sym _ _ v s]
  intro z
  simp only [diagonal, smul_apply, sum_apply]
  let t := ∑ i : Axis, z i • ((↑(j+2 : ℕ) : ℝ)⁻¹ • ∑ j,
    z j • diagonal (Q j i) z)
  simp_rw [show ∀ i k, added (Q k i) (compAxis k) (fun _ => z) = z k • diagonal (Q k i) z from
    fun _ _ ↦ added_diag ..]
  change t = 0
  have H : t = - t := by
    dsimp only [t]
    simp_rw [Finset.smul_sum, ← Finset.sum_neg_distrib, ← smul_neg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    nth_rw 1 [h.antisymmetric a b]
    simp only [smul_smul, diagonal, neg_apply]
    congr 1; ring
  have he : (2:ℝ) • t = 0 := by rw [two_smul]; nth_rw 1 [H]; simp
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)⟩

theorem contracted_diag {Q : TwoJet G.Color j} (h : ClosedJet Q) (i : Axis) (x : E4) :
    (contracted h).value i x = (↑(j+2 : ℕ) : ℝ)⁻¹ • ∑ k, x k • diagonal (Q k i) x := by
  unfold Taylor.value contracted
  simp only [diagonal, smul_apply, sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => added_diag ..)

theorem curl_inverse {Q : TwoJet G.Color j} (h : ClosedJet Q) : takeCurl (contracted h) = Q := by
  funext i l
  apply ext_diag _ _ ((closedCurl _).coeffSym i l) (h.coeffSym i l); funext x
  rw [takeCurl_diag]
  let c : ℝ := (j+2 : ℕ)
  have he (i l : Axis) : grad i ((contracted h).value l) x =
      c⁻¹ • (diagonal (Q i l) x + ∑ k : Axis, x k • grad i (diagonal (Q k l)) x) := by
    rw [← grad_self (fun k => Q k l) i x]
    rw [show (contracted h).value l = _ from funext (contracted_diag h l)]
    unfold grad D
    rw [fderiv_fun_const_smul]
    · rfl
    exact DifferentiableAt.fun_sum fun b _ => (compAxis b).differentiableAt.smul ((diag_smooth _ ∞).differentiable (by simp) _)
  have hz (i l k) : grad i (diagonal (Q l k)) x = -grad i (diagonal (Q k l)) x := by
    nth_rw 1 [h.antisymmetric l k]
    change fderiv ℝ (-diagonal (Q k l)) x _ = _
    rw [fderiv_neg]; rfl
  have hw (k) : grad i (diagonal (Q k l)) x - grad l (diagonal (Q k i)) x =
      grad k (diagonal (Q i l)) x := by
    have H := h.closed k i l x
    conv at H => lhs; arg 1; arg 2; rw [hz]
    rw [← add_right_cancel_iff (a := (-(grad i (diagonal (Q k l)) x) + grad l (diagonal (Q k i)) x))]
    rw [add_assoc] at H
    rw [H]
    abel
  simp only [Pi.sub_apply, he]
  rw [← smul_sub, add_sub_add_comm, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub, hw, grad_euler (Q i l) (h.coeffSym i l) x]
  -- Antisymmetry in the second derivative-of-x term
  rw [show diagonal (Q l i) x = - diagonal (Q i l) x from
    congr_arg (fun A : T E4 G.Color j => diagonal A x) (h.antisymmetric l i)]
  rw [sub_neg_eq_add, ← two_smul ℝ, ← add_smul, add_comm (2 : ℝ), show (j:ℝ)+2=c by push_cast [c]; rfl,
    smul_smul, inv_mul_cancel₀ (by dsimp [c]; positivity), one_smul]

theorem potential_recover (A : Taylor G j) : contracted (closedCurl A) = A := by
  apply Taylor.value_ext
  funext i x
  rw [contracted_diag]
  have hz := grad_self A.val i x
  rw [show (fun z : E4 ↦ ∑ k : Axis, z k • diagonal (A.val k) z) = fun _ => 0 from
    funext A.property.2] at hz
  have hd : grad i (fun _ : E4 => (0:G.Color)) x = 0 := by simp [grad,D]
  rw [hd] at hz
  have he : ∑ k : Axis, x k • grad i (A.value k) x = - A.value i x := by
    exact eq_neg_of_add_eq_zero_right hz.symm
  simp_rw [takeCurl_diag, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, he, sub_neg_eq_add]
  change (↑(j+2 : ℕ) : ℝ)⁻¹ • ((∑ k : Axis, x k • grad k (diagonal (A.val i)) x) + _) = _
  rw [grad_euler _ (A.property.1 i) x]
  change (↑(j+2 : ℕ) : ℝ)⁻¹ • (((↑(j+1 : ℕ) : ℝ)) • A.value i x + _) = _
  nth_rw 2 [← one_smul ℝ (A.value i x)]
  rw [← add_smul, show ((↑(j+1 : ℕ) : ℝ)+1) = ↑(j+2 : ℕ) by norm_cast,
    smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Real equivalence degree by degree. G-invariance can be imposed on polynomials
of these actual closed jets. -/
def potential : Labels.Taylor G j ≃ₗ[ℝ] ↥(formSpace j G.Color) where
  toFun A := ⟨takeCurl A,closedCurl A⟩
  invFun Q := contracted Q.property
  left_inv := potential_recover
  right_inv Q := Subtype.ext (curl_inverse Q.property)
  map_add' A B := by apply Subtype.ext; funext i l; ext1 z; simp [takeCurl,smul_sub,smul_add]; abel
  map_smul' u A := by apply Subtype.ext; funext i l; ext1 z; simp [takeCurl,smul_sub,smul_comm u]

end YM.Maxwell
