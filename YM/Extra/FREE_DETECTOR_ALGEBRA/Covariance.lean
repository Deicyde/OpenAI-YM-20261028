import YM.Extra.FREE_DETECTOR_ALGEBRA.Forms

set_option warningAsError false

/-! Rotation of jets/tensor duals. In particular preserve all actual
Bianchi/Maxwell constraints. -/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}

def mov (s : Ortho) : E4 →L[ℝ] E4 := (Ortho.motion s).toContinuousLinearMap

@[simp] theorem mov_apply (s : Ortho) (x : E4) : mov s x = Ortho.move s x := rfl

lemma mov_inv_decomp (s : Ortho) (a : Axis) : mov s⁻¹ (basis a) = ∑ b, s.val a b • basis b := by
  rw [mov_apply]
  have he := axis_resolve (Ortho.move s⁻¹ (basis a))
  rw [← he]; apply Finset.sum_congr rfl; intro b _; rw [Ortho.move,M4.move_basis]; rfl

/-- Action on directions of a tensor. -/
def byDir (s : Ortho) : T E4 F j →ₗ[ℝ] T E4 F j :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => mov s⁻¹)).toLinearMap

/-- Action on directions and on both two-form indices. -/
def carry (s : Ortho) : TwoJet F j →ₗ[ℝ] TwoJet F j where
  toFun Q := bi s.val (fun i m => byDir s (Q i m))
  map_add' Q R := by
    change bi s.val _ = _
    rw [← map_add (bi s.val)]
    congr 1
  map_smul' t Q := by
    change bi s.val _ = _
    rw [← map_smul (bi s.val)]
    congr 1

theorem carry_eval (s : Ortho) (Q : TwoJet F j) (i m : Axis) (v) : carry s Q i m v =
    bi s.val (fun a b => Q a b (fun l => mov s⁻¹ (v l))) i m := by
  change bi s.val (fun i m => byDir s (Q i m)) i m v = _
  simp only [bi_eval,sum_apply,smul_apply]; rfl

theorem carry_id (Q : TwoJet F j) : carry 1 Q = Q := by
  ext1 i; ext1 m; ext1 v
  simp only [carry_eval,inv_one,mov_apply,Ortho.move_one]; exact congr_fun (congr_fun (bi_one _) i) m

theorem carry_mul (s t : Ortho) (Q : TwoJet F j) : carry (s*t) Q = carry s (carry t Q) := by
  ext1 i; ext1 m; ext1 v
  simp_rw [carry_eval,mov_apply,mul_inv_rev,Ortho.move_mul]
  have he := bi_mul s.val t.val (fun i m => Q i m (fun j => Ortho.move t⁻¹ (Ortho.move s⁻¹ (v j))))
  exact congr_fun (congr_fun he i) m

def reel (s : Ortho) (A : Maxwell.Field F) (i m : Axis) (x : E4) : F :=
    bi s.val (fun a b => A a b (mov s⁻¹ x)) i m

theorem carry_diag (s : Ortho) (Q : TwoJet F j) (i m : Axis) : diagonal (carry s Q i m) =
    reel s (fun i m => diagonal (Q i m)) i m := by
  funext x; exact carry_eval ..

theorem mov_gradient (s : Ortho) (a : Axis) {f : E4 → F} {x}
    (hf : ContDiffAt ℝ ∞ f (mov s⁻¹ x)) :
    grad a (fun y => f (mov s⁻¹ y)) x = ∑ i : Axis, s.val a i • grad i f (mov s⁻¹ x) := by
  unfold grad D
  have hd := ((hf.differentiableAt (by simp)).hasFDerivAt.comp x (mov s⁻¹).hasFDerivAt).fderiv
  rw [show fderiv ℝ (fun y => f (mov s⁻¹ y)) x = _ from hd,ContinuousLinearMap.comp_apply,mov_inv_decomp,_root_.map_sum]
  simp_rw [_root_.map_smul]

/-- 3-index action. -/
def tri (s : M4) (v : Axis → Axis → Axis → F) (i j k : Axis) :=
    ∑ a : Axis, ∑ b : Axis, ∑ c : Axis, s i a • s j b • s k c • v a b c

theorem reel_gradient (s : Ortho) {f : Maxwell.Field F} {x}
    (hf : ∀ i m, ContDiffAt ℝ ∞ (f i m) (mov s⁻¹ x)) (a i m : Axis) :
    grad a (reel s f i m) x = tri s.val (fun i m a => grad a (f i m) (mov s⁻¹ x)) i m a := by
  let T (u v : Axis) := fun x => s.val i u • s.val m v • f u v (mov s⁻¹ x)
  have hs u v : ContDiffAt ℝ ∞ (f u v ∘ mov s⁻¹) x := (hf u v).comp x (mov s⁻¹).contDiff.contDiffAt
  have ht u v : ContDiffAt ℝ ∞ (T u v) x := contDiffAt_const.smul (contDiffAt_const.smul (hs u v))
  have he u v : grad a (T u v) x = s.val i u • s.val m v • ∑ b : Axis, s.val a b • grad b (f u v) (mov s⁻¹ x) := by
    rw [← mov_gradient s a (hf u v)]
    change grad a (s.val i u • (s.val m v • (f u v ∘ mov s⁻¹))) x = _
    rw [grad_smul (show ContDiffAt ℝ ∞ (s.val m v • (f u v ∘ mov s⁻¹)) x from contDiffAt_const.smul (hs u v)), grad_smul (hs u v)]
    rfl
  change grad a (fun y => ∑ u : Axis, ∑ v : Axis, T u v y) x = _
  rw [grad_sum_fun _ (fun u _ => ContDiffAt.sum (fun v _ => ht u v))]
  unfold tri
  refine Finset.sum_congr rfl fun u _ => ?_
  change grad a (fun y => ∑ v : Axis, T u v y) x = _
  rw [grad_sum_fun _ (fun v _ => ht u v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [he,Finset.smul_sum,Finset.smul_sum]


theorem tri_cycle (s : M4) (f : Axis → Axis → Axis → F) (i j k : Axis) :
    tri s f j k i = tri s (fun i j k => f j k i) i j k := by
  let T (a b c : Axis) := s i a • s j b • s k c • f b c a
  have e (a b c) : s j b • s k c • s i a • f b c a = T a b c := by dsimp [T]; rw [smul_comm (s i a), smul_comm (s k c)]
  unfold tri; simp_rw [e]
  change (∑ b : Axis, ∑ c : Axis, ∑ a : Axis, T a b c) = ∑ a : Axis, ∑ b : Axis, ∑ c : Axis, T a b c
  have he b : ∑ c : Axis, ∑ a : Axis, T a b c = ∑ a : Axis, ∑ c : Axis, T a b c := Finset.sum_comm
  simp_rw [he]
  rw [Finset.sum_comm]

theorem tri_trace (s : Ortho) (f : Axis → Axis → Axis → F) (j : Axis) :
    ∑ i : Axis, tri s.val f i j i = ∑ b : Axis, s.val j b • ∑ a : Axis, f a b a := by
  have he (a b c) : ∑ i : Axis, s.val i a • s.val j b • s.val i c • f a b c =
      if a=c then s.val j b • f a b c else 0 := by
    have hv (i : Axis) : s.val i a • s.val j b • s.val i c • f a b c =
        (s.val i a*s.val i c) • s.val j b • f a b c := by rw [smul_comm (s.val j b),mul_smul]
    simp_rw [hv]
    rw [← Finset.sum_smul,rowId]; split <;> simp
  unfold tri
  let T (i a b c : Axis) := s.val i a • s.val j b • s.val i c • f a b c
  rw [Finset.sum_comm]
  have hv (a : Axis) : ∑ i : Axis, ∑ b : Axis, ∑ c : Axis, T i a b c = ∑ b : Axis, s.val j b • f a b a := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]; dsimp only [T]; simp [he]
  change ∑ a : Axis, ∑ i : Axis, ∑ b : Axis, ∑ c : Axis, T i a b c = _
  simp_rw [hv]
  rw [Finset.sum_comm]; simp_rw [Finset.smul_sum]

theorem bi_skew (s : M4) (Q : Rank2 F) (he : ∀ i m, Q i m = -Q m i) (i m : Axis) : bi s Q i m = -bi s Q m i := by
  simp_rw [bi_eval,← Finset.sum_neg_distrib]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by nth_rw 1 [he b a]; rw [smul_neg,smul_neg,smul_comm]

lemma carry_shell (s : Ortho) (Q : Sol F j) : carry s Q.val ∈ onShell F j := by
  have hE (i m a : Axis) (x : E4) : grad a (diagonal (carry s Q.val i m)) x = tri s.val
      (fun i m a => grad a (Q.field i m) (mov s⁻¹ x)) i m a := by rw [carry_diag]; exact reel_gradient s (fun i m => Q.smooth i m _) ..
  constructor
  · constructor
    · intro i m v σ
      rw [carry_eval,carry_eval]
      refine congr_arg (fun g : Rank2 F => bi s.val g i m) ?_
      funext a b
      exact Q.closed.coeffSym a b (fun l => mov s⁻¹ (v l)) σ
    · intro i m
      ext1 v
      rw [neg_apply,carry_eval,carry_eval]
      exact bi_skew s.val _ (fun i m => by nth_rw 1 [Q.closed.antisymmetric i m]; rfl) i m
    intro a b c x
    rw [hE,hE,hE]
    let f := fun i m a : Axis => grad a (Q.field i m) (mov s⁻¹ x)
    change tri _ f b c a + tri _ f c a b + tri _ f a b c = 0
    rw [tri_cycle s.val f a b c, tri_cycle s.val f b c a, tri_cycle s.val _ a b c]
    have he (a b c) : f b c a + f c a b + f a b c = 0 := Q.closed.closed a b c _
    simp_rw [tri,← Finset.sum_add_distrib,← smul_add,he, smul_zero, Finset.sum_const_zero]
  intro i x
  simp_rw [hE, tri_trace]
  have he (i) : ∑ a : Axis, grad a (Q.field a i) (mov s⁻¹ x) = 0 := Q.property.2 i _
  simp_rw [he,smul_zero,Finset.sum_const_zero]

def solAct (s : Ortho) : Sol F j →ₗ[ℝ] Sol F j := ((carry s).comp (onShell F j).subtype).codRestrict _ fun Q => carry_shell s Q

@[simp] theorem solAct_mul (s t : Ortho) (Q : Sol F j) : solAct (s*t) Q = solAct s (solAct t Q) := Subtype.ext (carry_mul s t Q.val)
@[simp] theorem solAct_id (Q : Sol F j) : solAct 1 Q = Q := Subtype.ext (carry_id Q.val)

def solO (s : Ortho) : Sol F j ≃ₗ[ℝ] Sol F j where
  toLinearMap := solAct s
  invFun := solAct s⁻¹
  left_inv x := by simp [← solAct_mul]
  right_inv x := by simp [← solAct_mul]

theorem field_solO (s : Ortho) (Q : Sol F j) (i m : Axis) :
    Sol.field (solO s Q) i m = reel s Q.field i m := carry_diag s Q.val i m
end YM.Extra.FD
