import YM.Next.EXTRACTION.Tails

/-! Eqs. (Jrad), (Wstress). Linear curvature variables in physical colors and elementary
radial potentials including degree-one curl tests (their radial projections, *not* presumed
independent). Used to count real signed-coordinate tensor types. At the base in radial gauge
F and ∇F have these same linear formulas: there is no constant term in the potential. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Filter Gauge Tensor Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace

variable {G : Gauge} {j : ℕ}

def sign (s : Signed) (a : Axis) : ℝ := if s.flip a then -1 else 1
@[simp] lemma sign_sq (s : Signed) (a : Axis) : sign s a^2 = 1 := by unfold sign; split <;> norm_num

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
lemma sign_sign (s : Signed) (a : Axis) (x : V) : sign s a • sign s a • x = x := by
  unfold sign; split <;> simp

lemma signed_sum (s : Signed) (a : Axis) (v : Axis → V) :
    ∑ i, s.matrix i a • v i = sign s a • v (s.perm a) := by
  simp [Signed.matrix_at,sign]

lemma signed_sum_inv (s : Signed) (a : Axis) (v : Axis → V) :
    ∑ i, s.matrix (s.perm a) i • v i = sign s a • v a := by
  simp [Signed.matrix_at,sign, ite_smul]
end

lemma signed_move (s : Signed) (z : E4) (i : Axis) : Ortho.move s.ortho z (s.perm i) = sign s i * z i := by
  rw [Signed.ortho_move]; change s.act z.ofLp (s.perm i)=_
  rw [Signed.act_at,sign]; split <;> simp

lemma signed_move_inv (s : Signed) (z : E4) (i : Axis) : Ortho.move s.ortho⁻¹ z i = sign s i * z (s.perm i) := by
  nth_rw 2 [← Ortho.move_inv s.ortho z]; rw [signed_move]
  unfold sign; split <;> simp

lemma signed_basis (s : Signed) (i : Axis) : Ortho.move s.ortho (basis i) = sign s i • basis (s.perm i) := by
  ext1 j
  obtain ⟨j,rfl⟩ := s.perm.surjective j
  rw [signed_move]; simp only [basis_eq,PiLp.smul_apply,s.perm.injective.eq_iff,smul_eq_mul]
  split_ifs with h; subst i; rfl; simp

lemma signed_turn_value (s : Signed) (A : Taylor G j) (a : Axis) (z : E4) :
    (Taylor.turn s.ortho A).value (s.perm a) z = sign s a • A.value a (Ortho.move s.ortho⁻¹ z) := by
  rw [Taylor.turn_value]; apply signed_sum_inv

/-- Tensor coefficient evaluated on a repeated vector. In degree zero the choice of vector
is immaterial. For j=1 this is the *unscaled* first derivative contracted with that vector. -/
def curled (j : ℕ) (x : E4) (a b : Axis) : Taylor G j →ₗ[ℝ] G.Color :=
  (ContinuousMultilinearMap.apply ℝ _ G.Color (fun _ : Fin j => x)).toLinearMap ∘ₗ
    LinearMap.proj b ∘ₗ LinearMap.proj a ∘ₗ (Maxwell.formSpace j G.Color).subtype ∘ₗ Maxwell.potential.toLinearMap
abbrev curl0 := @curled G 0 0
abbrev curl1 (k : Axis) := @curled G 1 (basis k)

lemma curled_deriv (A : Taylor G j) (z : E4) (a b : Axis) : curled j z a b A =
    Maxwell.grad a (A.value b) z - Maxwell.grad b (A.value a) z := congr_fun (Maxwell.takeCurl_diag A a b) z
lemma curled_swap (A : Taylor G j) (z : E4) (a b : Axis) : curled j z a b A = -curled j z b a A := by simp [curled_deriv]
lemma curl0_value (A : Taylor G 0) (a b : Axis) : curl0 a b A = A.value b (basis a) - A.value a (basis b) := by
  rw [curled_deriv]
  have he (a b : Axis) : Maxwell.grad a (A.value b) 0 = A.value b (basis a) := by
    unfold Maxwell.grad D Taylor.value
    rw [differential_diagonal _ (A.property.1 _), ContinuousMultilinearMap.curryLeft_apply]
    simp only [show (0+1:ℕ)=1 from rfl, one_smul]; unfold diagonal; congr! 1; ext1 i; fin_cases i; simp
  rw [he,he]


lemma curled_paint (A : Taylor G j) (z : E4) (a b : Axis) (g : G.El) :
    curled j z a b (Taylor.paint g A) = G.adjoint g (curled j z a b A) := by
  rw [curled_deriv,curled_deriv, map_sub]
  have he (i k) := Maxwell.grad_linear ((G.adjoint g).toContinuousLinearMap) ((Tensor.diag_smooth (A.val k) ∞).contDiffAt (x:=z)) i
  exact congr_arg₂ (·-·) (he a b) (he b a)

lemma curled_turn (A : Taylor G j) (z : E4) (a b : Axis) (s : Signed) :
    curled j (Ortho.move s.ortho z) (s.perm a) (s.perm b) (Taylor.turn s.ortho A) =
      (sign s a * sign s b) • curled j z a b A := by
  let L := (Ortho.motion s.ortho⁻¹).toContinuousLinearMap
  have he (a b) : Maxwell.grad (s.perm a) ((Taylor.turn s.ortho A).value (s.perm b)) (Ortho.move s.ortho z) =
      (sign s a * sign s b) • Maxwell.grad a (A.value b) z := by
    unfold Maxwell.grad D
    rw [show (Taylor.turn s.ortho A).value (s.perm b) = sign s b • (A.value b ∘ L) from
      funext fun t => signed_turn_value s A b t, fderiv_const_smul, fderiv_comp]
    · have ht : L (basis (s.perm a)) = sign s a • basis a := by
        rw [← sign_sign s a (basis (s.perm a)), ← signed_basis, L.map_smul]
        simp [L]
      simp only [L.fderiv, smul_apply, ContinuousLinearMap.comp_apply, ht,map_smul,smul_smul,
        show L (Ortho.move s.ortho z)=z from Ortho.inv_move s.ortho z, mul_comm (sign s a)]
    · exact (Tensor.diag_smooth _ 1).differentiable (by decide) _
    · exact L.differentiableAt
    exact ((Tensor.diag_smooth _ 1).differentiable (by decide)).differentiableAt.comp _ L.differentiableAt
  rw [curled_deriv,curled_deriv,he,he b a,mul_comm (sign s b),smul_sub]

lemma curl0_turn (A : Taylor G 0) (s : Signed) (a b) :
    curl0 (s.perm a) (s.perm b) (Taylor.turn s.ortho A) = (sign s a * sign s b) • curl0 a b A := by
  simpa only [show Ortho.move s.ortho 0 = 0 from map_zero (Ortho.motion s.ortho)] using curled_turn A 0 a b s

lemma curl1_turn (A : Taylor G 1) (s : Signed) (k a b) :
    curl1 (s.perm k) (s.perm a) (s.perm b) (Taylor.turn s.ortho A) =
      (sign s k * (sign s a * sign s b)) • curl1 k a b A := by
  have he := curled_turn A (basis k) a b s
  rw [signed_basis] at he; rw [mul_smul,← he]
  change diagonal (Maxwell.takeCurl _ _ _) _ = sign s k • diagonal (Maxwell.takeCurl (j:=1) _ _ _) _
  rw [Tensor.homogeneous, pow_one,sign_sign]

/-- Elementary coordinates. We don't assume they satisfy Maxwell. Integrate an arbitrary
(possibly not closed) antisymmetric two-form in a radial direction. Summing will reproduce
an actual radial jet when using its curl. -/
def leg (a b : Axis) (q : T E4 G.Color j) : Taylor G j :=
  ⟨fun i => ((j:ℝ)+2)⁻¹ • ((if i=b then added q (Maxwell.compAxis a) else 0) -
                             (if i=a then added q (Maxwell.compAxis b) else 0)), by
    refine ⟨fun i x s => ?_,fun z => ?_⟩
    · dsimp only; split_ifs <;> simp [added_sym _ _ x s]
    have he (i) : diagonal ((((j:ℝ)+2)⁻¹ • ((if i=b then added q (Maxwell.compAxis a) else 0) -
        (if i=a then added q (Maxwell.compAxis b) else 0))) : T E4 G.Color (j+1)) z =
        ((j:ℝ)+2)⁻¹ • ((if i=b then z a • diagonal q z else 0) - (if i=a then z b • diagonal q z else 0)) := by
      split_ifs <;> simp [diagonal,show ∀ a, added q (Maxwell.compAxis a) (fun _ => z) = z a • diagonal q z from fun _ => added_diag ..]
    simp_rw [he,smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero,Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
    ring_nf; simp ⟩

lemma leg_value (a b : Axis) (q : T E4 G.Color j) (i : Axis) (z : E4) :
    (leg a b q).value i z = ((j:ℝ)+2)⁻¹ • ((if i=b then z a • diagonal q z else 0) - (if i=a then z b • diagonal q z else 0)) := by
  have he (a) : added q (Maxwell.compAxis a) (fun _ => z) = z a • diagonal q z := added_diag ..
  unfold leg Taylor.value diagonal; dsimp only; split_ifs <;> simp [he, diagonal]

def leg0 (a b : Axis) : G.Color →ₗ[ℝ] Taylor G 0 where
  toFun c := leg a b (ContinuousMultilinearMap.constOfIsEmpty ℝ _ c)
  map_add' c d := by
    apply Taylor.value_ext; funext i z
    change (leg ..).value i z = (leg ..).value i z + (leg ..).value i z
    simp_rw [leg_value]; split_ifs <;> simp [smul_sub,diagonal, smul_add] <;> abel
  map_smul' t c := by
    apply Taylor.value_ext; funext i z
    change (leg ..).value i z = t • (leg ..).value i z
    simp_rw [leg_value]; split_ifs <;> simp [diagonal, smul_sub,smul_comm t]

def leg1 (k a b : Axis) : G.Color →ₗ[ℝ] Taylor G 1 where
  toFun c := leg a b (added (ContinuousMultilinearMap.constOfIsEmpty ℝ _ c) (Maxwell.compAxis k))
  map_add' c d := by
    apply Taylor.value_ext; funext i z
    change (leg ..).value i z = (leg ..).value i z + (leg ..).value i z
    simp_rw [leg_value,added_diag]; split_ifs <;> simp [smul_sub,diagonal, smul_add] <;> abel
  map_smul' t c := by
    apply Taylor.value_ext; funext i z
    change (leg ..).value i z = t • (leg ..).value i z
    simp_rw [leg_value,added_diag]; split_ifs <;> simp [diagonal, smul_sub,smul_comm t]

theorem leg0_value (c : G.Color) (a b i : Axis) (z : E4) :
    (leg0 a b c).value i z = (2:ℝ)⁻¹ • ((if i=b then z a • c else 0) - (if i=a then z b • c else 0)) := by
  simp only [leg0, LinearMap.coe_mk,AddHom.coe_mk, leg_value]; simp [diagonal]
theorem leg1_value (c : G.Color) (k a b i : Axis) (z : E4) :
    (leg1 k a b c).value i z = (3:ℝ)⁻¹ • ((if i=b then z a • z k • c else 0) - (if i=a then z b • z k • c else 0)) := by
  norm_num only [leg1,LinearMap.coe_mk,AddHom.coe_mk, leg_value,added_diag,Nat.cast_one]; rfl

theorem leg0_swap (a b : Axis) (x : G.Color) : leg0 a b x = -leg0 b a x := by
  apply Taylor.value_ext; funext i z; change _ = -(leg0 b a x).value i z; simp [leg0_value, ← smul_neg]
theorem leg1_swap (k a b : Axis) (x : G.Color) : leg1 k a b x = -leg1 k b a x := by
  apply Taylor.value_ext; funext i z; change _ = -(leg1 k b a x).value i z; simp [leg1_value, ← smul_neg]
@[simp] theorem leg0_diag (a : Axis) (x : G.Color) : leg0 a a x = 0 := by apply Taylor.value_ext; funext i z; rw [leg0_value,sub_self,smul_zero]; rfl
@[simp] theorem leg1_diag (k a : Axis) (x : G.Color) : leg1 k a a x = 0 := by apply Taylor.value_ext; funext i z; rw [leg1_value,sub_self,smul_zero]; rfl

theorem leg1_cycle (k a b : Axis) (x : G.Color) : leg1 k a b x + leg1 a b k x + leg1 b k a x = 0 := by
  apply Taylor.value_ext; funext i z
  change (leg1 k a b x).value i z + (leg1 a b k x).value i z + (leg1 b k a x).value i z = 0
  rw [leg1_value,leg1_value,leg1_value, smul_comm (z b) (z k), smul_comm (z a) (z k),smul_comm (z b) (z a)]
  simp only [smul_sub]; abel

theorem turn_leg0 (s : Signed) (a b : Axis) (x : G.Color) :
    Taylor.turn s.ortho (leg0 a b x) = (sign s a * sign s b) • leg0 (s.perm a) (s.perm b) x := by
  apply Taylor.value_ext; funext i z
  obtain ⟨i,rfl⟩ := s.perm.surjective i
  rw [signed_turn_value]; change _ = (_:ℝ) • (leg0 _ _ x).value (s.perm i) z
  rw [leg0_value,leg0_value,signed_move_inv,signed_move_inv]
  simp only [s.perm.injective.eq_iff,mul_smul,smul_sub]
  congr 1
  · split_ifs with h
    · subst i; simp_rw [smul_comm _ (2:ℝ)⁻¹, smul_comm (sign s a) (sign s b)]
    simp
  split_ifs with h
  · subst i; simp_rw [smul_comm _ (2:ℝ)⁻¹]
  simp

theorem turn_leg1 (s : Signed) (k a b : Axis) (x : G.Color) : Taylor.turn s.ortho (leg1 k a b x) =
    (sign s k * (sign s a * sign s b)) • leg1 (s.perm k) (s.perm a) (s.perm b) x := by
  apply Taylor.value_ext; funext i z
  obtain ⟨i,rfl⟩ := s.perm.surjective i
  rw [signed_turn_value]; change _ = (_:ℝ) • (leg1 _ _ _ x).value (s.perm i) z
  rw [leg1_value,leg1_value,signed_move_inv,signed_move_inv,signed_move_inv]
  simp only [s.perm.injective.eq_iff,smul_sub]; congr 1
  · split_ifs with h
    · subst i; simp_rw [smul_smul]; congr 1; ring
    simp
  split_ifs with h
  · subst i; simp_rw [smul_smul]; congr 1; ring
  simp

theorem paint_leg0 (g : G.El) (a b : Axis) (x : G.Color) : Taylor.paint g (leg0 a b x) = leg0 a b (G.adjoint g x) := by
  apply Taylor.value_ext; funext i z; rw [Taylor.paint_value, leg0_value, leg0_value]; split_ifs <;> simp
theorem paint_leg1 (g : G.El) (k a b : Axis) (x : G.Color) : Taylor.paint g (leg1 k a b x) = leg1 k a b (G.adjoint g x) := by
  apply Taylor.value_ext; funext i z; rw [Taylor.paint_value, leg1_value, leg1_value]; split_ifs <;> simp

private theorem radial_value (A : Taylor G j) (i : Axis) (z : E4) :
    A.value i z = ((j:ℝ)+2)⁻¹ • ∑ a, z a • curled j z a i A := by
  conv_lhs => rw [← Maxwell.potential_recover A]
  rw [Maxwell.contracted_diag]; norm_cast

private def valAt (j : ℕ) (i : Axis) (x : E4) : Taylor G j →ₗ[ℝ] G.Color where
  toFun A := A.value i x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sum_legs0 (A : Taylor G 0) : (∑ a, ∑ b, leg0 a b (curl0 a b A)) = (2:ℝ) • A := by
  apply Taylor.value_ext; funext i z
  change valAt (G:=G) 0 i z (∑ a, ∑ b, leg0 a b (curl0 a b A)) = (2:ℝ) • A.value i z
  have he (a b : Axis) : curled 0 z a b A = curl0 a b A := congr_arg (Maxwell.takeCurl A a b) (Subsingleton.elim ..)
  rw [two_smul,radial_value]; simp_rw [map_sum,he]
  change ∑ a, ∑ b, (leg0 a b _).value i z = _
  simp_rw [leg0_value, smul_sub, Finset.sum_sub_distrib]; simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,Nat.cast_zero,zero_add]
  rw [Finset.sum_comm (f := fun a b : Axis => ite (i=a) ((2:ℝ)⁻¹ • z b • curl0 a b A) 0)]; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [show ∀ b, curl0 i b A = -curl0 b i A from fun _ => curled_swap A _ _ _, smul_neg,Finset.sum_neg_distrib,sub_neg_eq_add,Finset.smul_sum]

theorem sum_curled (A : Taylor G 1) (a b : Axis) (z : E4) :
    ∑ k, z k • curl1 k a b A = curled 1 z a b A := by
  let L := ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)
  obtain ⟨f,hf⟩ := L.surjective (Maxwell.takeCurl A a b)
  have he (x : E4) : curled 1 x a b A = f x := congr_arg (diagonal · x) hf.symm
  simp only [curl1,he,← map_smul, ← map_sum]; congr! 1; ext1 i; simp

theorem sum_legs1 (A : Taylor G 1) : (∑ a, ∑ b, ∑ k, leg1 k a b (curl1 k a b A)) = (2:ℝ) • A := by
  apply Taylor.value_ext; funext i z
  change valAt (G:=G) 1 i z (∑ a, ∑ b, ∑ k, leg1 k a b (curl1 k a b A)) = (2:ℝ) • A.value i z
  rw [two_smul,radial_value]; simp_rw [map_sum]
  change ∑ a, ∑ b, ∑ k, (leg1 k a b _).value i z = _
  have he (a b : Axis) : (∑ k, (leg1 k a b (curl1 k a b A)).value i z) = (3:ℝ)⁻¹ •
      ((if i=b then z a • curled 1 z a b A else 0) - (if i=a then z b • curled 1 z a b A else 0)) := by
    simp_rw [leg1_value]; split_ifs <;> simp [← Finset.smul_sum, Finset.sum_sub_distrib, sum_curled]
  simp_rw [he, smul_sub, Finset.sum_sub_distrib]; norm_num
  -- simp positions
  simp_rw [show ∀ b, curled 1 z i b A = -curled 1 z b i A from fun _ => curled_swap A _ _ _, smul_neg,Finset.sum_neg_distrib,sub_neg_eq_add,Finset.smul_sum]
end YM.StressFlux
