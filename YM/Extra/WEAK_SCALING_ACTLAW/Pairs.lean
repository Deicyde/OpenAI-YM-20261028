import YM.Extra.WEAK_SCALING_ACTLAW.Decompose

/-!
# Color-paired F*F labels on the actual free comparator at cap four

Gauge invariance before the quotient. Orders, curl convention and real
color normalization on the actual radial gauge labels. Pair-sector
generation and signed action **after** both equation and all-spectator
quotients; no assumption of free independent coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Set Filter Function Labels Tensor
open scoped Matrix.Norms.Frobenius Topology InnerProductSpace ContDiff
variable {G : Gauge} {L : Register G} {d : ℕ}

private def linear (A : Taylor G 0) (a : Axis) := continuousMultilinearCurryFin1 ℝ E4 G.Color (A.val a)
private lemma lin_value (A : Taylor G 0) (a : Axis) (z : E4) : A.value a z = linear A a z := by
  change A.val a _ = _
  rw [linear,continuousMultilinearCurryFin1_apply]; congr 1

def strength (A : Taylor G 0) (a b : Axis) := (2:ℝ) • A.value b (basis a)
lemma skew (A : Taylor G 0) (a b : Axis) : strength A a b = -strength A b a := by
  have hs (a : Axis) := A.radial_value (basis a)
  have h := A.radial_value (basis a + basis b)
  simp only [lin_value, PiLp.add_apply, map_add,add_smul,smul_add,basis_eq,ite_smul,one_smul,zero_smul,
    Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at h hs
  simp only [hs,zero_add,add_zero] at h
  simp only [strength,lin_value]; rw [eq_neg_of_add_eq_zero_right h,smul_neg,neg_neg]

lemma painted (u : G.El) (A : Taylor G 0) (a b) : strength (Taylor.paint u A) a b = G.adjoint u (strength A a b) := by
  simp [strength]

private lemma swap_value (u : Signed) (a b : Axis) : u.ortho⁻¹.val a b = u.matrix b a := rfl
lemma turned (u : Signed) (A : Taylor G 0) (a b) : strength (Taylor.turn u.ortho⁻¹ A) a b =
    (Work.A01.eps u a * Work.A01.eps u b) • strength A (u.perm a) (u.perm b) := by
  rw [strength, Taylor.turn_value, inv_inv, Work.A01.move_basis]
  rw [Finset.sum_eq_single_of_mem (u.perm b) (Finset.mem_univ _)]
  · simp_rw [lin_value,map_smul,swap_value,strength,lin_value, Work.A01.eps]; module
  intro i _ hi
  simp [swap_value, Signed.matrix_at,Ne.symm hi]

private def axisPart (a : Axis) (x : G.Color) : E4 [×1]→L[ℝ] G.Color :=
    (continuousMultilinearCurryFin1 ℝ E4 G.Color).symm ((EuclideanSpace.proj (𝕜:=ℝ) a).smulRight x)
private lemma axis_apply (a : Axis) (x : G.Color) (z : E4) : diagonal (axisPart a x) z = z a • x := by
  rw [axisPart, Tensor.diagonal, continuousMultilinearCurryFin1_symm_apply]; rfl

def atom (a b : Axis) : G.Color →ₗ[ℝ] Taylor G 0 := by
  let F (x : G.Color) (i : Axis) := (2:ℝ)⁻¹ • ((if i=b then axisPart a x else 0) - (if i=a then axisPart b x else 0))
  have he (i z x) : diagonal (F x i) z = (2:ℝ)⁻¹ • ((if i=b then z a • x else 0) - (if i=a then z b • x else 0)) := by
    dsimp only [F,Tensor.diagonal,smul_apply,sub_apply]; split_ifs <;> simp [axisPart]
  have ht (x : G.Color) : F x ∈ radial G 0 := by
    refine ⟨fun i t s => congrArg (F x i) ?_,fun z => ?_⟩
    · exact funext fun i => congrArg t (@Subsingleton.elim (Fin 1) _ _ _ : s i=i)
    simp_rw [he,smul_comm (z _) (2:ℝ)⁻¹,← Finset.smul_sum]; rw [smul_eq_zero]; right
    simp only [smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,if_true]; module
  refine ⟨⟨(fun x => ⟨F x, ht x⟩),fun x y => ?_⟩,fun c x => ?_⟩ <;> (
    apply Taylor.value_ext; funext i z; simp only [Taylor.value,Submodule.coe_add, SetLike.val_smul,Pi.add_apply,
      Pi.smul_apply, RingHom.id_apply];
    first | change diagonal (F _ i) z = diagonal (F _ i) z + diagonal (F _ i) z | change diagonal (F _ i) z = (c:ℝ) • diagonal (F _ i) z
    simp_rw [he]; split_ifs <;> module)

lemma atom_value (a b : Axis) (x : G.Color) (i z) : Taylor.value (atom a b x) i z =
    (2:ℝ)⁻¹ • ((if i=b then z a • x else 0) - (if i=a then z b • x else 0)) := by
  dsimp only [atom,Taylor.value,LinearMap.coe_mk,AddHom.coe_mk,Tensor.diagonal,smul_apply,sub_apply]
  split_ifs <;> simp [axisPart]

lemma paint_atom (u : G.El) (a b : Axis) (x : G.Color) : atom a b (G.adjoint u x) = Taylor.paint u (atom a b x) := by
  apply Taylor.value_ext; funext i z; rw [atom_value, Taylor.paint_value,atom_value]; split_ifs <;> simp

abbrev atom' (p : Fin 6) (x : G.Color) := atom (Cube.left p) (Cube.right p) x
abbrev probe' (p : Fin 6) (A : Taylor G 0) := strength A (Cube.left p) (Cube.right p)

set_option maxHeartbeats 1000000 in
theorem atoms (A : Taylor G 0) : A = ∑ i, atom' i (probe' i A) := by
  let X := ∑ i, atom' i (probe' i A)
  have h0 (p : Axis) : strength A p p = 0 := by
    apply smul_right_injective G.Color (two_ne_zero (α:=ℝ)); change (2:ℝ) • _=(2:ℝ) • _
    rw [two_smul]; nth_rw 1 [skew A p p]; simp
  have he (p q : Axis) : strength X p q = strength A p q := by
    rw [strength]; dsimp only [X]; unfold Taylor.value; simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,Tensor.diagonal,
      sum_apply]
    change (2:ℝ) • (∑ i : Fin 6, Taylor.value (atom' i (probe' i A)) q (basis p)) = _
    simp only [atom', probe', atom_value, Finset.smul_sum, smul_inv_smul₀ (two_ne_zero (α:=ℝ))]
    have hi : ∀ c : Axis, c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by decide
    have hl : ∀ i : Fin 6, Cube.left i = if i=0 ∨ i=1 ∨ i=2 then 0 else if i=3 ∨ i=4 then 1 else 2 := by decide
    have hr : ∀ i : Fin 6, Cube.right i = if i=0 then 1 else if i=1 ∨ i=3 then 2 else 3 := by decide
    rcases hi p with h|h|h|h <;> rcases hi q with h'|h'|h'|h' <;>
      simp only [Fin.sum_univ_six,h,h',hl,hr,basis_eq] <;> norm_num [Fin.ext_iff,h0] <;> rw [skew, neg_neg]
  apply Taylor.value_ext; funext b z
  have hz : (∑ a, z a • basis a) = z := by ext i; simp
  have hl (A : Taylor G 0) : (2:ℝ) • Taylor.value A b z = ∑ a, z a • strength A a b := by
    rw [lin_value]; conv_lhs => rw [← hz,map_sum,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [strength,lin_value,map_smul,smul_comm]
  apply smul_right_injective _ (two_ne_zero (α:=ℝ)); simp only [hl]; exact Finset.sum_congr rfl fun i _ => congrArg _ (he i b).symm

def fieldL (a b : Axis) (c : G.ColorIndex) : Taylor G 0 →ₗ[ℝ] ℝ := {
  toFun A := strength A a b c
  map_add' _ _ := by simp [strength,Taylor.value,Tensor.diagonal, smul_add]
  map_smul' r A := by simp [strength,Taylor.value,Tensor.diagonal,smul_comm (2:ℝ)] }

def pol (a b : Axis) (c : G.ColorIndex) : Pol G := ∑ k : Fin (dim G 0),
  MvPolynomial.C (↑(fieldL a b c ((axes G 0) k)):ℂ) * MvPolynomial.X (⟨0,k⟩ : Key G)

def pairPol (G : Gauge) (a b i j : Axis) := ∑ c : G.ColorIndex, pol a b c * pol i j c

lemma pol_bound (a b : Axis) (c : G.ColorIndex) : MvPolynomial.IsWeightedHomogeneous generation (pol a b c) 2 :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun i _ => (MvPolynomial.isWeightedHomogeneous_X ℂ generation (⟨0,i⟩ : Key G)).C_mul _)
lemma pair_bound (a b i j) : pairPol G a b i j ∈ limited G 4 := by
  refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr fun d hd => (show height d ≤ 4 from le_of_eq ?_)
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun c _ => (pol_bound a b c).mul (pol_bound i j c)) (MvPolynomial.mem_support_iff.mp hd)
lemma pol_eval (A : Jet G) (a b : Axis) (c) : Labels.read A (pol a b c) = (strength (A 0) a b c : ℂ) := by
  have he := congrArg (fieldL a b c) ((axes G 0).sum_repr (A 0))
  change _= (↑(fieldL a b c (A 0)):ℂ)
  rw [← he]; simp only [pol,Labels.read,map_sum,map_smul,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X, Labels.coord,Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
lemma pair_eval (A : Jet G) (a b i j : Axis) : Labels.read A (pairPol G a b i j) = (inner ℝ (strength (A 0) a b) (strength (A 0) i j):ℂ) := by
  rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct,pairPol,pol_eval]

def pairLabel (G : Gauge) (a b i j : Axis) : Label G 4 := ⟨pairPol G a b i j, pair_bound .., fun x u => by
  simp only [pair_eval,colored,painted,real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← map_sub,G.norm_adjoint]⟩

lemma rotated (g : Signed) (a b i j : Axis) :
    tensor g.ortho (pairLabel G a b i j) =
      (↑(Work.A01.eps g a * Work.A01.eps g b * Work.A01.eps g i * Work.A01.eps g j) : ℂ) • pairLabel G (g.perm a) (g.perm b) (g.perm i) (g.perm j) := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (changed _ (pairPol ..)) = Labels.read A ((_ :ℂ) • pairPol ..)
  rw [eval_changed,map_smul,pair_eval,pair_eval]; unfold changedJet
  rw [turned,turned,real_inner_smul_left,real_inner_smul_right]; push_cast; rw [smul_eq_mul]; ring

lemma inputs (h : G.Simple) (p : Label G 4) : ∃ (z : ℂ) (b : Fin 6 → Fin 6 → ℂ),
    p=z • Labels.unit G 4 + ∑ i, ∑ j, b i j • pairLabel G (Cube.left i) (Cube.right i) (Cube.left j) (Cube.right j) := by
  obtain ⟨z,Q,he,hQ⟩ := quadratic h p
  let B (i j : Fin 6) := ((Q.comp (atom (Cube.left i) (Cube.right i))).compl₂ (atom (Cube.left j) (Cube.right j)))
  have hB (i j : Fin 6) (g : G.El) (x y : G.Color) : B i j (G.adjoint g x) (G.adjoint g y) = B i j x y := by
    dsimp [B]; rw [paint_atom,paint_atom,hQ]
  choose c hc using fun i j => bilinear_invariant h (B i j) (hB i j)
  refine ⟨z,c,Subtype.ext (Labels.eval_ext _ _ fun A => ?_)⟩
  rw [Submodule.coe_add, AddSubmonoidClass.coe_finsetSum, map_add,he]
  congr 1
  · exact (by simp [Labels.unit])
  calc
    Q (A 0) (A 0) = ∑ i, ∑ j, Q (atom' i (probe' i (A 0))) (atom' j (probe' j (A 0))) := by
      conv_lhs => rw [atoms (A 0), map_sum Q, LinearMap.sum_apply]; simp only [map_sum]
    _ = ∑ i : Fin 6, ∑ j : Fin 6, (inner ℝ (probe' i (A 0)) (probe' j (A 0))) • c i j := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hc i j _ _
    _ = _ := by simp [pairLabel,pair_eval,probe',Complex.real_smul,mul_comm]
end YM.Extra.WeakScaling.Color
