import YM.Next.UV_STRESS.Across
import YM.UVNext.FREE_STRESS_CERTIFICATE.Planes
import YM.UVNext.FREE_STRESS_CERTIFICATE.Samples

/-! Actual signed and real action on the curl contractions. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set
variable {G : Gauge} (F : Frames G) {j l d n : ℕ}

set_option maxHeartbeats 180000 in
private lemma axis_leg (A : Labels.Taylor G j) (i a : Axis) (m : Fin j → Axis) (s : Signed) :
    (Labels.Taylor.turn s.ortho⁻¹ A).val i (Fin.cons (YM.basis a) (YM.basis ∘ m)) =
      ((eps s i * eps s a) * ∏ x : Fin j, eps s (m x)) •
        A.val (s.perm i) (Fin.cons (YM.basis (s.perm a)) (YM.basis ∘ s.perm ∘ m)) := by
  change (∑ k : Axis, _ • (((A.val k).compContinuousLinearMap _) : Tensor.T E4 G.Color (j+1)))
    (Fin.cons (YM.basis a) (YM.basis ∘ m)) = _
  -- collapse output matrix column of s
  simp only [sum_apply,smul_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have ht (k) : s.ortho⁻¹.val i k = s.matrix k i := rfl
  simp_rw [ht, inv_inv]
  rw [Finset.sum_eq_single (s.perm i)]
  ·
    let Q : Fin (j+1) → Axis := Fin.cons a m
    have hQ : Fin.cons (YM.basis a) (YM.basis ∘ m) = fun x => YM.basis (Q x) := by
      funext x; refine Fin.cases ?_ (fun k => ?_) x <;> simp [Q]
    have hQ' : Fin.cons (YM.basis (s.perm a)) (YM.basis ∘ s.perm ∘ m) = fun x => YM.basis (s.perm (Q x)) := by
      funext x; refine Fin.cases ?_ (fun k => ?_) x <;> simp [Q]
    rw [hQ,hQ']
    have hE (a : Axis) : LinearMap.toContinuousLinearMap (Ortho.motion s.ortho).toLinearEquiv.toLinearMap (YM.basis a) = eps s a • YM.basis (s.perm a) := move_basis s a
    simp_rw [hE,ContinuousMultilinearMap.map_smul_univ _ (fun x => eps s (Q x)), Fin.prod_univ_succ (fun x => eps s (Q x)),smul_smul]
    simp [Q, mul_assoc,eps]
  · intro b _ hb; simp [Signed.matrix_at,Ne.symm hb]
  · simp

def carry (s : Signed) (p : Place j) : Place j := ((s.perm p.1.1,s.perm p.1.2),s.perm ∘ p.2)
def signs (s : Signed) (p : Place j) := eps s p.1.1 * eps s p.1.2 * ∏ x, eps s (p.2 x)

theorem signed_component (s : Signed) (p : Place j) (A : Labels.Taylor G j) :
    component p (Labels.Taylor.turn s.ortho⁻¹ A) = signs s p • component (carry s p) A := by
  obtain ⟨⟨i,k⟩,m⟩ := p
  change (((j+1:ℕ):ℝ)) • ((Labels.Taylor.turn s.ortho⁻¹ A).val k (Fin.cons (YM.basis i) (YM.basis ∘ m)) -
    (Labels.Taylor.turn s.ortho⁻¹ A).val i (Fin.cons (YM.basis k) (YM.basis ∘ m))) = _
  rw [axis_leg, axis_leg, mul_comm (eps s k) (eps s i), ← smul_sub, smul_comm]
  rfl

theorem signed_bond (s : Signed) (p : Place j) (q : Place l) (h : j+l+4 ≤ d) :
    Labels.tensor (G:=G) s.ortho (bond p q h) =
      (↑(signs s p * signs s q) : ℂ) • bond (carry s p) (carry s q) h := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (rotated s.ortho (tape p q)) = Labels.read A (_ • tape _ _)
  rw [rotated, Labels.eval_changed, map_smul,eval_tape,eval_tape]
  unfold Labels.changedJet; rw [signed_component,signed_component,real_inner_smul_left,real_inner_smul_right]
  rw [← mul_assoc, Complex.ofReal_mul]; rfl

abbrev FourFields (F : Frames G) := (freeTable F).Field 4
abbrev FiveFields (F : Frames G) := (freeTable F).Field 5

def link (d : ℕ) (h : 4 ≤ d) (a b c e : Axis) : (freeTable F).Field d := embed F d (ff G d h a b c e)
abbrev flat (a b c e : Axis) : FourFields F := link F 4 le_rfl (a:Axis) (b:Axis) (c:Axis) (e:Axis)

def first (a b c e k : Axis) : FiveFields F := embed F 5 (fq G 5 le_rfl a b c e k)

@[simp] theorem link_real (H : (freeTable F).RealSpin) (h : 4 ≤ d) (a b c e : Axis) :
    (freeTable F).conj H d (link F d h a b c e) = link F d h a b c e := by simp only [link, ff,conjugate_embed,bond_real]
@[simp] theorem first_real (H : (freeTable F).RealSpin) (a b c e k : Axis) :
    (freeTable F).conj H 5 (first F a b c e k) = first F a b c e k := by simp only [first,fq,conjugate_embed,bond_real]

lemma signed_link (H : (freeTable F).RealSpin) (s : Signed) (a b c e : Axis) (h : 4 ≤ d) :
    (freeTable F).mirror H d s (link F d h a b c e) = (↑(eps s a*eps s b*(eps s c*eps s e)):ℂ) •
      link F d h (s.perm a) (s.perm b) (s.perm c) (s.perm e) := by
  simp only [link,ff,mirror_embed,signed_bond,map_smul,signs,Fintype.prod_empty,mul_one,initialPlace]
  simp_rw [bond_initial]; rfl

lemma signed_first (H : (freeTable F).RealSpin) (s : Signed) (a b c e k : Axis) :
    (freeTable F).mirror H 5 s (first F a b c e k) = (↑(eps s a*eps s b*(eps s c*eps s e)*eps s k):ℂ) •
      first F (s.perm a) (s.perm b) (s.perm c) (s.perm e) (s.perm k) := by
  simp only [first,fq,mirror_embed,signed_bond,map_smul,signs,Fintype.prod_empty,mul_one,initialPlace, gradientPlace,Finset.prod_const, Finset.card_univ,Fintype.card_fin,pow_one,mul_assoc]
  simp_rw [bond_gradient]; rfl

-- shorthand on actual classes
lemma left_link (h : 4 ≤ d) (a b c e : Axis) : link F d h b a c e = - link F d h a b c e := by
  unfold link; rw [ff_left h a b c e,map_neg]
lemma right_link (h : 4 ≤ d) (a b c e : Axis) : link F d h a b e c = - link F d h a b c e := by
  unfold link; rw [ff_right h a b c e,map_neg]
lemma swap_link (h : 4 ≤ d) (a b c e : Axis) : link F d h a b c e = link F d h c e a b := by unfold link; rw [ff_swap h a b c e]
@[simp] lemma link_zeroL (h : 4 ≤ d) (a c e : Axis) : link F d h a a c e=0 := by simp [link]
@[simp] lemma link_zeroR (h : 4 ≤ d) (a b c : Axis) : link F d h a b c c=0 := by simp [link]
lemma left_first (a b c e k : Axis) : first F b a c e k = - first F a b c e k := by
  unfold first; rw [fq_left _ a b c e k,map_neg]
lemma right_first (a b c e k : Axis) : first F a b e c k = - first F a b c e k := by
  unfold first; rw [fq_right _ a b c e k,map_neg]
@[simp] lemma first_zeroL (a c e k : Axis) : first F a a c e k=0 := by simp [first]
@[simp] lemma first_zeroR (a b c k : Axis) : first F a b c c k=0 := by simp [first]

end YM.UVNext.FreeStress
