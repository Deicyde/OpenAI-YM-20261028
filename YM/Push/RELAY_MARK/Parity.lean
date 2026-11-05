import YM.Push.RELAY_MARK.Gauge

/-!
# Equation parity, signed group and real form

Keep action on curvature-jet equations *before*
selecting invariant lifts. Not real-spin reconstruction!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {j d : ℕ} {p q : Label G d} {f : Pre G} {m : ℕ × ℕ}

section Orient
open Maxwell

-- Here use the signed action, actual frame chosen for H output.
private def arrow (s : Signed) (i : Axis) : ℝ := if s.flip i then -1 else 1
private lemma axis_move (s : Signed) (i : Axis) : (Ortho.motion s.ortho) (basis i)=arrow s i • basis (s.perm i) := by
  apply PiLp.ext; intro j
  by_cases h : s.perm i=j
  · subst j; rw [Ortho.motion_at,Signed.ortho_move]; unfold arrow; split <;> simp_all
  obtain ⟨k,rfl⟩ := s.perm.surjective j
  rw [Ortho.motion_at,Signed.ortho_move]
  have he : k ≠ i := s.perm.injective.ne_iff.mp (Ne.symm h)
  cases hs : s.flip k <;> simp [hs,he]

private lemma turned_h (s : Signed) (A : Taylor G j) (i : Axis) :
    (Taylor.turn s.ortho⁻¹ A).value i = arrow s i • (A.value (s.perm i) ∘ (Ortho.motion s.ortho)) := by
  funext x
  rw [Taylor.turn_value,Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]
  · rw [show (s.ortho⁻¹).val i (s.perm i)=arrow s i from ?_,inv_inv]; rfl
    change star (s.matrix _ i)=_
    simp only [Signed.matrix_at,↓reduceIte,star_trivial]; rfl
  intro k _ hk
  rw [show (s.ortho⁻¹).val i k=(0:ℝ) from ?_,zero_smul]
  change star (s.matrix k i)=_
  simp only [Signed.matrix_at, Ne.symm hk,if_false,star_trivial]

private lemma rotate_grad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Signed) (i : Axis) (x : E4) (t : ℝ)
    (f : E4 → E) (h : ContDiff ℝ ∞ f) :
    grad i (t • (f ∘ Ortho.motion s.ortho)) x = (t * arrow s i) • grad (s.perm i) f (Ortho.motion s.ortho x) := by
  let R := (Ortho.motion s.ortho).toContinuousLinearMap
  have ht := (h.differentiable (by simp)).comp R.differentiable
  change fderiv ℝ (t • (f ∘ R)) x (basis i)=_
  rw [fderiv_const_smul (ht x), fderiv_comp x (h.differentiable (by simp) _) R.differentiableAt,R.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply]
  rw [show R (basis i)=_ from axis_move s i,map_smul,smul_smul]; rfl

private lemma rotated_curl (s : Signed) (A : Taylor G j) (a b : Axis) :
    Tensor.diagonal (takeCurl (Taylor.turn s.ortho⁻¹ A) a b) = (arrow s a*arrow s b) •
      (Tensor.diagonal (takeCurl A (s.perm a) (s.perm b)) ∘ Ortho.motion s.ortho) := by
  rw [takeCurl_diag,takeCurl_diag,turned_h,turned_h]; funext x
  simp only [Pi.sub_apply,Pi.smul_apply,comp_apply]
  have hh (i : Axis) : ContDiff ℝ ∞ (A.value i) := Tensor.diag_smooth _ _
  rw [rotate_grad _ _ _ _ _ (hh _), rotate_grad _ _ _ _ _ (hh _),
    mul_comm (arrow s b),smul_sub]

private lemma rotated_div (s : Signed) (b : Axis) (A : Shell G j) (x : E4) :
    ∑ a : Axis, grad a (Tensor.diagonal (takeCurl (Taylor.turn s.ortho⁻¹ (gaugeJet A)) a b)) x=0 := by
  have he := (show A.val∈onShell _ _ from A.property).2 (s.perm b) (Ortho.motion s.ortho x)
  simp_rw [rotated_curl,match_leg,rotate_grad s _ x _ _ (Tensor.diag_smooth _ ∞),
    show ∀ i:Axis, arrow s i*arrow s b*arrow s i=arrow s b from fun i=>by unfold arrow; split_ifs <;> ring,
    ← Finset.smul_sum];
  rw [Equiv.sum_comp s.perm (fun a:Axis=> grad a (Tensor.diagonal (A.val a (s.perm b))) (Ortho.motion s.ortho x)), he, smul_zero]

lemma turn_ideal (s : Signed) (h : p∈ Maxwell.equationIdeal G d) : tensor s.ortho p∈Maxwell.equationIdeal G d := by
  rw [ideal_meaning] at *
  intro A
  change read _ (rotated s.ortho p.val)=_
  rw [rotated,eval_changed]
  let Y : Jet G := changedJet (fun i=>Taylor.turn s.ortho⁻¹) (fun i=>gaugeJet (A i))
  have hz (i : ℕ) : ∃ x : Shell G i, gaugeJet x=Y i := by
    have hv : takeCurl (Y i) ∈ onShell G.Color i := ⟨closedCurl _,fun a x=>rotated_div s a (A i) x⟩
    exact ⟨⟨_,hv⟩, Maxwell.potential.symm_apply_apply (Y i)⟩
  choose z ha using hz
  change read Y _ = _; rw [← funext ha]; exact h z
end Orient

lemma conjugate_ideal (h : p∈Maxwell.equationIdeal G d) : realBar p∈Maxwell.equationIdeal G d := by
  rw [Maxwell.ideal_meaning] at *
  intro A
  change read _ (conjPol p.val)=_
  rw [conj_value,h A,star_zero]

lemma turned_grade (s : Signed) (h : p∈ Grade m) : tensor s.ortho p∈Grade m := by
  have he := gradePart_mem m (tensor s.ortho p)
  rw [gradePart_turn,gradePart_self _ _ h] at he; exact he
lemma conjugate_grade (h : p∈Grade m) : realBar p∈Grade m := by
  have ht := gradePart_mem m (realBar p)
  rw [gradePart_bar,gradePart_self _ _ h] at ht; exact ht

lemma star_project (h : Forms H d f p.val) : Forms H d (star f) (realBar p).val := by
  let L := (starL ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have he {F : ℝ → ℂ} (k : ℕ) (ht : ContDiffAt ℝ (k:WithTop ℕ∞) F 0) :
      iteratedDeriv k (fun t=>star (F t)) 0 = star (iteratedDeriv k F 0) := by
    change iteratedFDeriv ℝ k (L ∘ F) 0 _=_
    rw [L.iteratedFDeriv_comp_left ht le_rfl]; rfl
  refine ⟨(realBar p).property.1,fun A => L.contDiff.contDiffAt.comp 0 (h.nice A),fun A k hk=>?_⟩
  change iteratedDeriv k (fun t=>star (f _)) 0 = iteratedDeriv k (fun t=>read _ (conjPol p.val)) 0
  simp_rw [conj_value]
  rw [he k (h.nice_at A k hk), he k (read_smooth A p.val _).contDiffAt,h.through _ k hk]

lemma conj_high (h : p.val∈above m) : (realBar p).val∈above m := by
  refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr (fun i hi=> MvPolynomial.mem_restrictSupport_iff ℂ |>.mp h ?_)
  exact MvPolynomial.support_map_subset (starRingEnd ℂ) p.val hi
lemma signed_high (h : p.val∈above m) (s : Signed) : (tensor s.ortho p).val∈above m :=
    change_above h _



lemma Cone.bar (h : Cone H d m p.val f q.val) : Cone H d m (realBar p).val (star f) (realBar q).val := by
  refine ⟨conjugate_grade h.grows, star_project h.maps, ?_, star_power h.size,h.mark.conj⟩
  change (realBar q-realBar p : Label G d).val∈above m
  rw [← map_sub]; exact conj_high (p:=q-p) h.head
end YM.Push.Mark
