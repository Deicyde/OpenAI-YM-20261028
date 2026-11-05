import YM.Extra.SOURCE_HISTORIES.Motion

/-! Average with respect to the true orientation group, charged BEFORE L.
Only changing orientation & extending linearly on the rebased basis, no new
physical reference normalization. Group operations don't get cheaper when
the masks change. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Motion
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ}

set_option maxRecDepth 4000 in
theorem card_pos : 0<Fintype.card Motion := Fintype.card_pos

def share : ℝ := (Fintype.card Motion : ℝ)⁻¹

set_option maxRecDepth 4000 in
theorem share_pos : 0 < share := inv_pos.mpr (by exact_mod_cast card_pos)

variable (F : Labels.Frame G d)

abbrev Tally := Motion × F.Index

/-- Coefficients on the twisted-column dictionary. **Complex linear**
on normalized columns, even with flips. -/
def chips : F.Coeff →ₗ[ℂ] Tally F → ℂ where
  toFun v x := (share:ℂ) * scalar x.1 (patch F (backward x.1) v x.2)
  map_add' u v := by ext1 i; simp [patch_add,scalar_add,mul_add]
  map_smul' c v := by
    ext1 i
    have he : scalar (backward i.1) c = scalar i.1 c := rfl
    simp only [patch_smul,he,Pi.smul_apply,smul_eq_mul, RingHom.id_apply,scalar_mul,scalar_self]; ring

lemma norm_chips (x : Tally F) (v : F.Coeff) : ‖chips F v x‖=share*‖patch F (backward x.1) v x.2‖ := by
  change ‖(share:ℂ)*_‖=_; rw [norm_mul,norm_scalar,Complex.norm_real,Real.norm_of_nonneg share_pos.le]

/-- Reynolds average of the chosen rebased column outputs X. -/
def repaint (X : F.Index → F.Coeff) (v : F.Coeff) : F.Coeff :=
    ∑ j : Tally F,chips F v j • patch F j.1 (X j.2)

private def drawing (X : F.Index → F.Coeff) (v : F.Coeff) (m : Motion) : F.Coeff :=
    patch F m (∑ i, patch F (backward m) v i • X i)

lemma modal (X : F.Index → F.Coeff) (v : F.Coeff) : repaint F X v = (share:ℂ) • ∑ m : Motion,
    patch F m (∑ i, patch F (backward m) v i • X i) := by
  rw [repaint,Fintype.sum_prod_type,Finset.smul_sum]
  simp_rw [patch_sum,patch_smul,Finset.smul_sum, chips, LinearMap.coe_mk, AddHom.coe_mk,mul_smul]

lemma repainted_H (s : Signed) (X : F.Index → F.Coeff) (v : F.Coeff) :
    F.act s.ortho (repaint F X v)=repaint F X (F.act s.ortho v) := by
  have he (t : Signed) (b : Bool) : F.act s.ortho (drawing F X v (t,b)) = drawing F X (F.act s.ortho v) (s*t,b) := by
    unfold drawing patch backward
    cases b
    · simp only [Bool.false_eq_true,if_false,mul_inv_rev, ← Frame.act_mul]
      rw [show (t⁻¹ * s⁻¹).ortho = t⁻¹.ortho * s.ortho⁻¹ by
        rw [show (t⁻¹ * s⁻¹).ortho = t⁻¹.ortho * s⁻¹.ortho from map_mul Signed.inclusionO ..]; rw [show s⁻¹.ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s],
        show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..]; simp
    simp only [if_true,mul_inv_rev,act_conj,← Frame.act_mul]
    rw [show (t⁻¹ * s⁻¹).ortho = t⁻¹.ortho * s.ortho⁻¹ by
      rw [show (t⁻¹ * s⁻¹).ortho = t⁻¹.ortho * s⁻¹.ortho from map_mul Signed.inclusionO ..]; rw [show s⁻¹.ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s],
      show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..]; simp
  rw [modal,modal,map_smul,map_sum]
  change (share:ℂ) • (∑ m : Motion, F.act s.ortho (drawing F X v m)) = (share:ℂ) • (∑ m : Motion, drawing F X (F.act s.ortho v) m)
  simp_rw [Fintype.sum_prod_type, he]
  rw [show ∑ t : Signed, ∑ b, drawing F X (F.act s.ortho v) (s*t,b) = _ from
    Equiv.sum_comp (Equiv.mulLeft s) (fun t => ∑ b : Bool, drawing F X (F.act s.ortho v) (t,b))]

lemma repainted_star (X : F.Index → F.Coeff) (v : F.Coeff) :
    star (repaint F X v)=repaint F X (star v) := by
  have he (s : Signed) (b : Bool) : star (drawing F X v (s,b)) = drawing F X (star v) (s,b.not) := by
    cases b <;> simp [drawing,patch,backward,act_conj]
  rw [modal,modal,star_smul,star_sum]
  change star (share:ℂ) • (∑ m:Motion, star (drawing F X v m))=(share:ℂ) • (∑ m:Motion, drawing F X (star v) m)
  simp_rw [Fintype.sum_prod_type,Fintype.sum_bool,he]; simp [add_comm]

lemma repainted_eq (X : F.Index → F.Coeff) (v : F.Coeff) (m : Motion) :
    patch F m (repaint F X v)=repaint F X (patch F m v) := by
  unfold patch; split <;> simp only [repainted_H,repainted_star]

set_option maxRecDepth 4000 in
private lemma bills_const {E : Type*} [AddCommGroup E] [Module ℂ E] (v : E) :
    (share:ℂ) • (∑ _ : Motion, v) = v := by
  have ht := card_pos
  simp only [Finset.sum_const, Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul ℂ _ _, smul_smul]; simp only [share, Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ (show (Fintype.card Motion:ℂ)≠0 from Nat.cast_ne_zero.mpr ht.ne'), one_smul]

/-- Averaging doesn't change an equivariant leading part. -/
lemma repaint_same (Q : F.Coeff →ₗ[ℂ] F.Coeff) (h : ∀ x m,patch F m (Q x)=Q (patch F m x)) (v : F.Coeff) :
    repaint F (fun i => Q (Size.axis F i)) v = Q v := by
  rw [modal]
  simp_rw [← map_smul,← map_sum,Size.sum_axes,h,round]
  exact bills_const _

set_option maxRecDepth 4000 in
/-- Density or response f intertwining the literal moves. -/
lemma field_same {n : Side} (f : F.Coeff →ₗ[ℂ] Config G n → ℂ)
    (h : ∀ v m,dance m (f v)=f (patch F m v)) (v : F.Coeff) (U : Config G n) :
    ∑ j : Tally F, chips F v j * dance j.1 (f (Size.axis F j.2)) U = f v U := by
  have hz (m : Motion) : ∑ j : F.Index, chips F v (m,j) * dance m (f (Size.axis F j)) U = (share:ℂ) • f v U := by
    let x := patch F (backward m) v
    have he : (∑ j, scalar m (x j) • patch F m (Size.axis F j)) = v := by
      simp_rw [← patch_smul, ← patch_sum,Size.sum_axes]; exact round F m v
    calc
      _ = (share:ℂ) • f (∑ j, scalar m (x j) • patch F m (Size.axis F j)) U := by
        simp_rw [h,map_sum,Finset.sum_apply,map_smul,Pi.smul_apply, Finset.smul_sum, smul_eq_mul, chips]
        exact Finset.sum_congr rfl fun i _ => mul_assoc ..
      _ = (share:ℂ) • f v U := by rw [he]
  simp_rw [Fintype.sum_prod_type,hz,← Finset.smul_sum]
  simpa only [Fintype.sum_prod_type] using bills_const (E:=ℂ) (f v U)

section invoices
/-- Cost comparison for diagonal-weighted l1 sums. -/
private lemma core_axes (L : Side) (v : F.Coeff) : ∑ i, ‖v i‖ * F.coeffSize (vowel F L (F.core (Size.axis F i))) =
    F.coeffSize (vowel F L (F.core v)) := by
  -- expand pointwise. `core` deletes ONLY i=0
  unfold Frame.coeffSize
  refine Finset.sum_congr rfl fun i _ => ?_
  have he (v : F.Coeff) : ‖vowel F L v i‖=(L.val:ℝ)^(d-(F.grades i).1)*‖v i‖ := by
    unfold vowel; rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
  rw [he]
  have ht : F.core v i = update v 0 0 i := rfl
  by_cases hi : i = 0
  · subst i
    rw [Size.core_axis,ht]; simp [vowel]
  rw [Size.core_axis,if_neg hi,ht,update_of_ne hi,Finset.sum_eq_single i, he]
  · simp [Size.axis,mul_comm]
  · intro b _ hb; simp [Size.axis,vowel,Pi.single_eq_of_ne hb]
  simp

lemma vowel_tab (L : Side) (v : F.Coeff) :
    (∑ i : Tally F, ‖chips F v i‖ * F.coeffSize (vowel F L (F.core (Size.axis F i.2)))) ≤
      orbitCost F * F.coeffSize (vowel F L (F.core v)) := by
  have he (z : Motion) : (∑ i, ‖chips F v (z,i)‖ * F.coeffSize (vowel F L (F.core (Size.axis F i)))) ≤
      share * (orbitCost F * F.coeffSize (vowel F L (F.core v))) := by
    simp_rw [norm_chips,mul_assoc,← Finset.mul_sum,core_axes]
    apply mul_le_mul_of_nonneg_left _ share_pos.le
    rw [← core_patch, ← patch_vowel]
    exact patch_cost ..
  rw [Fintype.sum_prod_type]
  refine le_trans (Finset.sum_le_sum fun i _ => he i) (le_of_eq ?_)
  have ht := card_pos
  simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, show (Fintype.card Motion : ℝ)*share=1 from mul_inv_cancel₀ (Nat.cast_ne_zero.mpr ht.ne'), one_mul]

lemma core_tab (v : F.Coeff) :
    (∑ i : Tally F, ‖chips F v i‖ * F.coeffSize (F.core (Size.axis F i.2))) ≤ orbitCost F * F.coeffSize (F.core v) := by
  let L : Side := ⟨1,by decide⟩
  have he (v) : vowel F L v = v := funext fun i => by simp [vowel,L]
  simpa only [he] using vowel_tab F L v
end invoices
end YM.Extra.Histories.Motion
