import YM.Push.LOOP_COEFFICIENT.SignatureLines

/-!
# Uniqueness of the kinetic line, degree-three cancellation in the initial-site convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Complex Matrix Set Lattice Bloch Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {p : Momentum} {b : Bool} {V W : Momentum → Matrix (Axes G) (Axes G) ℂ} {n : ℕ}

def unsigned (s : Equiv.Perm Axis) : Signed := ⟨s,fun _ => false⟩
lemma permuting {i j a b : Axis} (h : i ≠ j) (h' : a ≠ b) : ∃ s : Equiv.Perm Axis, s i = a ∧ s j = b := by
  let t := Equiv.swap i a
  have he : t j ≠ a := by rw [← show t i = a from Equiv.swap_apply_left ..]; simpa using h.symm
  exact ⟨Equiv.swap (t j) b * t,by simp [t, Equiv.swap_apply_of_ne_of_ne he.symm h'],by simp⟩

variable (hd : ContDiffAt ℂ ω V 0)
include hd
lemma mark_add₁ (u v : Momentum) : mark V 1 (u+v) = mark V 1 u + mark V 1 v := by
  ext i j; simp only [Matrix.add_apply,mark,of_apply,line_one (analyticComponent hd i j),map_add]

lemma mark_span₁ (h : ∀ j, mark V 1 (unitAxis j) = 0) (p : Momentum) : mark V 1 p = 0 := by
  ext i j; simp only [mark,of_apply,line_one (analyticComponent hd i j)]
  rw [← unit_span p,map_sum]; change _ = (0:ℂ); apply Finset.sum_eq_zero; intro k _; rw [map_smul]
  change p k * (fderiv ℂ _ 0 (unitAxis k)) = 0
  rw [show fderiv ℂ (fun z => V z i j) 0 (unitAxis k) = 0 from (line_one (analyticComponent hd i j) ..).symm.trans (congr_fun (congr_fun (h k) i) j),mul_zero]

lemma mark_cross (u v : Momentum) : mark V 2 (u+v) + mark V 2 (-u+v) = (2:ℂ) • (mark V 2 u + mark V 2 v) := by
  ext i j; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,mark,of_apply,line_two (analyticComponent hd i j),map_add,map_neg,_root_.add_apply, _root_.neg_apply]; ring

lemma mark_span₂ (h : ∀ j, mark V 2 (unitAxis j) = 0) (h' : ∀ i j, i ≠ j → mark V 2 (unitAxis i + unitAxis j) = 0) (p : Momentum) : mark V 2 p = 0 := by
  ext i j; let D := fderiv ℂ (fderiv ℂ fun z => V z i j) 0
  have hd' u : D u u = mark V 2 u i j := (line_two (analyticComponent hd i j) u).symm
  rw [← hd']; change D p p = 0
  let S (k l : Axis) := p k * (p l * D (unitAxis k) (unitAxis l))
  rw [show D p p = ∑ k, ∑ l, S k l from ?_]
  · have he k l : S k l = -S l k := by
      have hh k := (hd' (unitAxis k)).trans (congr_fun (congr_fun (h k) i) j)
      by_cases ha : k=l
      · subst l; simp [hh,S]
      have hb := (hd' (unitAxis k + unitAxis l)).trans (congr_fun (congr_fun (h' k l ha) i) j)
      simp only [map_add,_root_.add_apply,hh,Matrix.zero_apply, zero_add,add_zero] at hb
      dsimp [S]; linear_combination p k * p l * hb
    have hm : ∑ k, ∑ l, S k l = -(∑ k, ∑ l, S k l) := by
      conv_lhs => rw [Finset.sum_comm]; arg 2; ext; arg 2; ext; rw [he]
      simp
    linear_combination hm / 2
  conv_lhs => rw [← unit_span p]
  simp [S,Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intros; ring

namespace Signature
variable (h : Signature G b V)
include h
private lemma atAxis (hs : Short V n) (i j : Axes G) : mark V n (unitAxis j.1) i j = 0 := by
  simpa [unitAxis,Pi.single_apply,mul_ite] using h.transversal hd hs (unitAxis j.1) i j.2
private lemma atAxisLeft (hs : Short V n) (i j : Axes G) : mark V n (unitAxis i.1) i j = 0 := by
  have := congr_fun (congr_fun (h.mark_symmetry hd (unitAxis i.1) n) i) j
  rw [transpose_apply,h.atAxis hd hs,mark_neg, Matrix.smul_apply, smul_eq_mul] at this
  simpa using this.symm
private lemma atSum (hs : Short V n) (i j : Axes G) (k : Axis) :
    mark V n (unitAxis j.1 + unitAxis k) i j + mark V n (unitAxis j.1 + unitAxis k) i (k,j.2) = 0 := by
  simpa [mul_add, Finset.sum_add_distrib, mul_ite,unitAxis,Pi.single_apply] using h.transversal hd hs (unitAxis j.1 + unitAxis k) i j.2
lemma short_two : Short V 2 := by
  have he := h.short_one hd
  apply he.succ; apply mark_span₁ hd
  intro k; ext i j
  have ht := h.atSum hd he i j k
  rw [mark_add₁ hd] at ht; simp only [Matrix.add_apply,h.atAxis hd he i j,h.atAxis hd he i (k,j.2),add_zero,zero_add] at ht
  change mark V 1 (unitAxis k) i j = 0
  by_cases ha : i.1 = k
  · rw [← ha]; apply h.atAxisLeft hd he
  by_cases hb : i.1 = j.1
  · rw [← hb,h.atAxisLeft hd he,add_zero] at ht; exact ht
  let s := unsigned (Equiv.swap k j.1)
  have hs := h.mark_spin hd he s (Or.inr (fun _ => rfl)) (unitAxis k) i j
  simp only [unit_act,s,unsigned,Bool.false_eq_true,if_false, Equiv.swap_apply_left,Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne ha hb,one_mul,one_smul,Prod.mk.eta] at hs
  rw [hs] at ht; linear_combination ht / 2
end Signature

/-- Polarized potential kernel, not half its Hessian. Momentum Taylor
coefficient in the transverse diagonal real direction (divided derivative). -/
def probe₂ (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (a : G.ColorIndex) : ℂ := mark V 2 (unitAxis 0) (1,a) (1,a) / 2

namespace Signature
lemma probe_real (h : Signature G b V) (a) : ((probe₂ V a).re:ℂ) = probe₂ V a := conj_eq_iff_re.mp
    (by unfold probe₂; rw [map_div₀,← Complex.star_def, h.mark_diagonal_star hd _ (unit_star 0)]; simp)

variable (h : Signature G true V)
include h
lemma mark_axis₂ {a : G.ColorIndex} (hG : G.Simple) (hα : probe₂ V a = 0) (k : Axis) : mark V 2 (unitAxis k) = 0 := by
  ext i j; change _ = 0
  have he := h.short_two hd
  have hp := (div_eq_zero_iff.mp hα).resolve_right (by norm_num)
  by_cases ha : i.1 = j.1
  · by_cases hb : j.1 = k
    · rw [← hb,h.atAxis hd he]
    obtain ⟨s,hs,ht⟩ := permuting (i:=0) (j:=1) (by decide) (Ne.symm hb)
    have hh := h.mark_spin hd he (unsigned s) (Or.inl rfl) (unitAxis 0) (1,a) (1,a)
    simp only [unit_act,unsigned,Bool.false_eq_true,if_false,hs,ht,one_mul,one_smul,hp] at hh
    rw [h.mark_color hd hG a]; simp [ha,hh]
  let s := Signed.mirror i.1
  have hv := h.mark_spin hd he s (Or.inl rfl) (unitAxis k) i j
  simp only [unit_act,s,Signed.mirror,Equiv.refl_apply,decide_true,if_true,decide_eq_true_eq,ha,if_false,neg_mul,one_mul,Prod.mk.eta] at hv
  split at hv
  · simp only [neg_smul,one_smul,mark_neg,neg_sq,one_pow] at hv
    linear_combination hv / 2
  simp only [one_smul] at hv; linear_combination hv / 2

lemma mark_pair₂ {a : G.ColorIndex} (hG : G.Simple) (hα : probe₂ V a = 0) {l k : Axis} (hlk : l≠k) : mark V 2 (unitAxis l + unitAxis k) = 0 := by
  let p := unitAxis l + unitAxis k
  have hm := h.mark_axis₂ hd hG hα
  have hS := h.short_two hd
  have hdia (i j : Axes G) (he : i.1=j.1) : mark V 2 p i j = 0 := by
    let s := Signed.mirror l
    have hs := h.mark_spin hd hS s (Or.inl rfl) p i j
    simp only [p,Signed.act_add,s,unit_act,Signed.mirror,Equiv.refl_apply,hlk, Prod.mk.eta,decide_eq_true_eq, ite_true, ite_false,neg_smul,one_smul] at hs
    rw [he] at hs
    have ht : mark V 2 (-unitAxis l + unitAxis k) i j = mark V 2 p i j := hs.trans (by split <;> simp [p])
    have hv := mark_cross hd (unitAxis l) (unitAxis k); rw [hm,hm,zero_add,smul_zero] at hv
    have hv' : mark V 2 p i j + mark V 2 (-unitAxis l + unitAxis k) i j = 0 := congr_fun (congr_fun hv i) j
    rw [ht] at hv'; linear_combination hv' / 2
  have hoff (i j : Axes G) (ha : i.1≠l) (hb : i.1≠k) (hc : i.1≠j.1) : mark V 2 p i j = 0 := by
    have hv := h.mark_spin hd hS (Signed.mirror i.1) (Or.inl rfl) p i j
    simp only [p,Signed.act_add,unit_act,Signed.mirror,Equiv.refl_apply,ha,hb,hc,Prod.mk.eta,decide_eq_true_eq, ite_true, ite_false,one_smul,neg_mul,one_mul] at hv
    dsimp [p]; linear_combination hv / 2
  ext ⟨i,b⟩ ⟨j,c⟩; change mark V 2 p (i,b) (j,c) = 0
  by_cases h₁ : i=j
  · exact hdia _ _ h₁
  by_cases hi : i=l ∨ i=k
  swap
  · exact hoff _ _ (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)) h₁
  by_cases hj : j=l ∨ j=k
  swap
  · have hv := h.mark_symmetry hd p 2
    rw [mark_neg,neg_sq,one_pow,one_smul] at hv
    rw [← hv,transpose_apply]; exact hoff _ _ (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h)) (Ne.symm h₁)
  have ht : mark V 2 p (i,b) (l,c) + mark V 2 p (i,b) (k,c) = 0 := h.atSum hd hS (i,b) (l,c) k
  rcases hi with rfl|rfl <;> rcases hj with rfl|rfl
  · exact (h₁ rfl).elim
  · rwa [hdia (i,b) (i,c) rfl,zero_add] at ht
  · rwa [hdia (i,b) (i,c) rfl,add_zero] at ht
  exact (h₁ rfl).elim

lemma short_three {a : G.ColorIndex} (hG : G.Simple) (hα : probe₂ V a = 0) : Short V 3 := (h.short_two hd).succ
  (mark_span₂ hd (h.mark_axis₂ hd hG hα) (fun _ _ he => h.mark_pair₂ hd hG hα he))

lemma short_four_of_short_three (hs : Short V 3) : Short V 4 := by
  apply hs.succ; intro p; ext i j; change _ = 0
  let s : Signed := ⟨Equiv.refl _,fun _ => true⟩
  have he := h.mark_spin hd hs s (Or.inl rfl) p i j
  rw [show s.act p = -p from rfl,mark_neg] at he
  simp [s] at he; linear_combination -he / 2

lemma relative_four {a : G.ColorIndex} (hG : G.Simple) (hw : Signature G true W) (hu : ContDiffAt ℂ ω W 0)
    (hα : probe₂ W a = 1) : Short (fun p => V p - (probe₂ V a) • W p) 4 := by
  have h' := h.sub (hw.smul (probe₂ V a).re)
  rw [h.probe_real hd] at h'
  have hd' := hd.sub (hu.const_smul (probe₂ V a))
  apply h'.short_four_of_short_three hd'; apply h'.short_three hd' hG (a:=a)
  unfold probe₂ at *; rw [mark_sub hd (hu.const_smul _),mark_smul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  linear_combination -(mark V 2 (unitAxis 0) (1,a) (1,a) / 2) * hα
end Signature
end YM.Push.Loops
