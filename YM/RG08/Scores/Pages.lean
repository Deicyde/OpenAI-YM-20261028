import YM.RG08.Scores.Test
import YM.Push.FINITE_DETECTION.Leading
import YM.Frontier6.Normal.Taylor
/-!
# Taylor re-address estimate on the physical address cell
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Scores.Pages
open Function Filter Set Tensor Push.FiniteDetection.Kelvin
open scoped ContDiff Topology BigOperators

variable {D : ℕ} {R : ℝ} (c : E4) (δ : ℝ)
-- affine map anchored in coarse centered cell

def roll (g : Exam D) : Exam D := ⟨fun x => g.val (c+δ•x), (score D g).comp (show ContDiff ℝ D (fun x:E4=>c+δ•x) from by fun_prop)⟩
def scoreL (D : ℕ) : Exam D →ₗ[ℝ] Exam D where
  toFun := roll c δ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma facades (g : Exam D) (k : ℕ) (h : k≤D) (x : E4) : iteratedFDeriv ℝ k (roll c δ g).val x=δ^k • iteratedFDeriv ℝ k g.val (c+δ•x) := by
  let A := δ • ContinuousLinearMap.id ℝ E4
  let B : E4 → ℝ := fun z => g.val (c+z)
  have hd : ContDiff ℝ D B := (score D g).comp (f:=fun z=> c+z) (by fun_prop)
  rw [show (roll ..).val=B ∘ A from rfl,A.iteratedFDeriv_comp_right hd _ (Nat.cast_le.mpr h)]
  unfold B; rw [iteratedFDeriv_comp_add_left,show A x=δ•x from rfl]
  ext1 v
  let T := iteratedFDeriv ℝ k g.val (c+δ•x)
  simpa using! T.map_smul_univ (fun _ => δ) v
structure Stays (R : ℝ) : Prop where
  nonneg : 0≤δ
  short : δ≤1
  here : c ∈ examinable R
  covers : MapsTo (fun x : E4=> c+δ•x) (examinable R) (examinable R)
lemma roll_paid (h : Stays c δ R) : ∃ A : Sight D R →L[ℝ] Sight D R, ‖A‖≤1 ∧ ∀ g,A (sheet D R g)=sheet D R (roll c δ g) := by
  let L := scoreL c δ D
  have he (g : Exam D) : ‖((sheet D R).comp L) g‖≤1*‖sheet D R g‖ := by
    rw [one_mul]; apply (bound D R (L g) (norm_nonneg _)).2
    rintro ⟨⟨k,hk⟩,v⟩ x
    have hl : k≤D := by omega
    have hX : c+δ•x.val ∈ examinable R := h.covers x.property
    change ‖iteratedFDeriv ℝ k (roll c δ g).val x.val (basis ∘ v)‖ ≤ _
    rw [facades,smul_apply,norm_smul,Real.norm_of_nonneg (pow_nonneg h.nonneg _)]
    · apply le_trans (mul_le_mul_of_nonneg_right (pow_le_one₀ h.nonneg h.short) (norm_nonneg _)); rw [one_mul]
      exact (bound D R g (norm_nonneg _)).1 le_rfl (⟨⟨k,hk⟩,v⟩: Sheet D) ⟨_,hX⟩
    exact hl
  obtain ⟨X,hX,hx⟩:= port (sheet D R) (doors D R) ((sheet D R).comp L) zero_le_one he
  exact ⟨X,hX,fun g=>LinearMap.congr_fun hx g⟩

def scroll (D : ℕ) (h : Stays c δ R) : Sight D R →L[ℝ] Sight D R := (roll_paid (D:=D) c δ h).choose
lemma scroll_leaf (h : Stays c δ R) : ‖scroll c δ D h‖≤1 ∧ ∀ g,scroll c δ D h (sheet D R g)=sheet D R (roll c δ g) := (roll_paid (D:=D) c δ h).choose_spec

def crop (g : Exam D) (k : ℕ) : Exam D := ⟨Tensor.diagonal (coeff g.val k c),diag_smooth (coeff g.val k c) D⟩
def home (g : Exam D) (k : ℕ) : Exam D := roll (-c) 1 (crop c g k)
def cache (g : Exam D) (m : ℕ) : Exam D := ∑ i:Fin m, home c g i.val
def voided (g : Exam D) (m : ℕ) : Exam D := g-cache c g m
private lemma translated (g : Exam D) (i k : ℕ) (h:k≤D) (x : E4) :
    iteratedFDeriv ℝ k (home c g i).val x=iteratedFDeriv ℝ k (crop c g i).val (-c+x) := by
  rw [home, facades _ _ _ _ h]; simp
lemma crop_eq (g : Exam D) (k : ℕ) : (crop c g k).val=Frontier6.Normal.fragment k (fun x : E4=> g.val (c+x)) := by
  unfold crop Frontier6.Normal.fragment
  simp only [coeff, iteratedFDeriv_comp_add_left,add_zero]
private lemma activates (g : Exam D) (i k : ℕ) (h:k≤D) : iteratedFDeriv ℝ k (home c g i).val c=if i=k then iteratedFDeriv ℝ k g.val c else 0 := by
  rw [translated _ _ _ _ h,neg_add_cancel]
  split_ifs with hr
  · subst i
    have hv : ContDiffAt ℝ k g.val c := ((score D g).of_le (Nat.cast_le.mpr h)).contDiffAt
    have he := diag_response (coeff g.val k c) (?_ : Sym (coeff g.val k c)) 0
    · exact smul_right_injective (E4 [×k]→L[ℝ] ℝ) (show ((k.factorial:ℝ)⁻¹) ≠ 0 from by positivity) he
    exact coeff_symm hv
  rw [crop_eq]
  exact Frontier6.Normal.zero_fragment k i (Ne.symm hr)
private lemma diag_down {k m:ℕ} {T : Tensor.T E4 ℝ k} (h:Sym T) (ht:k<m) : iteratedFDeriv ℝ m (Tensor.diagonal T)=0 := by
  induction m,ht using Nat.le_induction with
  | base => exact funext (diag_above T h)
  | succ p hp ih => ext; simp [iteratedFDeriv_succ_eq_comp_left,ih]
private lemma draining (g : Exam D) {m k : ℕ} (h:m≤k) (ht:k≤D) (x : E4) : iteratedFDeriv ℝ k (cache c g m).val x=0 := by
  rw [cache,Submodule.coe_sum, iteratedFDeriv_sum_apply]
  · apply Finset.sum_eq_zero; intro i _
    rw [translated _ _ _ _ ht]; exact congr_fun (diag_down (T:=coeff g.val i.val c) (coeff_symm (by
      exact ((score D g).of_le (Nat.cast_le.mpr (by omega))).contDiffAt)) (by omega : i.val<k)) _
  intro i _; exact ((score D (home c g i.val)).of_le (Nat.cast_le.mpr ht)).contDiffAt
lemma void_cost (g : Exam D) (m : ℕ) (k : ℕ) (ht:k≤D) :
    (k<m → iteratedFDeriv ℝ k (voided c g m).val c=0) ∧
    (m≤k → iteratedFDeriv ℝ k (voided c g m).val=iteratedFDeriv ℝ k g.val) := by
  have he x : iteratedFDeriv ℝ k (voided c g m).val x=iteratedFDeriv ℝ k g.val x-iteratedFDeriv ℝ k (cache c g m).val x :=
    iteratedFDeriv_sub_apply ((score D g).of_le (Nat.cast_le.mpr ht) |>.contDiffAt) ((score D (cache c g m)).of_le (Nat.cast_le.mpr ht) |>.contDiffAt)
  constructor
  · intro hp
    rw [he,cache, Submodule.coe_sum,iteratedFDeriv_sum_apply]
    · simp_rw [activates _ _ _ _ ht]
      rw [Finset.sum_eq_single (⟨k,hp⟩:Fin m),if_pos rfl,sub_self]
      · intro b _ hb; rw [if_neg (show b.val≠k from fun h=> hb (Fin.ext h))]
      simp
    intro i _; exact ((score D (home c g i.val)).of_le (Nat.cast_le.mpr ht)).contDiffAt
  intro hp; exact funext fun x=>by rw [he,draining _ _ hp ht,sub_zero]
end YM.RG08.Scores.Pages
