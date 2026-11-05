import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Window
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.Push.FREE_RESOLVENT.Masking



/-!
# Full-coordinate API, including resolvent windows (u ≥ 0)

The substitution and chart prices are on active coordinates. A consumer on
the *completed* link bases can still use exactly the windows of either
implementation and the same Gram matrix--after PROJECTION. Compressing
after inversion of the unprojected matrix is NOT certified here! The
postselection completion is `Shell.pad` from FreeResolvent; ordered-window
versions proved here use its precise choice, even for comparisons to tree-
only data. Include determinant and cross-block statements. Unlike
`Completion.stamp`, use any indexing & arbitrary u. Window centers can
be vacant. Self membership is needed at least on vacant centers. This
file supplies pure algebra; hypotheses Gap or centers will only be used
as paid (see later papers).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange FreeResolvent Shell Function Set Matrix
open scoped Classical BigOperators
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α)

/-- Fill A from *active* coordinates. At t=1 corresponding to . -/
def shells (M : Matrix β β ℝ) (t : ℝ) := insertion e * M * (insertion e).transpose + t • FreeResolvent.Shell.off e


lemma shells_live (M : Matrix β β ℝ) (t : ℝ) (i j : β) : shells e M t (e i) (e j)=M i j := by
  unfold shells
  simp [Matrix.mul_apply,insertion,e.injective.eq_iff,Shell.off_test,ite_mul,mul_ite,smul_eq_mul]

lemma shells_dry_left (M : Matrix β β ℝ) (t : ℝ) {i : α} (h : i ∉ range e) (j : α) :
    shells e M t i j=t * (1:Matrix α α ℝ) i j := by
  have ht (b : β) : e b ≠ i := fun H => h ⟨_,H⟩
  simp [shells,Matrix.mul_apply,insertion,ht,Shell.off_test,h,Matrix.one_apply,smul_eq_mul]
lemma shells_dry_right (M : Matrix β β ℝ) (t : ℝ) (i : α) {j : α} (h : j ∉ range e) :
    shells e M t i j=t * (1:Matrix α α ℝ) i j := by
  have ht (b : β) : e b ≠ j := fun H => h ⟨_,H⟩
  by_cases hi : i=j
  · subst j; exact shells_dry_left _ _ _ h _
  simp [shells,Matrix.mul_apply,insertion,ht,Shell.off_test,hi,smul_eq_mul]

/-- A single principal window on full addresses. -/
def fragment (s : Set α) : (e ⁻¹' s) ↪ s where
  toFun t := ⟨e t.val,t.property⟩
  inj' _ _ h := Subtype.ext (e.injective (congr_arg (fun t : s => (t:α)) h))

lemma fragment_hits {s : Set α} (i : s) : i∈range (fragment e s) ↔ i.val∈range e := by
  constructor
  · intro ⟨t,ht⟩; exact ⟨t.val,congr_arg (fun x : s=> (x:α)) ht⟩
  rintro ⟨t,ht⟩
  exact ⟨⟨t,(show e t∈s from ht ▸ i.property)⟩,Subtype.ext ht⟩

lemma shells_principal (M : Matrix β β ℝ) (t : ℝ) (s : Set α) :
    SectorChange.Schur.principal (shells e M t) s =
      shells (fragment e s) (SectorChange.Schur.principal M (e ⁻¹' s)) t := by
  ext i j
  let E := fragment e s
  by_cases hi : i∈range E
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : j∈range E
    · obtain ⟨b,rfl⟩ := hj
      change shells e M t (e ↑a) (e ↑b)=shells E _ t (E a) (E b)
      rw [shells_live,shells_live]; rfl
    have h : j.val∉range e := mt (fragment_hits e j).mpr hj
    change shells e M t _ j.val=shells E _ t _ j
    rw [shells_dry_right _ _ _ _ h,shells_dry_right _ _ _ _ hj,Matrix.one_apply,Matrix.one_apply]
    simp [show (E a).val≠j.val from fun he => hj ⟨_,Subtype.ext he⟩,show E a≠j from fun he => hj ⟨_,he⟩]
  have h : i.val∉range e := mt (fragment_hits e i).mpr hi
  change shells e M t i.val j.val=shells E _ t i j
  rw [shells_dry_left _ _ _ h,shells_dry_left _ _ _ hi,Matrix.one_apply,Matrix.one_apply]; simp [Subtype.val_inj]

lemma shells_times (M N : Matrix β β ℝ) (s t : ℝ) : shells e M s * shells e N t = shells e (M*N) (s*t) := by
  let B := insertion e; let H := FreeResolvent.Shell.off e
  have h : (B*M*B.transpose)*(B*N*B.transpose)=B*(M*N)*B.transpose := by
    have hp : B.transpose * B=1 := Shell.pin e
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B.transpose B,hp,Matrix.one_mul]
  have he : H*B=0 := barred e; have ht : B.transpose*H=0 := barred_left e
  have hh : H*H=H := off_off e
  unfold shells; change (B*M*B.transpose+s • H)*(B*N*B.transpose + t • H)=_
  rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,h,Matrix.mul_smul, Matrix.mul_assoc (B*M), ht, Matrix.mul_zero, smul_zero, add_zero,
    Matrix.smul_mul, ← Matrix.mul_assoc H, ← Matrix.mul_assoc H,he,Matrix.zero_mul,Matrix.zero_mul,smul_zero,zero_add,
    Matrix.smul_mul,Matrix.mul_smul,hh,smul_smul]
lemma shells_one : shells e 1 1=1 := by
  simp only [shells,one_smul,Matrix.mul_one, Shell.off,Shell.rim]; abel
lemma shells_shift (M : Matrix β β ℝ) (s t : ℝ) :
    shells e M s + t • 1=shells e (M+t • 1) (s+t) := by
  rw [← shells_one e]
  simp only [shells,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,smul_add, add_smul, one_smul]; abel
lemma shells_inv (M : Matrix β β ℝ) {s} (h : IsUnit M.det) (hs : s≠0) :
    (shells e M s)⁻¹=shells e M⁻¹ s⁻¹ := Matrix.inv_eq_right_inv (by rw [shells_times,M.mul_nonsing_inv h,mul_inv_cancel₀ hs,shells_one])

/-- First compress E-*completed* matrix to a window, then invert. -/
lemma shells_principal_inv (M : Matrix β β ℝ) (t : ℝ) (s : Set α) {u}
    (h : IsUnit ((SectorChange.Schur.principal M (e ⁻¹' s) + u • 1).det))
    (ht : t+u≠0) :
    (SectorChange.Schur.principal (shells e M t) s + u • 1)⁻¹ =
      shells (fragment e s) ((SectorChange.Schur.principal M (e ⁻¹' s)+u • 1)⁻¹) (t+u)⁻¹ := by
  rw [shells_principal,shells_shift,shells_inv _ _ h ht]

/-- Pull whole window family back to active (always about the *same*
center, not active-only geometry). -/
def aperture (W : α → Set α) (i : β) := e ⁻¹' (W (e i))

/-- Full-space propagation of ordered columns, including those requested
with identity at a missing link. Meet only weak invertibility hypotheses.
Actual use is t=1 and u≥0, positive through a paid gap. -/
theorem shells_pane (M : Matrix β β ℝ) (t : ℝ) (W : α → Set α) {u}
    (h : ∀ i, IsUnit (SectorChange.Schur.principal M (e ⁻¹' W i) + u • 1).det)
    (ht : t+u≠0) (hh : ∀ i, i ∈ W i) :
    pane W (shells e M t) u = shells e (pane (aperture e W) M u) (t+u)⁻¹ := by
  ext i j
  by_cases hi : i∈range e
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : j∈range e
    · obtain ⟨b,rfl⟩ := hj
      rw [shells_live]
      let s := W (e b)
      by_cases hA : e a∈s
      · let c : (e ⁻¹' s) := ⟨a,hA⟩; let d : (e ⁻¹' s) := ⟨b,hh _⟩
        rw [pane_read W _ u (hh _) hA,pane_read (aperture e W) M u (show b∈aperture e W b from hh _) hA,
          shells_principal_inv e M t (W (e b)) (h _) ht]
        exact shells_live (fragment e s) _ (t+u)⁻¹ c d
      rw [pane_absent W _ u (Or.inr hA),pane_absent (aperture e W) M u (show b ∉ aperture e W b ∨ a∉aperture e W b from Or.inr hA)]
    have hx : e a≠j := fun H => hj ⟨a,H⟩
    rw [shells_dry_right _ _ _ _ hj,Matrix.one_apply,if_neg hx,mul_zero]
    let s := W j
    by_cases he : e a∈s
    · let c : s := ⟨e a,he⟩; let d : s := ⟨j,hh _⟩
      rw [pane_read W _ u (hh _) he,shells_principal_inv e M t (W j) (h _) ht]
      change shells (fragment e s) _ (t+u)⁻¹ c d = 0
      rw [shells_dry_right _ _ _ _ (show d∉range (fragment e s) from mt (fragment_hits e d).mp hj),
        Matrix.one_apply,if_neg (fun H => hx (congr_arg Subtype.val H)),mul_zero]
    exact pane_absent W _ u (Or.inr he)
  rw [shells_dry_left _ _ _ hi,Matrix.one_apply]
  let s := W j
  by_cases he : i∈s
  · let c : s := ⟨i,he⟩; let d : s := ⟨j,hh _⟩
    rw [pane_read W _ u (hh _) he,shells_principal_inv e M t (W j) (h _) ht]
    change shells (fragment e s) _ (t+u)⁻¹ c d = _
    rw [shells_dry_left _ _ _ (show c∉range (fragment e s) from mt (fragment_hits e c).mp hi),Matrix.one_apply]
    by_cases hx : i=j
    · rw [if_pos (Subtype.ext hx),if_pos hx]
    rw [if_neg (fun H => hx (congr_arg Subtype.val H)),if_neg hx]
  rw [pane_absent W _ u (Or.inr he),if_neg (show i≠j from fun H => he (H.symm ▸ hh j)),mul_zero]













/-! Determinant has no extra measure factor at t=1. -/






/-! Expose use with the literal whole Mid implementation. Actual Q and
coverage hypotheses follow from physical assembled prices, later. -/
open Lattice Wilson RG Pressure Pressure.Stores Tree
open SectorChange.Gaussian Rows
variable {c f : Side}


end YM.AnalyticBridge.LocalGaussianLaws
