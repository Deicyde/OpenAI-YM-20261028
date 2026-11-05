import YM.Org.Theatre
import YM.Push.STRESS_FLUX.Haar

/-!
when adding back contact-free Wilson equation terms, do it even on the
*full joint array*, before taking the reciprocal-cardinality replication root. The null test
in the hypothesis of `restore_root` below is proved from concrete finite integration by
parts for combinations of the form `restore_equations`; separation is from all active links
including on copies. A varying top coefficient is allowed. No assertion that contact error
is small when the stencils overlap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Lattice Cells Wilson RG Function Set Filter Gauge MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} (T : Tiling n) {A B : Config G n → ℂ}
variable (β : ℝ)

private lemma one_restore (h : Interior (T.chamber 0) A) (hB : Interior (T.chamber 0) B)
    (hnull : ∀ F : Config G n → ℂ, Interior (T.chamber 0)ᶜ F → moment β (fun U => (A U - B U)*F U)=0)
    (v : T.Cell) {F : Config G n → ℂ} (he : Interior (T.chamber v)ᶜ F) :
    moment β (fun U => T.copy v A U * F U) = moment β (fun U => T.copy v B U * F U) := by
  have ht : (T.chamber v)ᶜ ⊆ univ := subset_univ _
  have hs : T.chamber v ⊆ univ := subset_univ _
  let s := T.omega v
  let b := T.translateBy v
  let z := -s⁻¹.act b
  have hM : MapsTo (affine s⁻¹ z) (T.chamber v)ᶜ (T.chamber 0)ᶜ := fun y hy hw => by
    apply hy; have hf : affine s b (affine s⁻¹ z y) ∈ T.chamber v := (T.reflected_chamber _ v).mp hw
    simpa [affine,z] using hf
  let R := F ∘ pull s⁻¹ z
  have hr : Interior (T.chamber 0)ᶜ R := he.unchanged s⁻¹ z hM
  have hp (U : Config G n) : pull s b (pull s⁻¹ z U) = U := by rw [pull_pull, affine, show s⁻¹.act b+z=0 from add_neg_cancel _, inv_mul_cancel,pull_id]
  classical
  rw [← sub_eq_zero, moment,moment,← integral_sub (((T.copies _ h).enlarges hs |>.times (he.enlarges ht)).integrable β)
    (((T.copies _ hB).enlarges hs |>.times (he.enlarges ht)).integrable β)]
  let W U := (T.copy v A U * F U) - (T.copy v B U * F U)
  have hW : Integrable W (law G n β) := (((T.copies _ h).enlarges hs |>.times (he.enlarges ht)).integrable β).sub
    (((T.copies _ hB).enlarges hs |>.times (he.enlarges ht)).integrable β)
  change moment β W = 0
  rw [← moment_pull β s⁻¹ z W hW]
  have hw (U) : (W ∘ pull s⁻¹ z) U = (if T.hand v then star (A U-B U) else A U-B U) * R U := by simp [W,R,Tiling.copy,hp,z,s,b,sub_mul,star_sub]; split <;> rfl
  by_cases hv : T.hand v
  · rw [moment]; simp_rw [hw,if_pos hv, show ∀ U, star (A U-B U) * R U = star ((A U-B U)*star (R U)) from fun U => by rw [star_mul',star_star],Complex.star_def, integral_conj];
    change (starRingEnd ℂ) (moment β (fun U => (A U-B U)*star (R U)))=0
    rw [hnull _ hr.real, map_zero]
  simp_rw [show W ∘ pull s⁻¹ z = _ from funext hw,if_neg hv]; exact hnull _ hr

lemma restore_all (h : Interior (T.chamber 0) A) (hB : Interior (T.chamber 0) B)
    (hnull : ∀ F : Config G n → ℂ, Interior (T.chamber 0)ᶜ F → moment β (fun U => (A U - B U)*F U)=0)
    (I : Finset T.Cell) :
    moment β (fun U => ∏ v∈I, T.copy v A U) = moment β (fun U => ∏ v∈I, T.copy v B U) := by
  classical
  let W (s : Finset T.Cell) U := ∏ v∈s, T.copy v B U
  let X (s : Finset T.Cell) U := ∏ v∈s, T.copy v A U
  have he (s : Finset T.Cell) : ∀ t : Finset T.Cell, Disjoint s t → moment β (fun U => X s U * W t U) = moment β (W (s∪t)) := by
    induction s using Finset.induction_on with
    | empty => intro t _; simp [X,moment]
    | insert i s hi ih =>
      intro t ht
      let D := (T.chamber i)ᶜ
      have hd : Disjoint s (insert i t) := Finset.disjoint_left.mpr fun x hx h => by rcases Finset.mem_insert.mp h with h|h; exact hi (h ▸ hx); exact Finset.disjoint_left.mp ht (Finset.mem_insert_of_mem hx) h
      have ht' : i∉t := fun h => Finset.disjoint_left.mp ht (Finset.mem_insert_self _ _) h
      have hD {v} (hv : i ≠ v) : T.chamber v ⊆ D := fun _ hx hr => hv ((T.which_chamber hr).symm.trans (T.which_chamber hx))
      have hE : Interior D (X s) := Interior.combines _ _ (fun j hj => (T.copies _ h).enlarges (hD (fun e => hi (e.symm ▸ hj))))
      have hF : Interior D (W t) := Interior.combines _ _ (fun j hj => (T.copies _ hB).enlarges (hD (fun e => ht' (e.symm ▸ hj))))
      calc
        _ = moment β (fun U => T.copy i A U * (X s U * W t U)) := by simp [X, hi,mul_assoc]
        _ = moment β (fun U => T.copy i B U * (X s U * W t U)) := one_restore T β h hB hnull i (hE.times hF)
        _ = moment β (fun U => X s U * W (insert i t) U) := by simp [W, ht',mul_left_comm]
        _ = moment β (W (insert i s ∪ t)) := by rw [ih _ hd,Finset.union_insert,Finset.insert_union]
  simpa only [Finset.union_empty, W,X,Finset.prod_empty,mul_one] using he I ∅ (Finset.disjoint_empty_right I)

lemma restore_root (h : Interior (T.chamber 0) A) (hB : Interior (T.chamber 0) B)
    (hnull : ∀ F : Config G n → ℂ, Interior (T.chamber 0)ᶜ F → moment β (fun U => (A U - B U)*F U)=0) :
    T.rootTest β A=T.rootTest β B := congr_arg (fun z : ℂ => ‖z‖ ^ (Fintype.card T.Cell : ℝ)⁻¹) (restore_all T β h hB hnull Finset.univ)

/-- Exact equality of the tested replicated roots for any finite linear combination of the
varying-link identities (e.g., difference between a T B − C and a (T−equation) B − C insert
at one chamber's shell node). Actual B needn't itself be a single primary; retain its joint
replication estimate separately. No norm budget at this lemma. -/
theorem restore_equations (h : Interior (T.chamber 0) A) (hB : Interior (T.chamber 0) B) {ι : Type*} (I : Finset ι)
    (x : ι → Site n) (d : ι → Step) (X : ι → Config G n → G.Color) (α : ι → Config G n → ℂ)
    (hX : ∀ i∈I, RegularD (X i)) (ha : ∀ i∈I, Tame (α i)) (K : ι → Set (Site n)) (hK : ∀ i∈I, LocalOn (K i) (α i))
    (hx : ∀ i∈I, x i ∈ T.chamber 0 ∧ x i ∉ K i)
    (he : ∀ U : Config G n, A U - B U = ∑ i∈I, (↑(equation β (x i) (d i) (X i) U) : ℂ) * α i U) :
    T.rootTest β A = T.rootTest β B := by
  refine restore_root T β h hB (fun F hF => ?_)
  have hG : Tame F := ⟨hF.borel, by obtain ⟨t,ht⟩ := hF.cost; exact ⟨t,(norm_nonneg (F 1)).trans (ht _),ht⟩⟩
  have hr i (hi : i ∈ I) : Tame (fun U => (equation β (x i) (d i) (X i) U : ℂ)) :=
      tame_of_continuous (Complex.continuous_ofReal.comp (equation_continuous _ _ _ (hX i hi)))
  simp_rw [moment,he,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun i hi => ((hr i hi).mul ((ha i hi).mul hG)).int _)]
  refine Finset.sum_eq_zero fun i hi => haar_nullity β (hX i hi) ((ha i hi).mul hG) (B:=K i ∪ (T.chamber 0)ᶜ) ?_ (.inl ?_)
  · intro U V hU; exact congr_arg₂ (· * ·) (hK i hi U V (fun j h₁ h₂ => hU j (.inl h₁) (.inl h₂))) (hF.localSites U V (fun j h₁ h₂ => hU j (.inr h₁) (.inr h₂)))
  simp [hx i hi |>.2,hx i hi |>.1]
end YM.StressFlux
