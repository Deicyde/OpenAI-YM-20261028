import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Views

set_option warningAsError false

/-!
# Turning actual Pulse Credit and tangent on the compatible Pack vocab

Credits only at {single origin}; actual turn including χ conjugation
on signed coefficient density. No assumption of orientation invariance
of `P.W`, rather use the genuine history pushes for eval, label
permutations already supplied and positivity of P.eval. Can't turn
through transitions beyond the aligned camp. Not a proof of existence of
credit from Mute. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.View
open Function Filter MeasureTheory RG Wilson Lattice Labels Source Bid Finset Overlay
open Multi Multi.Pack Push.RelayDifference
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side}

variable (s : Signed) (b : Site n) (χ : Bool)
def whirl (D : Pulse G n) : Pulse G n :=
    (oriented D.1 χ s b, fun q => oriented (D.2 ((vehicle s b).symm q)) χ s b)


lemma hand_norm (z : ℂ) : ‖hand χ z‖ = ‖z‖ := by cases χ <;> simp [hand]

def fee (P : BudgetPoint) := 2^P.order * jump P
lemma cheap (P : BudgetPoint) : 1 ≤ fee P :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (one_le_pow₀ (by norm_num)))

lemma funds {P : BudgetPoint} {o : Site n} {D : Pulse G n} {r c κ : ℝ} (h : Credit P r κ {o} D c) :
    Credit P r κ {affine s b o} (whirl s b χ D) (fee P*c) := by
  obtain ⟨hx,hr,hk,hc,⟨i,F,hi,hH,hy,A,f,x,HT,HV,HX⟩,p,hp,H⟩ := h
  let z := affine s b o
  let w := fee P
  have hW : c ≤ w*c := le_mul_of_one_le_left hc (cheap P)
  have hw : 0 ≤ w := zero_le_one.trans (cheap P)
  refine ⟨singleton_nonempty _,hr,hk,hc.trans hW,⟨hand χ i,Push.RelayDifference.oriented F χ s b,?_,by simp,
    (hand_norm ..).le.trans (hy.trans hW),fun j => twist s b (A j),fun j => Push.RelayDifference.oriented (f j) χ s b,
    fun j => w*x j,fun j => ?_,?_,fun U => ?_⟩,p ∘ (vehicle s b).symm,?_,fun j => ?_⟩
  · simp only [whirl,Push.RelayDifference.oriented,hi]; funext U; cases χ <;> simp [Push.RelayDifference.oriented,hand]
  · refine ⟨?_,reg s b χ (HT j).2.1,mul_nonneg hw ((HT j).2.2.1),?_⟩
    · apply singleton_subset_iff.mpr; exact mem_image_of_mem (flip s b) ((HT j).1 (mem_singleton_self _))
    intro i hi; rw [mem_singleton.mp hi]; unfold w fee; simp only [mul_assoc]
    exact TwoSided.cost s b P _ χ (HT j).2.1 ((HT j).2.2.2 _ (mem_singleton_self _))
  · have he (X : Support n) : burn P r (twist s b X) ≤ burn P r X := by
      unfold burn; apply Real.exp_monotone; gcongr; exacts [(add_pos_of_pos_of_nonneg P.exponent_pos hr).le,bills s b _ _]
    apply lower_budget (scale_budget hw HV) le_rfl (fun j => mul_nonneg (burn_pos ..).le (mul_nonneg hw ((HT j).2.2.1)))
    intro j; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (he _) ((HT j).2.2.1)) hw
  · simp_rw [show ∀ j,masked P.threshold (twist s b (A j)) (Push.RelayDifference.oriented (f j) χ s b) U=_ from
      fun j => congr_fun (masks s b (f j) P.threshold _ χ).symm U,Push.RelayDifference.oriented, HX]
    cases χ
    · rfl
    simp only [hand, ite_true]; exact tsum_star
  · rw [← (vehicle s b).sum_comp]; simp only [comp_apply,Equiv.symm_apply_apply]
    refine le_trans (le_trans (sum_le_sum fun j _ => ?_) hp) ?_
    · change burn P r (twist s b j.zone)*_ ≤ _
      unfold burn; gcongr; exacts [(H _).2.2.1,(add_pos_of_pos_of_nonneg P.exponent_pos hr).le,bills s b _ _]
    exact mul_le_mul_of_nonneg_left hW hk.le
    simp
  obtain ⟨j,rfl⟩ := (vehicle s b).surjective j
  unfold whirl; simp only [comp_apply,Equiv.symm_apply_apply]
  refine ⟨notice s b (H _).1 χ,fun hn => ?_,(H _).2.2.1,fun U => (hand_norm χ _).le.trans ((H _).2.2.2 _)⟩
  apply singleton_subset_iff.mpr; refine mem_image_of_mem (flip s b) ((H _).2.1 (fun hh => hn ?_) (mem_singleton_self _))
  funext U; rw [hh]; cases χ <;> simp [Push.RelayDifference.oriented,hand]











end YM.MultiNext.SignedSource.View
