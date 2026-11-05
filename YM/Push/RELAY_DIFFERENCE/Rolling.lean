import YM.Bid.Craft
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.Work.H03

/-!
# Rotate the literal pre-mask comparison through the tested orders

Range (all copies) supplement. Supports go to ACTUAL images even if
wrapping. The anchor is the corresponding image anchor; account for
moving starting endpoints. Work with input and output comparing identically
labelled representations; don't appeal to continuum covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.TwoSided
open Function Set Filter MeasureTheory Wilson RG Lattice Cells Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}

section Turn
variable (s : Signed) (b : Site n)

def inherit (A : Directions G n) : Move G n :=
    (fun i => if s.flip i.2 then 0 else A (sendEdge s b i), fun i => if s.flip i.2 then -A (sendEdge s b i) else 0)

lemma negative (U : Config G n) (A : Directions G n) (t : ℝ) : pull s b (increment U (t • A)) =
    vary (pull s b U) (t • inherit s b A) := by
  funext i
  unfold inherit increment vary pull _root_.YM.Lattice.Step.read
  have h₁ : s.flip i.2 = ((posDir i.2).rotate s).neg := by simp [Lattice.Step.rotate,posDir]
  cases h:s.flip i.2 <;> simp only [Prod.smul_fst,Prod.smul_snd,h,
    Pi.smul_apply,←h₁,Bool.false_eq_true, ↓reduceIte,smul_zero, G.mat_lieExp_zero, one_mul,mul_one]
  · rfl
  rw [mul_inv_rev, smul_neg, Work.F03.exp_neg_color]; rfl

private lemma hand_deriv (u : ℝ → ℂ) (χ : Bool) : deriv (fun t : ℝ => hand χ (u t)) 0 = hand χ (deriv u 0) := by
  cases χ
  · rfl
  change deriv (fun t => star (u t)) 0 = star _
  by_cases h : DifferentiableAt ℝ u 0
  · exact h.hasDerivAt.star.deriv
  rw [deriv_zero_of_not_differentiableAt h, star_zero]
  exact deriv_zero_of_not_differentiableAt (fun ht => h (by simpa only [star_star] using ht.star))

lemma read (F : Config G n → ℂ) (χ : Bool) (A : List (Directions G n)) (U) :
    leftDerivs (oriented F χ s b) A U = hand χ (mult F (A.map (inherit s b)) (pull s b U)) := by
  induction A generalizing U with
  | nil => rfl
  | cons A p ih => simp only [leftDerivs, ih,hand_deriv,negative,List.map_cons,mult]; rfl

lemma healthy_at (t : ℝ) (F : Support n) (U : Config G n) :
    Healthy t (F.image (affine s b)) U ↔ Healthy t F (pull s b U) := by
  have he : Injective (affine s b) := fun _ _ h => s.act_injective (add_right_cancel h)
  unfold Healthy
  rw [←Work.H03.flags_send s b t U, Finset.disjoint_image he]

lemma root_move (P : BudgetPoint) (x : Site n) (A : Directions G n) (H : P.dirBound (affine s b x) A) :
    let q := inherit s b A; let t := (2:ℝ)^P.power
    quota P x t q.1 ∧ quota P x t q.2 := by
  intro q t
  have hp : 0 < t := by unfold t; positivity
  have he (i : Edge (Site n)) : separation (sendEdge s b i).1 (affine s b x) ≤ separation i.1 x + 1 := by
    have hr : separation (affine s b i.1) (affine s b x) = separation i.1 x := by simp only [affine,separation_translate,separation_signed]
    unfold sendEdge _root_.YM.Lattice.Step.used
    split
    · dsimp only
      apply (separation_triangle _ (affine s b i.1) _).trans
      let a := ((posDir i.2).rotate s).dir
      rw [hr,separation,show affine s b i.1 - step a - affine s b i.1 = -step a by abel,pdist_neg]
      rw [add_comm]; exact Nat.add_le_add_left (pdist_step a) _
    · dsimp
      exact le_trans hr.le (Nat.le_succ _)
  have hf (i : Edge (Site n)) : ‖t⁻¹ • A (sendEdge s b i)‖ ≤ P.threshold * (1+(separation i.1 x:ℝ))^P.power := by
    rw [norm_smul_of_nonneg (inv_pos.mpr hp).le]; let j := sendEdge s b i
    have hd := H j
    have hy : 1 + (separation j.1 (affine s b x):ℝ) ≤ 2*(1+(separation i.1 x:ℝ)) := by
      have hw : (separation j.1 (affine s b x):ℝ) ≤ (separation i.1 x:ℝ)+1 := by exact_mod_cast he i
      linarith only [hw, Nat.cast_nonneg (α:=ℝ) (separation i.1 x)]
    calc
      _ ≤ t⁻¹ * (P.threshold*(1+(separation j.1 (affine s b x):ℝ))^P.power) :=
        mul_le_mul_of_nonneg_left hd (inv_pos.mpr hp).le
      _ ≤ t⁻¹ * (P.threshold*(2*(1+(separation i.1 x:ℝ)))^P.power) := by
        have ht := P.threshold_pos; gcongr
      _ = _ := by rw [mul_pow]; change t⁻¹*(P.threshold*(t*_))=_; field_simp
  have ht (i : Edge (Site n)) : 0 ≤ P.threshold * (1+(separation i.1 x:ℝ))^P.power := by
    have hx := P.threshold_pos; positivity
  constructor <;> intro i <;> cases h:s.flip i.2 <;>
    simp only [Pi.smul_apply,q,inherit,h,Bool.false_eq_true, ↓reduceIte,smul_zero,norm_zero,smul_neg,norm_neg] <;>
    first | exact hf i | exact ht i

/-- Orthogonal and conjugate transports of the pre-mask bound INCLUDING
the complete orders. No p,n dependent cost. These factors may need
calendar thresholds! One charge per calling step, need to prove how to
spend on singleton extension. -/
theorem cost (P : BudgetPoint) (x : Site n) (χ : Bool) {F : Config G n → ℂ}
    {Z : Support n} {c : ℝ} (h : P.Regular Z F) (ht : P.supBounds x Z F c) :
    P.supBounds (affine s b x) (Z.image (affine s b)) (oriented F χ s b)
      ((2:ℝ)^P.order * (jump P * c)) := by
  let M := (2:ℝ)^P.power
  have hm : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hK : 0 ≤ jump P * c := mul_nonneg (show 0 ≤ M^P.order from pow_nonneg (zero_le_one.trans hm) _) ht.1
  refine ⟨mul_nonneg (by positivity) hK,fun U hu v hv he => ?_⟩
  rw [read]
  have hw : ∀ z,‖hand χ z‖=‖z‖ := by intro z; cases χ <;> simp [hand]
  rw [hw]
  let y := v.map (inherit s b)
  have hh : Healthy P.threshold Z (pull s b U) := (healthy_at ..).mp hu
  have hx : Based (pull s b U) F P.order := h.smooth _ hh
  have hy : y.length ≤ P.order := by simpa only [y,List.length_map]
  have hl := many P x hx ht hh hm [] [] y (by simp) (by simp)
    (fun i hi => by obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi; exact root_move s b P x q (he q hq)) (by simpa using hy)
  refine le_trans (by simpa only [List.map_nil,List.nil_append,y,M,jump] using hl)
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hy) hK)
end Turn
end YM.Push.RelayDifference.TwoSided
