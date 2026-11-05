import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Quartet
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Clinic
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Museum


/-!
# Taper the actual guarded principal path sensitivities

Absorb the errors as one `Sized` argument EACH (incl. zeroth) with a
Z-dependent price, preserving the small-component pre-L cost in the
ordered pullback. No smooth strengthening of the E fees and no Taylor
comparison of the kth derivative between different chart positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations
    Exterior Bloch Bid MultiNext.SignedSource MultiNext.SignedSource.Banjo WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f}
    {Q C M r x y : ℝ} {j l n : ℕ} {A : Slab G c l} {w : Directions G f}

variable (hh : Matins T F B.power (2*C) M) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C)
    (ht : temp x ≤ 2*B.threshold) (hP : P.threshold=temp x) (hB : P.power ≤ B.power) (hC : 1 ≤ C) (hl : l ≤ n)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (A i)) (hu : loom P (reach x) C ≤ 1)
include hq ht hP hB hC hl h hu
lemma launch_cost (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) :
    Limb B.power (S.ratio.parent o) (iteratedFDeriv ℝ j (launch V (S.ratio.parent o) (reach x) g A) 0 v) (2*C*B.threshold) := by
  have ht : C*P.threshold ≤ 2*C*B.threshold := by rw [hP]; nlinarith only [mul_le_mul_of_nonneg_left ht (zero_le_one.trans hC)]
  intro i; apply le_trans (b:=C*P.threshold*spine B.power i.1 (S.ratio.parent o)) ?_ (mul_le_mul_of_nonneg_right ht (spine_pos ..).le)
  by_cases he : j=0
  · subst j; rw [iteratedFDeriv_zero_apply,launch_zero]; exact hq.visible hC hB i
  exact hq.individual h hC hl hj (by omega) v hv hB (Or.inr ⟨rfl,le_trans (by
    apply mul_le_mul_of_nonneg_right (le_mul_of_one_le_left P.threshold_pos.le hC) (by positivity)) hu⟩) i

def tranche (L : Side) (n : ℕ) (Q v w t : ℝ) := ((clinicFee n Q*v^2+w)/t)*(L.val:ℝ)^3
omit hq ht hP hB hC hl h hu in
lemma tranche_nn (L : Side) (n : ℕ) {Q v w t : ℝ} (hQ : 0≤Q) (hw : 0≤w) (ht : 0≤t) : 0≤tranche L n Q v w t := by unfold tranche; positivity [le_trans (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hQ) (clinicFee_le n hQ)]

variable (hT : Act T F x k n r Q) (hQ : 1≤Q) (hM : 1 ≤ M) (hn : 2 ≤ n) (hr : loom P (reach x) C ≤ r)
    (hw : ‖w‖ ≤ loom P (reach x) C) (hw' : ‖w‖ ≤ y)
include hh hT hQ hM hn hr hw hw'

lemma first_promise (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) :
    let a := enters V (S.ratio.parent o) (reach x) g A w
    let K := M+tranche S.patch.L n Q (loom P (reach x) C) y B.threshold
    Promise 2 K ((S.patch.L.val:ℝ)⁻¹) B o X (iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v) := by
  intro a K; let L := (S.patch.L.val:ℝ); let s := loom P (reach x) C; let Z := tranche S.patch.L n Q s y B.threshold
  have h0 : 0≤y := (norm_nonneg _).trans hw'; have hZ : 0≤Z := tranche_nn _ _ (by positivity) h0 B.threshold_pos.le
  let z' := launch V (S.ratio.parent o) (reach x) g A
  let z := iteratedFDeriv ℝ j z' 0 v
  have hp := hh.taper B X o z rfl (launch_cost hq ht hP hB hC hl h hu hj v hv)
  refine Quartet.sweet (M:=K) (Y:=Z) (by positivity) hZ le_rfl (by positivity) hp ⟨by positivity,fun i => ?_⟩
  have hfee := (timesEnter hq hT hP hn h hC hl hQ hu hr hw true).2 j hj v hv
  rw [spine_self,one_pow,mul_one] at hfee
  let b := iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v
  let a₀ := mainStroke T F true (iteratedFDeriv ℝ j a 0 v)
  have h : ‖a₀-route T z‖ ≤ y := by
    by_cases he : j=0
    · subst j; unfold a₀ z; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; change ‖(route T (z' 0)+w)-route T (z' 0)‖ ≤ _; simpa only [add_sub_cancel_left] using hw'
    unfold a₀ a; rw [enter_pos hq hj (by omega) v]; change ‖(route T z+0)-route T z‖ ≤ _; simpa
  have h := ((norm_sub_le_norm_sub_add_norm_sub b a₀ (route T z)).trans (add_le_add hfee h))
  have hL : L ≠ 0 := by unfold L; positivity
  change ‖(b-route T z) i‖ ≤ Z*L⁻¹^3* _
  apply ((norm_le_pi_norm ..).trans h).trans
  have he := B.threshold_pos.ne'
  calc
    _ = Z * L⁻¹^3 * B.threshold := by unfold Z L tranche s; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power i.1 o)) (by positivity)
end YM.PhysicalNext.JointLoad.Heir
