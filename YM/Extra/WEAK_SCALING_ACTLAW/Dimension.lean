import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five


/-! # Free dimension criterion for birth of a physical stress -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Dimension
open Set Function Filter Table Climb Org Cube Work.A01 Types Color
variable {G : Gauge} {L : Register G} {v : Pairs (Bel L)} {H : (Bel L).RealSpin} (h : Types H v)

include h in
private lemma cov (s : Signed) (i j : Axis) : (Bel L).mirror H 4 s (contracted v i j) =
    (eps s i * eps s j) • contracted v (s.perm i) (s.perm j) := by
  rw [contracted,map_sum,contracted,Finset.smul_sum,← Equiv.sum_comp s.perm (fun k => (eps s i * eps s j) • v (s.perm i) k (s.perm j) k)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h.action]; congr 1
  nlinarith only [congrArg (fun z : ℝ => eps s i * eps s j * z) (eps_self s a)]

include h in
private lemma invariant (s : Signed) : (Bel L).mirror H 4 s (total v) = total v := by
  change (Bel L).mirror H 4 s (∑ i, contracted v i i) = _
  simp_rw [map_sum,cov h,eps_self,one_smul, Equiv.sum_comp s.perm (fun i => contracted v i i)]; rfl

include h in
theorem members : A v ∈ meanFree H ∧ B v ∈ meanFree H ∧ Types.C v ∈ meanFree H := by
  let X : (Bel L).Stress := fun a b => contracted v a b
  let t := total v
  let y := Work.A15.front (n:=0) 0 (Fin.elim0 (α:=(Bel L).Tag)) 4
  have ht : X ∈ meanFree H := by
    refine ⟨⟨fun a b => Finset.sum_congr rfl (fun i _ => h.exchange a i b i), fun a b => by simp [X,contracted,h.real], ?_⟩,
      funext fun a => funext fun b => ?_⟩
    · intro s a b; rw [show (Bel L).mirror H 4 s (X a b) = _ from cov h s a b]; simp_rw [Complex.ofReal_mul, mul_smul,
        ← Finset.smul_sum,eps_column, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
    change y (contracted v a b) = 0; simp only [y,contracted,_root_.map_sum,h.mean, Finset.sum_const_zero]
  have he (P : (Bel L).Stress) : RawTensor H P ↔ ∀ s a b, (Bel L).mirror H 4 s (P a b) =
      ((↑(eps s a * eps s b) : ℂ)) • P (s.perm a) (s.perm b) := by
    unfold RawTensor; simp_rw [Complex.ofReal_mul,mul_smul,← Finset.smul_sum,eps_column]
  have h' : A v ∈ meanFree H := by
    refine ⟨⟨fun a b => ?_,fun a b => ?_,he _ |>.mpr fun s a b => ?_⟩,funext fun a => funext fun b => ?_⟩
    · by_cases h : a=b <;> simp [A,h,eq_comm (a:=b)]
    · by_cases t : a=b <;> simp [A,t,contracted,h.real]
    · by_cases t : a=b <;> simp [t,A,cov h, eps_self]
    change y (A v a b) = 0; by_cases t:a=b <;> simp [y,A,t,contracted,h.mean]
  have ho : (fun a b => if a=b then t else 0) ∈ meanFree H := by
    refine ⟨⟨fun a b => ?_,fun a b => ?_,he _ |>.mpr fun s a b => ?_⟩, funext fun a => funext fun b => ?_⟩
    · simp [eq_comm]
    · by_cases e : a=b <;> simp [e,t,total,h.real]
    · by_cases e : a=b <;> simp [e,t,invariant h,eps_self]
    change y (if a=b then t else 0) = 0; by_cases e : a=b <;> simp [e,y,t,total,h.mean]
  have hb : B v = (2:ℝ)⁻¹ • (fun a b => if a=b then t else 0) - A v := by ext1 i; ext1 j; by_cases h:i=j <;> simp [A,B,t,h]
  have hc : Types.C v = X - A v := by ext1 i; ext1 j; by_cases h:i=j <;> simp [Types.C,A,X,h]
  exact ⟨h',hb ▸ (meanFree H).sub_mem ((meanFree H).smul_mem _ ho) h',hc ▸ (meanFree H).sub_mem ht h'⟩


lemma rank_meanFree (hG : G.Simple) (H : (Bel L).Hierarchy) : 3 ≤ Module.finrank ℝ (meanFree H.spin) := by
  obtain ⟨hA,hB,hC⟩ := members (pairing_types L hG H)
  let v := pinned L
  let P : Fin 3 → meanFree H.spin := ![⟨A v,hA⟩,⟨B v,hB⟩,⟨Types.C v,hC⟩]
  let X : (Fin 3 → ℝ) →ₗ[ℝ] meanFree H.spin := ∑ i, (LinearMap.proj (R:=ℝ) i).smulRight (P i)
  have hi : Injective X := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro a ha
    have he := congrArg Subtype.val ha
    unfold X at he; rw [LinearMap.sum_apply, Fin.sum_univ_three] at he
    obtain ⟨h₁,h₂,h₃⟩ := tensor_detection hG L (a 0) (a 1) (a 2) he
    have h (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := (by decide : ∀ i : Fin 3, i=0 ∨ i=1 ∨ i=2) i
    funext i; rcases h i with h|h|h <;> simp [h,h₁,h₂,h₃]))
  exact (Module.finrank_fin_fun ..).symm.trans_le (LinearMap.finrank_le_finrank_of_injective hi)

lemma space (hG : G.Simple) (H : (Bel L).Hierarchy) : Module.finrank ℝ (polar H.spin) < Module.finrank ℝ (meanFree H.spin) :=
    lt_of_le_of_lt (Five.rank_polar hG H.spin) (rank_meanFree hG H)
end YM.Extra.WeakScaling.Dimension
