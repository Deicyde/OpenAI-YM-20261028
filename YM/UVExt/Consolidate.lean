import YM.UVExt.AlmostTail

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Laurent Lattice Wilson RG
open scoped Classical BigOperators Topology ContDiff
variable {ν ν' ι α β γ : Type*} {F : Filter ι} [F.NeBot] {σ C C' : ℝ} {L : α→ℝ} {L' : β→ℝ} {a : α→ℝ} {s : α→β} {b : β→ℝ}

def pool (a : α→ℝ) (s : α→β) (x : β) := ∑' (i : {i // s i=x}), a i

lemma pool_money (h : Carries C σ L a) (hσ : 0 < σ) (hL : ∀ i, L' (s i) ≤ L i) (hx : ∀ i, 0 ≤ L' i) :
    Carries C σ L' (pool a s) := by
  have hc := h.paid
  let V (x) := ∑' (i : {i : α // s i=x}), Real.exp (σ*L i.val)*‖a i.val‖
  have hV : HasSum V (∑' i, Real.exp (σ*L i)*‖a i‖) := hc.2.1.hasSum.tsum_fiberwise s
  refine ⟨hx,fun t => (le_trans ?_ ((Summable.sum_le_tsum t (fun _ _=>by unfold V; positivity) hV.summable).trans (hV.tsum_eq.trans_le hc.2.2)))⟩
  refine Finset.sum_le_sum fun x hx=> ?_
  have ha : Summable (‖a ·‖) := Summable.of_nonneg_of_le (fun _=>by positivity) (fun i=> le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hσ.le (h.1 _)))) hc.2.1
  apply le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (ha.subtype (s · = x))) (by positivity : 0 ≤ Real.exp (σ*L' x))) _
  rw [← tsum_mul_left]; unfold V
  refine Summable.tsum_le_tsum (fun i => by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show L' x ≤ _ by convert hL i.val using 1; exact congr_arg L' i.property.symm) hσ.le)) (norm_nonneg _)) ((ha.subtype (s ·=x)).mul_left _) (hc.2.1.subtype (s ·=x))

section matrix
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
lemma pool_read (f : α→ℝ) (v : β→Y) (s : α→β) (hg : Summable f) (h : Summable (fun i => f i • v (s i))) : HasSum (fun j => pool f s j • v j) (∑' i, f i • v (s i)) := by
  suffices ∀ j, pool f s j • v j=∑' (i:{i//s i=j}), f i • v (s i) from (Eq.mp (congr_arg (fun z => HasSum z (∑' i, f i • v (s i))) ((funext this).symm)) (h.hasSum.tsum_fiberwise s))
  intro j; unfold pool; refine Eq.trans (Eq.symm ((hg.subtype (s ·=j)).tsum_smul_const (v j))) ?_
  apply tsum_congr; intro i; rw [i.property]; rfl
end matrix

lemma squared_money (h : Carries C σ L a) (h' : Carries C' σ L' b) (h0 : 0 ≤ C) :
    Carries (C*C') σ (fun i : α×β=> L i.1+L' i.2) (fun i => a i.1*b i.2) := by
  let A i := Real.exp (σ*L i)*‖a i‖; let B i := Real.exp (σ*L' i)*‖b i‖
  have hA := h.paid.2.1.norm; have hB := h'.paid.2.1.norm
  refine ⟨fun i=> add_nonneg (h.1 _) (h'.1 _),fun s => ?_⟩
  calc
    _ = ∑ i∈s, A i.1*B i.2 := Finset.sum_congr rfl fun i _=> by simp only [A,B, mul_add,Real.exp_add, norm_mul]; ring
    _ ≤ ∑' i:α×β, A i.1*B i.2 := Summable.sum_le_tsum s (fun _ _=>by unfold A B; positivity) (summable_mul_of_summable_norm hA hB)
    _ = (∑' i, A i)*(∑' i,B i) := (tsum_mul_tsum_of_summable_norm hA hB).symm
    _ ≤ C*C' := mul_le_mul h.paid.2.2 h'.paid.2.2 (tsum_nonneg fun _=>by unfold B; positivity) h0 -- ? result elaboration

lemma product_money {R : ν→ν'→ℝ} [Fintype ν'] (W : ν→ℝ) (hW : ∀ i, 0 ≤ W i) (K : ν→ℝ) (hK : ∀ i, ∑ j, |R i j| = K i) (ht : SumBudget (fun i=> K i * Real.exp (σ*W i)) C) :
    Carries C σ (fun i : ν×ν' => W i.1) (fun i => R i.1 i.2) := by
  let H (i : ν×ν') := Real.exp (σ*W i.1)*‖R i.1 i.2‖
  have h i : ∑' j, H (i,j)=K i * Real.exp (σ*W i) := by unfold H; rw [tsum_fintype, ← hK,Finset.sum_mul]; simp_rw [Real.norm_eq_abs]; apply Finset.sum_congr rfl fun j _=>mul_comm _ _
  have hs := summable_prod_of_nonneg (f:=H) (fun i => by unfold H; positivity) |>.mpr ?_
  · refine ⟨fun i=> hW _,fun q=>le_trans (Summable.sum_le_tsum (f:=H) q (fun j _=>by unfold H; positivity) hs) ?_⟩
    rw [hs.tsum_prod]; simp_rw [h]; exact ht.2.2
  exact ⟨fun _=> Summable.of_finite,by simp_rw [h]; exact ht.2.1⟩

lemma proper_wallet [Finite α] : True := trivial
end YM.UVExt.Paths
