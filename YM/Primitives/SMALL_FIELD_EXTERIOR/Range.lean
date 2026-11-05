import YM.Primitives.SMALL_FIELD_EXTERIOR.Flat
import YM.Primitives.SMALL_FIELD_EXTERIOR.Scroll


/-!
# Approximate range of the generator

Method of continuity, done directly in finite error norms. No claim of C^k
solution of elliptic PDE on corners; no density or BL estimate assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V u f : Points ι → ℝ} {r ε : ℝ}

private lemma finer (hV : Regular r 2 V) (h : ∀ f : Points ι → ℝ, ContinuousOn f (cube ι r) →
    ∃ u, Neumann r u ∧ ∃ c : ℝ, size r 0 (f-(elliptic V u+(fun _ => c))) ≤ (1/2) * size r 0 f) : Approximate r V := by
  intro f hf ε he
  let A : ℝ := 1/2
  let C := size r 0 f
  have ht (n : ℕ) : ∃ u, Neumann r u ∧ ∃ c : ℝ, size r 0 (f-(elliptic V u+(fun _ => c))) ≤ A^n*C := by
    induction n with
    | zero =>
      refine ⟨0,Neumann.const 0,0,?_⟩; rw [elliptic_zero,show (fun _ : Points ι => (0:ℝ))=0 from rfl]; simp [C]
    | succ n ih =>
      obtain ⟨u,hu,c,hc⟩ := ih
      let g : Points ι → ℝ := f-(elliptic V u+(fun _ => c))
      obtain ⟨v,hv,d,hd⟩ := h g (hf.sub (((hu.elliptic1 hV).cOn).add continuousOn_const))
      refine ⟨u+v,hu.add hv,c+d,?_⟩
      rw [show f-(elliptic V (u+v)+(fun _ => c+d))=g-(elliptic V v+(fun _ => d)) by
        unfold g; rw [elliptic_add V hu hv]; ext; simp; ring]
      exact hd.trans ((mul_le_mul_of_nonneg_left hc (by norm_num : 0 ≤ A)).trans_eq (by rw [pow_succ']; ring))
  have hT : Tendsto (fun n : ℕ => A^n*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ A by unfold A; norm_num) (by unfold A; norm_num)).mul_const C)
  obtain ⟨j,hj⟩ := (hT.eventually (gt_mem_nhds he)).exists
  obtain ⟨u,hu,c,hc⟩ := ht j
  exact ⟨u,hu,c,hc.trans (show A^j*C < ε from hj).le⟩

private lemma turning (hr : 0 < r) (hV : Regular r 2 V) (hh : Charged r V 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t∈Icc (0:ℝ) 1, Approximate r (t • V) → ∀ s : ℝ, |t-s| ≤ C → Approximate r (s • V) := by
  obtain ⟨K,hk,h⟩ := advance_rate hr hV hh
  let C := 1/(8*K)
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C,hC,fun t ht ha s hs => finer (hV.smul s) ?_⟩
  intro f hf
  let m := size r 0 f
  rcases eq_or_lt_of_le (size_nn r 0 f) with he|he
  · refine ⟨0,Neumann.const 0,0,?_⟩; rw [elliptic_zero,show (fun _ : Points ι => (0:ℝ))=0 from rfl]; simp [← he]
  change 0 < m at he
  obtain ⟨u,hu,c,hc⟩ := ha f hf (m/4) (by positivity)
  let L : Points ι → ℝ := elliptic (t • V) u + (fun _ => c)
  let H : Points ι → ℝ := elliptic (s • V) u + (fun _ => c)
  have hL : ContinuousOn L (cube ι r) := (hu.elliptic1 (hV.smul t)).cOn.add continuousOn_const
  have hH : ContinuousOn H (cube ι r) := (hu.elliptic1 (hV.smul s)).cOn.add continuousOn_const
  have hp : size r 0 L ≤ 2*m := (deficit (V:=0) continuousOn_const hL hf).trans (by
    change m+size r 0 (f-L) ≤ _
    change size r 0 (f-L) ≤ _ at hc; linarith)
  refine ⟨u,hu,c,?_⟩
  have hi : size r 0 (L-H)=|t-s| * size r 0 (drift V u) := by
    unfold L H
    rw [add_sub_add_right_eq_sub,size_congr 0 (under_drift hV u s t), size_smul]
  calc
    size r 0 (f-H) = size r 0 ((f-L)+(L-H)) := by rw [sub_add_sub_cancel]
    _ ≤ size r 0 (f-L) + size r 0 (L-H) := size_add continuousOn_const (hf.sub hL) (hL.sub hH)
    _ ≤ m/4 + C*(K * (2*m)) := by
      rw [hi]; exact add_le_add hc (mul_le_mul hs ((h u hu t ht c).trans (mul_le_mul_of_nonneg_left hp hk.le)) (size_nn ..) hC.le)
    _ = _ := by change m/4 + C*(K*(2*m)) = (1/2)*m; unfold C; field_simp; ring

theorem approximated (hr : 0 < r) (hV : Regular r 2 V) (hh : Charged r V 0) : Approximate r V := by
  obtain ⟨C,hc,h⟩ := turning hr hV hh
  obtain ⟨N,hN⟩ := exists_nat_gt (1/C)
  have hn : (0:ℝ)<N := (one_div_pos.mpr hc).trans hN
  let t (i : ℕ) := (i:ℝ)/N
  have he i (hi : i ≤ N) : Approximate r (t i • V) := by
    induction i with
    | zero => simp [t,approximate_flat hr]
    | succ i ih =>
      have hz : i≤N := by omega
      apply h (t i) ⟨by unfold t; positivity, (div_le_one hn).mpr (by exact_mod_cast hz)⟩ (ih hz) _
      have hw : t i-t (i+1)= -(1/(N:ℝ)) := by unfold t; push_cast; ring
      rw [hw,abs_neg,abs_of_nonneg (by positivity), div_le_iff₀ hn]
      rw [mul_comm]; exact ((div_lt_iff₀ hc).mp hN).le
  simpa [t,div_self hn.ne'] using he N le_rfl

/-- Enough to invert against any continuous test of mean zero on the BOX. -/
theorem range_zero (hr : 0 < r) (hV : Regular r 2 V) (hh : Charged r V 0)
    (hf : ContinuousOn f (cube ι r)) (h : raw r V f=0) (he : 0 < ε) :
    ∃ u, Neumann r u ∧ size r V (f-elliptic V u) ≤ ε := by
  obtain ⟨K,hk⟩ := glide hr hV.cOn
  have hK := hk.pos
  obtain ⟨u,hu,c,hc⟩ := approximated hr hV hh f hf (ε/K) (by positivity)
  refine ⟨u,hu,?_⟩
  let L := elliptic V u; let C : Points ι → ℝ := fun _ => -c
  let D := f-L+C
  have hi : ContinuousOn L (cube ι r) := (hu.elliptic1 hV).cOn
  have hD : D=f-(elliptic V u+(fun _ => c)) := by unfold D C L; ext; simp; ring
  have hg : bracket r V (f-L) C=0 := by
    have hx : C=(-c) • (1:Points ι → ℝ) := by ext; simp [C]
    have hv : bracket r V L C=0 := hu.mean_zero hr.le hV _
    rw [bracket_sub hV.cOn hf hi continuousOn_const,hv]; change bracket r V f C - 0 = 0
    rw [hx,bracket_sym r V f,bracket_smul,bracket]
    rw [one_mul,h,mul_zero,sub_zero]
  have hj : size r V D ≤ K * size r 0 D := by
    simpa only [one_smul] using hk.down 1 ⟨zero_le_one,le_rfl⟩ D ((hf.sub hi).add continuousOn_const)
  calc
    _ ≤ size r V D := pythagoras hV.cOn (hf.sub hi) continuousOn_const hg
    _ ≤ _ := hj.trans (by rw [hD]; exact (mul_le_mul_of_nonneg_left hc hK.le).trans_eq (by field_simp))
end YM.Primitives.SmallFieldExterior
