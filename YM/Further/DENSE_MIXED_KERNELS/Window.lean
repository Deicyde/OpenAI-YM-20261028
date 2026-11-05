import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic





/-!
# Differentiating mixed kernels on open patches

A *domination*, not a budget. Fixed-volume, no arithmetic cost. In particular
it is useful with coordinate norms on the full chart, without budgeting those
integrals via chart Fréchet norms which could carry enormous volume factors.
Allows arbitrary finite-order smooth integrands, not just analytic or compactly
supported ones, and no continuity in the hard (integrated) arguments. Will be
used BEFORE taking output mask, and applies also with unhealthy fields in the
neighborhood; bounds only on Healthy are not enough.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter MeasureTheory Function Set
open scoped NNReal ENNReal Topology BigOperators ContDiff Classical

universe u
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Open-neighborhood, ordinary coordinate norm domination. -/
structure District (μ : Measure Ω) (k : ℕ) (s : Set E) (f : Ω → E → F) : Prop where
  territory : IsOpen s
  smooth i : ContDiffOn ℝ k (f i) s
  meas : ∀ x∈s,AEStronglyMeasurable (fun i => f i x) μ
  holds : ∃ b : Ω → ℝ, Integrable b μ ∧ ∀ i,∀ x∈s,∀ j, j ≤ k → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ b i

def Window (μ : Measure Ω) (k : ℕ) (x : E) (f : Ω → E → F) := ∃ s, x∈s ∧ District μ k s f

variable {D : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {s : Set E} {x : E} {k : ℕ} {f g : Ω → E → F}

namespace District
include E
omit [FiniteDimensional ℝ E] in
theorem beneath (h : District μ k s f) {t} (ht : t ⊆ s) (ho : IsOpen t) : District μ k t f :=
  ⟨ho,fun i => (h.smooth i).mono ht, fun _ hy => h.meas _ (ht hy), by
    obtain ⟨b,hb,hb'⟩ := h.holds; exact ⟨b,hb,fun _ _ hy => hb' _ _ (ht hy)⟩⟩

omit [FiniteDimensional ℝ E] in
theorem reads (h : District μ k s f) (he : x∈s) : Integrable (fun i => f i x) μ := by
  obtain ⟨b,hb,hh⟩ := h.holds
  exact hb.mono' (h.meas _ he) (Eventually.of_forall fun i => by
    simpa only [norm_iteratedFDeriv_zero] using hh i x he 0 (Nat.zero_le _))

-- Allows AES, no joint measurability demanded beyond the hard-point integral uses.
private lemma flies (h : District μ (k+1) s f) (hv : x∈s) : AEStronglyMeasurable (fun i => fderiv ℝ (f i) x) μ := by
  have he (v : E) : AEStronglyMeasurable (fun i => fderiv ℝ (f i) x v) μ := by
    let T (r : ℝ) (i : Ω) := if x+r • v∈s then r⁻¹ • (f i (x+r • v)-f i x) else 0
    have ht r : AEStronglyMeasurable (T r) μ := by
      unfold T; split_ifs with hm
      · exact ((h.meas _ hm).sub (h.meas _ hv)).const_smul _
      exact aestronglyMeasurable_const
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] 0) ht
    have hx : Tendsto (fun r : ℝ => x+r • v) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using (show Continuous (fun r : ℝ=>x+r • v) from by fun_prop).tendsto 0
    refine Eventually.of_forall fun i => ?_
    have hf := (((h.territory.contDiffOn_iff.mp (h.smooth i) hv).differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero
    refine hf.congr' ?_
    filter_upwards [hx.mono_left nhdsWithin_le_nhds |>.eventually (h.territory.mem_nhds hv)] with r hr using (eq_comm.mp (if_pos hr))
  let B := Module.finBasis ℝ E
  let R (j) := ContinuousLinearMap.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (B.coord j))
  have hm (j) : AEStronglyMeasurable (fun i => R j (fderiv ℝ (f i) x (B j))) μ :=
    (R j).continuous.comp_aestronglyMeasurable (he (B j))
  refine (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hm i)).congr (Eventually.of_forall fun i => ?_)
  apply ContinuousLinearMap.ext; intro v
  rw [Finset.sum_apply,_root_.sum_apply]
  change (∑ j,B.repr v j • fderiv ℝ (f i) x (B j)) = _
  simp only [← map_smul, ← map_sum,B.sum_repr]

lemma lower (h : District μ (k+1) s f) : District μ k s (fun i => fderiv ℝ (f i)) := by
  obtain ⟨b,hb,hb'⟩ := h.holds
  refine ⟨h.territory,fun i => (h.smooth i).fderiv_of_isOpen h.territory (by simp),fun _ => flies h,
    b,hb,fun i x hx j hj => ?_⟩
  simpa only [iteratedFDeriv_succ_eq_comp_right,comp_apply,LinearIsometryEquiv.norm_map] using
    hb' i x hx (j+1) (by omega)

theorem switches (h : District μ (k+1) s f) (he : x∈s) : HasFDerivAt (fun Z => ∫ i,f i Z ∂μ)
    (∫ i,fderiv ℝ (f i) x ∂μ) x := by
  obtain ⟨b,hb,hh⟩ := h.lower.holds
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun y i => fderiv ℝ (f i) y)
    (h.territory.mem_nhds he) (Eventually.mono (h.territory.mem_nhds he) (fun _ hy => h.meas _ hy))
    (h.reads he) (h.lower.meas _ he) (Eventually.of_forall fun i x hx => by
      simpa only [norm_iteratedFDeriv_zero] using hh i x hx 0 (Nat.zero_le _)) hb
    (Eventually.of_forall fun i y hy => ((h.territory.contDiffOn_iff.mp (h.smooth i) hy).differentiableAt (by simp)).hasFDerivAt)

-- Costs stated for complete range in applications. Use fixed universe for induction.
theorem integrate (h : District μ k s f) : ContDiffOn ℝ k (fun x => ∫ i,f i x ∂μ) s := by
  induction k generalizing F with
  | zero =>
    obtain ⟨b,hb,hh⟩ := h.holds
    refine contDiffOn_zero.mpr fun x hx => ContinuousAt.continuousWithinAt ?_
    have he : ∀ᶠ y in 𝓝 x, y∈s := h.territory.mem_nhds hx
    apply continuousAt_of_dominated (F:=fun x i => f i x) (he.mono (fun y hy => h.meas y hy)) ?_ hb
      (Eventually.of_forall fun i => (h.territory.contDiffOn_iff.mp (h.smooth i) hx).continuousAt)
    exact he.mono (fun y hy => Eventually.of_forall fun i => by simpa only [norm_iteratedFDeriv_zero] using hh i y hy 0 le_rfl)
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen h.territory]
    exact ⟨fun x hx => (h.switches hx).differentiableAt.differentiableWithinAt, fun h => by simp at h,
      (ih h.lower).congr (fun _ hx => (h.switches hx).fderiv)⟩

end District

namespace Window

omit [FiniteDimensional ℝ E] in
theorem oft (h : Window μ k x f) : ∀ᶠ v in 𝓝 x, Window μ k v f := by
  obtain ⟨s,hx,h⟩ := h; filter_upwards [h.territory.mem_nhds hx] with i hi using ⟨s,hi,h⟩

theorem lower (h : Window μ (k+1) x f) : Window μ k x (fun i => fderiv ℝ (f i)) := by
  obtain ⟨S,hS,h⟩ := h; exact ⟨S,hS,h.lower⟩

omit [FiniteDimensional ℝ E] in
theorem of_le (h : Window μ k x f) {j : ℕ} (hj : j ≤ k) : Window μ j x f := by
  obtain ⟨S,hS,h⟩ := h
  obtain ⟨b,hb,hb'⟩ := h.holds
  exact ⟨S,hS,h.territory,fun i => (h.smooth i).of_le (Nat.cast_le.mpr hj),h.meas,b,hb,
    fun i z hz l hl => hb' i z hz l (hl.trans hj)⟩

omit [FiniteDimensional ℝ E] in
theorem pad_constant (h : Window μ k x f) (T : F →L[ℝ] D) : Window μ k x (fun i Z => T (f i Z)) := by
  obtain ⟨S,hS,h⟩ := h
  obtain ⟨b,hb,hb'⟩ := h.holds
  refine ⟨S,hS,h.territory,fun i => T.contDiff.comp_contDiffOn (h.smooth i),
    fun y hy => T.continuous.comp_aestronglyMeasurable (h.meas y hy),fun i => ‖T‖ * b i,hb.const_mul _,
    fun i z hz l hl => ?_⟩
  exact (T.norm_iteratedFDeriv_comp_left (h.territory.contDiffOn_iff.mp (h.smooth i) hz) (Nat.cast_le.mpr hl)).trans
    (mul_le_mul_of_nonneg_left (hb' i z hz l hl) (norm_nonneg _))

omit [FiniteDimensional ℝ E] in
lemma eq (h : Window μ k x f) (hl : ∀ᶠ v in 𝓝 x,∀ i, g i v=f i v) : Window μ k x g := by
  obtain ⟨S,hS,h⟩ := h
  obtain ⟨s,hs,hs',hx⟩ := mem_nhds_iff.mp (Eventually.and (show ∀ᶠ y in 𝓝 x, y ∈ S from h.territory.mem_nhds hS) hl)
  have he x (hx : x∈s) : ∀ i,g i x=f i x := (hs hx).2
  obtain ⟨b,hb,hb'⟩ := h.holds
  refine ⟨s,hx,hs',fun i => ((h.smooth i).mono (fun x hz => (hs hz).1)).congr (fun y hy => he y hy i),
    fun y hy => ?_,b,hb,fun i z hz l hl => ?_⟩
  · simpa only [he y hy] using! h.meas y (hs hy).1
  have hev : g i =ᶠ[𝓝 z] f i := mem_of_superset (hs'.mem_nhds hz) fun z hz => he z hz i
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds]; exact hb' i z (hs hz).1 l hl

omit [FiniteDimensional ℝ E] in
theorem reads (h : Window μ k x f) : Integrable (fun i => f i x) μ := by
  obtain ⟨S,hS,h⟩ := h; exact h.reads hS

omit [FiniteDimensional ℝ E] in
lemma near (h : Window μ k x f) : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ k (f i) y := by
  obtain ⟨S,hS,h⟩ := h; refine Eventually.mono (p:=fun y => y∈S) (h.territory.mem_nhds hS) fun z hz i =>
    h.territory.contDiffOn_iff.mp (h.smooth i) hz

omit [FiniteDimensional ℝ E] in
theorem smooth (h : Window μ k x f) (i) : ContDiffAt ℝ k (f i) x := h.near.self_of_nhds i

theorem switches (h : Window μ (k+1) x f) : HasFDerivAt (fun Z => ∫ i,f i Z ∂μ)
    (∫ i,fderiv ℝ (f i) x ∂μ) x := by
  obtain ⟨S,hS,h⟩ := h; exact h.switches hS

theorem integrate (h : Window μ k x f) : ContDiffAt ℝ k (fun x => ∫ i,f i x ∂μ) x := by
  obtain ⟨S,hS,h⟩ := h; exact h.integrate.contDiffAt (h.territory.mem_nhds hS)

omit [FiniteDimensional ℝ E] in
theorem comp {d : D} {T : D → E} (h : Window μ k (T d) f) (he : ContDiffAt ℝ k T d) : Window μ k d (fun i => f i ∘ T) := by
  obtain ⟨S,hS,h⟩ := h
  obtain ⟨b,hb,hb'⟩ := h.holds
  let L := Finset.range (k+1)
  let l := 1 + ∑ j∈L,‖iteratedFDeriv ℝ j T d‖
  have hi : 1 ≤ l := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hh : ∀ j∈L,∀ᶠ e in 𝓝 d,‖iteratedFDeriv ℝ j T e‖ ≤ l := by
    intro j hj
    have hv := he.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    exact hv.norm (ge_mem_nhds (lt_of_le_of_lt (Finset.single_le_sum (f:=fun i => ‖iteratedFDeriv ℝ i T d‖)
      (fun j _ => norm_nonneg _) hj) (lt_one_add _)))
  obtain ⟨s,hs,ho,hx⟩ := mem_nhds_iff.mp (((show ∀ᶠ y in 𝓝 d, T y ∈ S from he.continuousAt (h.territory.mem_nhds hS)).and
    (eventually_all_finset L|>.mpr hh)).and (he.eventually (by simp)))
  have Hs : MapsTo T s S := fun _ hv => (hs hv).1.1
  have ht : ContDiffOn ℝ k T s := ho.contDiffOn_iff.mpr fun _ hz => (hs hz).2
  let R := (k.factorial:ℝ) * l^k
  refine ⟨s,hx,ho,fun i => (h.smooth i).comp ht Hs,fun z hz => h.meas _ (Hs hz),
    fun i => R*b i,hb.const_mul _,fun i x hx j hj => ?_⟩
  have hz := norm_iteratedFDerivWithin_comp_le (C:=b i) (D:=l) (h.smooth i) ht
    (Nat.cast_le.mpr hj) h.territory.uniqueDiffOn ho.uniqueDiffOn Hs hx ?_ ?_
  · rw [← iteratedFDerivWithin_of_isOpen _ ho hx]
    have hK : 0 ≤ b i := le_trans (norm_nonneg _) (hb' i _ hS 0 (Nat.zero_le k))
    dsimp only [R]; rw [mul_right_comm (k.factorial:ℝ)]; apply hz.trans; gcongr
  · intro m hm
    rw [iteratedFDerivWithin_of_isOpen m h.territory (Hs hx)]
    exact hb' i _ (Hs hx) m (hm.trans hj)
  intro m hm h'm
  rw [iteratedFDerivWithin_of_isOpen m ho hx]
  exact ((hs hx).1.2 m (Finset.mem_range.mpr <| Nat.lt_succ_iff.mpr <| h'm.trans hj)).trans
    (by nth_rw 1 [← pow_one l]; gcongr)

end Window
end YM.Further.DenseMixedKernels
