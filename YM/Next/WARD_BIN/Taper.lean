import YM.Next.WARD_BIN.Project
import YM.Vac.Shelter


/-!
# On fitted footprints the t-rate controls vanishing in slot degree

Fitting in a large enough torus, read the actual curved links with common
scaled *inputs*. Keep the entire needed neighborhood. Not presuming that
a stencil value on all-good extends differentiably across the flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G07 Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {k : ℤ} {d n l : ℕ} {S : Finset Cover}

lemma value_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {X : F} (h : HasDerivAt f X 0) (h0 : f 0 = 0) :
    Tendsto (fun t : ℝ => t⁻¹ • f t) (𝓝[>] (0:ℝ)) (𝓝 X) := by
  simpa only [zero_add,h0,sub_zero] using!
    (hasDerivAt_iff_tendsto_slope_zero.mp h).mono_left
      (nhdsWithin_mono _ (show Ioi 0 ⊆ ({0}:Set ℝ)ᶜ from fun t ht => ne_of_gt ht))

/-- Real ray through Snap. Uniform for the finite link collection needed by
all *tests* of the cylinder. -/
lemma thin {n : Side} (H : Hol G) (V : Snap G d) (q : Site n) : ∃ c : ℝ,0<c ∧
    ∀ᶠ t in 𝓝[>] (0:ℝ), flags (c*t) (above q (curve H (t • V))) = ∅ := by
  let U (t : ℝ) := above q (curve H (t • V))
  have hF (e : Edge (Site n)) : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ t in 𝓝[>] (0:ℝ), G.chord (U t e) ≤ c*t := by
    let F (t : ℝ) := G.mat (U t e)
    have hf : HasDerivAt F (G.colorMat (access V (Lattice.lift (e.1-q),e.2))) 0 :=
      (Work.G02.linkGerm H d _).2.2 V
    let X := G.colorMat (access V (Lattice.lift (e.1-q),e.2))
    have hx : HasDerivAt (fun t : ℝ => F t-1) X 0 := hf.sub_const _
    have hw := value_scale hx (show F 0-1=0 by rw [show F 0=1 by unfold F U; rw [zero_smul,curve_zero]; rfl, sub_self])
    have he : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖t⁻¹ • (F t-1)‖ ≤ ‖X‖+1 := hw.norm.eventually (ge_mem_nhds (by linarith))
    have hs : 0 < G.colorScale := G.colorScale_pos
    refine ⟨(‖X‖+1)/G.colorScale,by positivity,?_⟩
    filter_upwards [he,self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t he ht
    have h : 0<t := ht
    change ‖F t-1‖/G.colorScale ≤ _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div] at he
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ h).mp he) hs.le
  choose p hp h using hF
  let z := 1+∑ i, p i
  have hZ : 0 < z := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => hp i)
  refine ⟨4*z,by positivity,?_⟩
  filter_upwards [eventually_all.mpr h,self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht h'
  apply RG.voids (r:=4*z*t) ?_ le_rfl
  intro i _
  apply le_trans (ht i)
  change p i * t ≤ 4*z*t/4
  rw [show 4*z*t/4=z*t by ring]; exact mul_le_mul_of_nonneg_right
    ((Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))
    (show 0<t from h').le

lemma below_lead {f : CoverConfig G → ℂ} (hf : Affordable S k f) (H : Hol G) (A : Snap G d)
    (ha : (l : ℤ) < k) : leading l (fun t : ℝ => f (curve H (t • A))) = 0 := by
  let g := fun t : ℝ => t • A
  have hs : ContDiff ℝ ∞ g := by simpa [g] using monoSmooth A 1 ∞
  have hv : ContDiffAt ℝ l (fun t : ℝ => f (curve H (t • A))) 0 := by
    apply ContDiffAt.of_le (n:=∞) _ (WithTop.coe_le_coe.mpr le_top)
    apply ContDiffAt.comp (f:=g) (g:=fun a => f (curve H a)) 0 ?_ hs.contDiffAt
    rw [show g 0=0 from zero_smul _ _]; exact hf.smooth_poly _ _
  obtain ⟨n,h⟩ := someFits S
  let q := (0:Site n)
  obtain ⟨b,hb,hr⟩ := thin H A q
  obtain ⟨c,hc,hC⟩ := hf.paid 0 2
  let K := k.toNat
  have hk : k=(K:ℤ) := Eq.symm (Int.toNat_of_nonneg (by omega))
  have hm : l<K := by exact_mod_cast (ha.trans_eq hk)
  apply leading_of_lim hv
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hx : Tendsto (fun t : ℝ => b*t) (𝓝[>] (0:ℝ)) (𝓝 (b*0)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) (g:=fun t => c*b^K*t^(K-l)) ?_ ?_
  · filter_upwards [hr,hx.eventually (ge_mem_nhds (show b*0<1 by simp)),self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht he h0
    have hy : 0<t := h0
    let U := above q (curve H (t • A))
    let p := Affordable.test (b*t) (by positivity) he
    have hh : Healthy p.threshold (footprint S q) U := by unfold Healthy; rw [show flags p.threshold U= ∅ from ht]; exact disjoint_bot_right
    have hc := (hC _ h p rfl q).bound [] le_rfl (by simp) U hh
    change ‖(t ^ l)⁻¹ • f _‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hw : ‖f (curve H (t • A))‖ ≤ c*(b*t)^K := by
      rw [← fromAbove hf.uses h q (curve H (t • A))]
      change ‖places q f U‖ ≤ _
      change ‖places q f U‖ ≤ c*(b*t)^k*(1:ℝ)^0 at hc
      rw [hk,zpow_natCast,pow_zero,mul_one] at hc; exact hc
    refine le_trans (mul_le_mul_of_nonneg_left hw (by positivity)) (le_of_eq ?_)
    rw [mul_pow, show t^K = t^(K-l)*t^l by rw [← pow_add, Nat.sub_add_cancel hm.le]]; field_simp
  simpa only [zero_pow (Nat.sub_ne_zero_of_lt hm), mul_zero] using!
    ((((show Continuous (fun t : ℝ => c*b^K*t^(K-l)) from by fun_prop).tendsto 0)).mono_left
      (nhdsWithin_le_nhds (a:=(0:ℝ)) (s:=Ioi 0)))

/-- The actual projected label has no entries below the exponent. -/
lemma crownAt_below {f : CoverConfig G → ℂ} (hf : Affordable S k f) (H : Hol G)
    (hp : GaugeInvariant f) (he : (l : ℤ) < k) : crownAt H hf hp d l n=0 := by
  by_cases hI : n ≤ d
  · apply Subtype.ext; apply Labels.eval_ext; intro V; rw [crownAt_ok _ _ _ _ hI]
    unfold crown; rw [← tile_reads]
    let g := f ∘ curve (d:=d) H
    have hg : ContDiffAt ℝ l g 0 := (hf.smooth_poly H d).of_le (WithTop.coe_le_coe.mpr le_top)
    have h (A : Snap G d) : Tensor.diagonal (Tensor.coeff g l 0) A = 0 := by
      rw [← leading_tensor A g hg]; exact below_lead hf H _ he
    change leading n _ = Labels.read _ _
    have hh (t : ℝ) : Tensor.diagonal (Tensor.coeff (f ∘ curve (d:=d) H) l 0) (engineered t (trunk d V)) = 0 := h _
    simp_rw [hh]
    change leading n (fun _ => (0:ℂ)) = Labels.read V 0
    simp [leading]
  unfold crownAt; rw [dif_neg hI]

end YM.WardBin
