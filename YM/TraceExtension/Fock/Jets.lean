import YM.TraceExtension.Fock.VacuumLocal
import YM.Shift.Cut

/-! Finite-order, uniform in probes through other slots, point support
lemma for Cauchy data. Includes the small-set remainder test; no continuity
of the distribution on discontinuous cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def finiteOrder (f : Probe V) (k : ℕ) := ∀ i ≤ k, iteratedFDeriv ℝ i f 0 = 0
omit [FiniteDimensional ℝ V] in
lemma fderivs_bound (f : Probe V) (k i j : ℕ) (hk : i+j ≤ k+1) (hv : finiteOrder f k) :
    ∃ C : ℝ, 0≤C ∧ ∀ (R : ℝ), 0 < R → ∀ x∈closedBall 0 R, ‖iteratedFDeriv ℝ i f x‖≤ C*R^j := by
    induction j generalizing i with
    | zero => exact ⟨Probe.size 0 i f,apply_nonneg ..,fun R h x hx => by simpa using SchwartzMap.le_seminorm ℂ 0 i f x⟩
    | succ j ih =>
        obtain ⟨C,hC,h⟩ := ih (i+1) (by omega)
        refine ⟨C,hC,fun R hR x hx=>?_⟩
        have ht := Convex.norm_image_sub_le_of_norm_fderiv_le (f:=iteratedFDeriv ℝ i ⇑f) (𝕜:=ℝ)
          (fun u _ => ContDiff.differentiable_iteratedFDeriv (m:=i) (by exact_mod_cast ENat.coe_lt_top i) (f.smooth ⊤) u)
          (fun u hu => (by rw [norm_fderiv_iteratedFDeriv]; exact h R hR u hu)) (convex_closedBall (0:V) R) (mem_closedBall_self hR.le) hx
        rw [hv i (by omega),sub_zero,sub_zero] at ht; rw [pow_succ,← mul_assoc]; exact ht.trans (mul_le_mul_of_nonneg_left (by simpa using hx) (by positivity))

private def squeezeMap (s : ℝ) (hs : 0<s) : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 s hs.ne')
private def fixed : Probe V := Probe.tint Probe.stall
private def equalizer (s : ℝ) (h : 0<s) : Probe V := Probe.along (squeezeMap s h) fixed
private def covering (f : Probe V) (r : ℝ) := if h : 0<r then Probe.sew (equalizer r h) f else 0

private lemma eq_margin {s : ℝ} (h : 0<s) : ((equalizer s h : Probe V):V → ℂ)=ᶠ[𝓝 0] 1 := by
    have he : ∀ᶠ i:V in 𝓝 0, squeezeMap s h i ∈ closedBall (0:V) 1 :=
       (squeezeMap s h).continuous.continuousAt.tendsto.eventually (by rw [map_zero]; exact closedBall_mem_nhds _ zero_lt_one)
    filter_upwards [he] with i hi
    rw [equalizer,Probe.along_at,fixed,Probe.tinted,Probe.stall.one_of_mem_closedBall hi]
    rfl
private lemma eq_range {s : ℝ} (h : 0<s) : tsupport ⇑(equalizer (V:=V) s h) ⊆ closedBall 0 (2/s) := by
    apply closure_minimal ?_ isClosed_closedBall; intro p hp; rw [mem_closedBall,dist_zero_right,le_div_iff₀ h]
    have he : squeezeMap s h p ∈ tsupport (fixed : Probe V) := subset_tsupport _ hp
    rw [fixed, Probe.tint_support, mem_closedBall,dist_zero_right] at he
    change ‖s • p‖≤2 at he; rw [norm_smul,Real.norm_of_nonneg h.le,mul_comm] at he; exact he
private lemma eq_deriv (i) {s : ℝ} (h : 0<s) (p : V) : ‖iteratedFDeriv ℝ i (equalizer s h) p‖ ≤ Probe.size 0 i (fixed (V:=V))*s^i := by
    let L : V →L[ℝ] V := (squeezeMap s h).toContinuousLinearMap
    have hl : ‖L‖ ≤ s := L.opNorm_le_bound h.le (fun v=> (by change ‖s • v‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg h.le]))
    have hv := SchwartzMap.le_seminorm ℂ 0 i (fixed (V:=V)) (L p)
    rw [pow_zero,one_mul] at hv
    rw [show ⇑(equalizer s h)= fixed ∘ L from rfl,L.iteratedFDeriv_comp_right ((fixed (V:=V)).smooth ⊤) p (by exact_mod_cast le_top)]
    apply ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _ |>.trans
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    gcongr
private lemma cover_small (f : Probe V) (d k i : ℕ) (hi : i≤k) (hp : finiteOrder f k) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℝ in atTop, Probe.size d i (covering f s)≤ε := by
    choose A hA hv using fun (j : Fin i.succ) => fderivs_bound f k (i-j.val) (j.val+1) (by have := j.isLt; omega) hp
    let u (j:ℕ) := if h:j < i+1 then A ⟨j,h⟩ else 0
    have hu j : 0≤u j := by unfold u; split; exact hA _; exact le_rfl
    let e := ∑ j∈Finset.range (i+1), (i.choose j:ℝ)*Probe.size 0 j (fixed (V:=V))*(u j*2^(j+1))
    have he : 0≤e := by unfold e; apply Finset.sum_nonneg; intro j _; unfold Probe.size; have := hu j; positivity
    filter_upwards [eventually_gt_atTop (2:ℝ),eventually_gt_atTop (e/ε)] with s hs hb
    have h : 0<s := by linarith
    apply (covering f s).seminorm_le_bound ℂ d i hε.le
    intro x
    by_cases hx : x∈closedBall 0 (2/s)
    · have hz : ‖x‖≤1 := by rw [mem_closedBall,dist_zero_right] at hx; exact hx.trans ((div_le_one h).2 hs.le)
      apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz))
      rw [show ⇑(covering f s)=(fun x=>equalizer s h x*f x) by ext1; simp [covering,h]]
      refine (norm_iteratedFDeriv_mul_le ((equalizer s h).smooth ⊤) (f.smooth ⊤) x (by exact_mod_cast le_top)).trans (le_trans ?_ (show e/s≤ ε from (div_le_iff₀ h).2 (by linarith [(div_lt_iff₀ hε).1 hb])))
      unfold e; rw [Finset.sum_div]; apply Finset.sum_le_sum; intro j hj
      have hh : j < i+1 := Finset.mem_range.mp hj
      simp only [u,dif_pos hh]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (eq_deriv j h x) (by positivity : (0:ℝ) ≤ i.choose j))
        (hv ⟨j,hh⟩ _ (by positivity : (0:ℝ)< 2/s) x hx) (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (by unfold Probe.size; positivity) (by positivity)))).trans_eq (by dsimp only; rw [div_pow]; field_simp; ring)
    have he : x∉tsupport (covering f s) := fun ht => hx (eq_range h (show x∈tsupport (equalizer s h) from (Probe.shrinks _ _ (by simpa [covering,h] using ht)).1))
    rw [Probe.vanish_j _ _ (notMem_tsupport_iff_eventuallyEq.mp he),norm_zero,mul_zero]; exact hε.le

lemma jet_support (p : Seminorm ℂ (Probe V)) (h : Continuous ⇑p) : ∃ k : ℕ, ∀ (A : Distn V) (b : ℝ),
    0≤b → (∀ f, ‖A f‖ ≤ b*p f) → (∀ f : Probe V, HasCompactSupport ⇑f → 0∉tsupport f → A f=0) →
    ∀ f, finiteOrder f k → A f=0 := by
    obtain ⟨s,c,hc,hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p h
    let k := s.sup Prod.snd
    refine ⟨k,fun A b hb hA hx f hf=>?_⟩
    have hs := (Distn.from_compact A (s:={(0:V)}ᶜ)).2 (fun f hs ht=> hx f ht (fun h => hs h rfl))
    have hp (x:ℝ) (h:0<x) : A (covering f x)=A f := by
        symm; apply sub_eq_zero.mp; rw [← map_sub]; apply hs
        have hh : (0:V)∉tsupport ⇑(f-covering f x) := notMem_tsupport_iff_eventuallyEq.mpr (by
           filter_upwards [eq_margin h] with i hi
           change _ - covering f x i=0; rw [covering,dif_pos h, Probe.sews, hi]; simp)
        rintro y hy hz; exact hh ((show y=0 from hz) ▸ hy)
    by_contra hn
    let ε := ‖A f‖; have he : 0<ε := norm_pos_iff.mpr hn
    let d := (↑c:ℝ)+1; have hd : 0<d := add_pos_of_nonneg_of_pos c.property zero_lt_one
    let E : ℝ≥0 := ⟨ε/(2*d*(b+1)),by positivity⟩
    have hv : 0 < (E:ℝ) := div_pos he (by positivity)
    obtain ⟨x,hx,hh⟩ := (((eventually_all_finset s).mpr fun i hi => cover_small f i.1 k i.2 (Finset.le_sup hi) hf E hv).and (eventually_gt_atTop (0:ℝ))).exists
    have hr := hA (covering f x); rw [hp x hh] at hr
    have hy : p (covering f x) ≤ d*E := by
        refine (hC _).trans ?_
        rw [_root_.smul_apply, Seminorm.finset_sup_apply]; change (c:ℝ)*_ ≤ _
        apply mul_le_mul (le_add_of_nonneg_right zero_le_one) ?_ _ hd.le
        · exact (show s.sup _ ≤ E from Finset.sup_le fun i hi => (show ((⟨Probe.size i.1 i.2 (covering f x),apply_nonneg ..⟩:ℝ≥0) ≤ E) from hx i hi))
        positivity
    have hm : ε≤b*(d*E) := hr.trans (mul_le_mul_of_nonneg_left hy hb)
    change ε ≤ b*(d*(ε/(2*d*(b+1)))) at hm; field_simp at hm; nlinarith
end YM.TraceExtension.Photons
