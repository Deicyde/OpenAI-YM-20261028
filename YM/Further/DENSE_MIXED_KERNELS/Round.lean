import YM.Further.DENSE_MIXED_KERNELS.Secure

/-!
# Actual patch and witness/protector profiles for H/K mixed vertices

Chi uses thresholds 1,4 on **squares**. Can use Γ with smaller
post-L const for Z. `Pads` prices them along the common normalized
color kernels, at TRUE displacements even on wrapping geometry and
stencils shared with other factors. Use to construct actual `Word`
entries before kernel switch. No finding a smooth representative of an
input H's value outside its mask. Guard inclusion hypotheses when
converting a principal term at a particular stencil are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module
open Port Gaussian Surface Tree Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {Ω ι κ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] {G : Gauge}
    {n : Side} {k : ℕ} {g w d r T : ℝ} {A : ChartRatio G} {H : Port A}
    {W : Config G n → Surface H ι κ Ω} {S : Surface H ι κ Ω}
    {U : Config G n} {P : Directions G n → Prop}

namespace Pads
variable (c : Chi)

def plot (x : G.Color) := c.read (‖x‖^2)
def skin (G : Gauge) (c : Chi) (w : ℝ) (x : G.Color) := plot c (w⁻¹ • x)

variable {x : G.Color}

lemma skins (hw : 0 < w) : skin G c w x = c.innerShare w ‖x‖ := by
  unfold skin plot Chi.innerShare
  congr 2
  rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hw).le, inv_mul_eq_div]
lemma escape (hw : 0 < w) (h : 2*w ≤ ‖x‖) : skin G c w x=0 := by
  by_contra he; rw [skins c hw] at he; exact (c.chosen_lt _ _ hw he).not_ge h
lemma remains (hw : 0 < w) (h : ‖x‖ ≤ w) : skin G c w x=1 := by
  rw [skins c hw]; apply Chi.to_one
  nlinarith [(div_le_one hw).mpr h,div_nonneg (norm_nonneg x) hw.le]
lemma scope (w : ℝ) : 0 ≤ skin G c w x ∧ skin G c w x ≤ 1 := c.range ..
lemma plot_smooth : ContDiff ℝ (k:WithTop ℕ∞) (plot (G:=G) c) :=
    (c.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ ⊤))).comp (contDiff_norm_sq (𝕜:=ℝ))


lemma global (G : Gauge) (k : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ∀ j, 0<j → j ≤ k →
    ‖iteratedFDeriv ℝ j (plot (G:=G) c) x‖ ≤ C := by
  let B := Metric.closedBall (0:G.Color) 2
  obtain ⟨C,hC,H⟩ := compact_pays k (plot c) B (ProperSpace.isCompact_closedBall ..) (fun _ _ => (plot_smooth c).contDiffAt)
  refine ⟨C,hC,fun x j hj hk => ?_⟩
  by_cases hx : x∈B
  · exact H _ hx _ hk
  have he : plot (G:=G) c=ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [show ∀ᶠ y in 𝓝 x,y∈Bᶜ from Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
    apply c.to_zero
    rw [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] at hy
    nlinarith
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hj)]
  exact (@norm_zero (Tensor.T G.Color ℝ j) _).trans_le (zero_le_one.trans hC)

def grow (G : Gauge) (c : Chi) (k : ℕ) (T : ℝ) := (global c G k).choose * (2^k*T)

lemma upward (_G : Gauge) (ht : 0≤T) (k : ℕ) : 0 ≤ grow _G c k T := mul_nonneg (zero_le_one.trans ((global c _ _).choose_spec.1))
    (by positivity)

lemma reads_skin {f : Config G n→G.Color} (hs : Ripple f U P k r T) (ht : 0≤T) (hw : 0<w) (he : r ≤ w) :
    Pitch (fun v => skin G c w (f v)) U P k 1 (grow G c k T) := by
  let g' x := w⁻¹ • (f x)
  let L : G.Color →L[ℝ] G.Color := w⁻¹ • ContinuousLinearMap.id _ _
  have hL x : ‖L x‖ ≤ w⁻¹ * ‖x‖ := by
    change ‖w⁻¹ • x‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hw).le]
  have hh : Ripple g' U P k 1 T := ((hs.linear L hL (by positivity)).mono ht le_rfl zero_le_one (by
    rw [inv_mul_eq_div,div_le_one hw]; exact he))
  let C := (global c G k).choose
  have hp : 1 ≤ C := (global c G k).choose_spec.1
  have h := hh.comp (g:=plot c) le_rfl ht (zero_le_one.trans hp) (plot_smooth c).contDiffAt
    ((global c G k).choose_spec.2 _) zero_le_one
  unfold skin; refine (h.save (by positivity) hp zero_le_one).parcel (upward c G ht k) le_rfl ?_
  exact (Real.norm_of_nonneg (scope (G:=G) c w (x:=f U)).1).trans_le (scope (x:=f U) c w).2

/-- For broad patch input a=mean+gZ. This price remains polynomial even when
there are other data calls on the same held coordinate. `w≥g` can choose
by the delay. Off plateaus derivatives not taken through an equality-only
selector: true Γ all around. -/
def displace (S : Surface H ι κ Ω) (g : ℝ) (p : Ω × H.front ι (H.Room κ)) := H.swing g (S.mean p.1) p.2.1

def pool (S : Surface H ι κ Ω) (c : Chi) (g w : ℝ) (s : Finset ι) (p : Ω × H.front ι (H.Room κ)) := ∏ i∈s,
    skin G c w (displace S g p i)
def stepRate (H : Port A) (c : Chi) (k : ℕ) (T : ℝ) := grow G c k (curve H k T)

lemma curve_pos (H : Port A) (k : ℕ) (hT : 0≤T) : 0 ≤ curve H k T :=
  mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
lemma step_nonneg (k : ℕ) (ht : 0≤T) : 0 ≤ stepRate H c k T := upward c G (curve_pos _ k ht) _

omit [MeasurableSpace Ω] in
lemma broad (s : Finset ι) (hs : Shifts W U P k g T) (ht : 0≤T) (hg : 0<g) (he : g≤1)
    (hw : g≤w) (y : Ω × H.back ι (H.Room κ)) (hp : y ∈ (W U).Perch) :
    Pitch (fun v => pool (W v) c g w s ((W v).mapUp g y)) U P k 1 (s.card*stepRate H c k T) := by
  have h (i : ι) := reads_skin c (f:=fun v => (W v).arc y i) (motion hg he ht hs y hp i) (curve_pos _ _ ht)
    (hg.trans_le hw) hw
  have hh v i : (displace (W v) g ((W v).mapUp g y)) i=(W v).arc y i := congr_fun (swing_track (W v) y hg) i
  unfold pool; simp_rw [hh]
  simpa only [Finset.prod_const, one_pow, Finset.sum_const,nsmul_eq_mul] using! product_real s
    (f:=fun i v => skin G c w ((W v).arc y i)) (fun i _ => h i)

omit [MeasurableSpace Ω] in
lemma pool_bounds (a : Ω × H.front ι (H.Room κ)) (s : Finset ι) : 0 ≤ pool S c g w s a ∧ pool S c g w s a ≤ 1 :=
  ⟨Finset.prod_nonneg fun i _ => (scope (x:=displace S g a i) c w).1, Finset.prod_le_one (fun i _ => (scope (x:=displace S g a i) c w).1)
    (fun i _ => (scope (x:=displace S g a i) c w).2)⟩
omit [MeasurableSpace Ω] in
lemma in_pool {s : Finset ι} (a : Ω × H.front ι (H.Room κ)) (h : pool S c g w s a ≠ 0) (hw : 0<w) :
    ∀ i∈s, ‖displace S g a i‖ < 2*w := fun _ hi => lt_of_not_ge (fun ht => h <| Finset.prod_eq_zero hi (escape c hw ht))
omit [MeasurableSpace Ω] in
lemma full_pool {s : Finset ι} {a : Ω × H.front ι (H.Room κ)} (hw : 0<w) (h : ∀ i∈s, ‖displace S g a i‖ ≤ w) :
    pool S c g w s a=1 := Finset.prod_eq_one fun i hi => remains c hw (h i hi)


-- stencil may include K too (unchanged coordinates). Count each true physical
-- position at most once in profile controls; no cost from E/K histories.
def take (H : Port A) (i : ι⊕κ) : H.front ι (H.Room κ)→L[ℝ]G.Color :=
    i.elim (fun j=> ContinuousLinearMap.proj (R:=ℝ) j ∘L ContinuousLinearMap.fst ℝ _ _)
      (fun j=> ContinuousLinearMap.proj (R:=ℝ) j ∘L ContinuousLinearMap.snd ℝ _ _)

lemma power (z : H.front ι (H.Room κ)) (i : ι⊕κ) : ‖take H i z‖ ≤ ‖z‖ := by
  rcases i with i|j
  · exact (norm_le_pi_norm z.1 i).trans (le_max_left ..)
  exact (norm_le_pi_norm z.2 j).trans (le_max_right ..)

-- use price even at weakness equality r=1

def light (H : Port A) (c : Chi) (d : ℝ) (i : ι⊕κ) (p : H.front ι (H.Room κ)) := skin G c d (take H i p)
omit [Fintype ι] [Fintype κ] in
lemma lum_cont (d : ℝ) (i : ι⊕κ) : Continuous (light H c d i) := by
  unfold light skin; apply Continuous.comp (plot_smooth c (G:=G) (k:=0)).continuous
    (f:=fun x => d⁻¹ • take H i x); exact (continuous_const (y:=d⁻¹)).smul (take H i).continuous

def speed (H : Port A) (c : Chi) (k : ℕ) (T : ℝ) := grow G c k (2*curve H k T)
lemma sunnier (k : ℕ) (ht : 0≤T) : 0 ≤ speed H c k T := upward c G (by have he := curve_pos H k ht; positivity) _

omit [MeasurableSpace Ω] in
lemma shade (hs : Shifts W U P k g T) (ht : 0≤T) (hg : 0<g) (he : g≤1) (hd : 1≤d) {y : Ω × H.back ι (H.Room κ)}
    (hp : y∈(W U).Perch) (i : ι⊕κ) : Pitch (fun v => light H c d i ((W v).mapUp g y).2) U P k 1 (speed H c k T) := by
  have h := drift hg he ht hs y hp
  let f x := ((W x).mapUp g y).2
  have H' : Ripple f U P k 1 (2*curve H k T) := ⟨h.smooth,fun l hl he hv => by
    rw [one_mul]; exact (h.bounds l hl he hv)⟩
  exact reads_skin c (H'.onLeft (take H i) (power · i)) (by have he:= curve_pos H k ht; positivity) (zero_lt_one.trans_le hd) hd

end Pads
end YM.Further.DenseMixedKernels
