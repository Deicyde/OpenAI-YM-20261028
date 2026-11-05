import YM.Next.UV_STRESS.Grain

/-!
# Cutoff smears actually priced from Spots

Requires one continuum extraction (PointLimits and Ordered and Smooth reached,
INCLUDING for Maxwell comparator at this C). No further extraction. Auxiliary
cluster arguments at *fixed* k and ***on old/new Wilson checks***.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Metric Extraction Climb Ward Table
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
variable {D n : ℕ} (W : ℕ → Wheel C D) {R : ℝ} {t : Caps n}

/-- One arity-and-label-list price (only used for *finite* lists in producer).
No constants or threshold uniform in unbounded lists. Crude cost times strip
width, gradient cost times *normalized* mesh/stripe. Bulk and slab from genuine
centered replicated arrays. `spacing` proportional to geometry ratio at
kth station (NOT cutoff), powers with respect to this parameter rather than
borrow hidden rate in outer volume. -/
structure Balances (F : Extraction.Order) (R : ℝ) (u : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (e A B : ℕ → ℝ) : Prop where
  goes : Tendsto e atTop (𝓝 0)
  stripe : Tendsto (fun k => (W k).σ) atTop (𝓝 0)
  room : ∀ᶠ k in atTop,(4*n:ℝ)*(W k).spacing ≤ (W k).σ
  pos : ∀ᶠ k in atTop, 0≤A k ∧ 0≤B k
  off : Tendsto (fun k => A k^n * (W k).σ) atTop (𝓝 0)
  on_ : Tendsto (fun k => B k^n * ((W k).spacing / (W k).σ)) atTop (𝓝 0)
  costs : ∀ᶠ k in atTop,(W k).Spots F R (e k) (A k) (B k) u w

lemma Balances.upon (f : Extraction.Order) {e A B : ℕ → ℝ} {u} {w : Ribbon (Bel C.book) t}
    (h : Balances W F R u w e A B) : Balances W (F.refine f) R u w e A B :=
  ⟨h.goes,h.stripe,h.room,h.pos,h.off,h.on_,h.costs.mono fun i hi => (W i).spots_upon hi f⟩

variable {e A B : ℕ → ℝ} (hC : C.Makes) (hr : 0<R) (H : F.PointLimits C S) (h : S.Smooth) (hP : (Bel C.book).Smooth)
variable (u : ∀ i,t i ≤ D) (w : Ribbon (Bel C.book) t) (hx : Balances W F R u w e A B)
include hx hC H h hP hr

theorem opens_clear (ε : ℝ) (he : 0 < ε) : ∀ᶠ k : ℕ in atTop, ∀ (𝓛 : Filter (ℕ×ℕ)) (_ : 𝓛.NeBot),
    𝓛 ≤ F.fuse → ∀ Y : Bud C t, Tendsto ((W k).tones u w) 𝓛 (𝓝 Y) →
      ∀ x ∈ Scaling.window R n, x∈openFilm _ (8*(W k).σ) → ‖glow (W k) S Y x-disc (hang t w) x‖ ≤ ε := by
  let Q := disc (hang t w)
  let s := Scaling.window (2*R) n
  have hf : ContinuousOn Q (conf n) := (smoothDisc hP _).continuousOn
  have hy : UniformContinuousOn Q s := (window_closed ..).uniformContinuousOn_of_continuous
    (hf.mono (fun x hx => spaced_conf (by positivity : 0 < (2*R)⁻¹) hx.1))
  obtain ⟨δ,hδ,hY⟩ := uniformContinuousOn_iff.mp hy (ε/3) (by positivity)
  obtain ⟨σ,hσ,hW⟩ := upgrade_window (n:=n) R hr
  have ht : Tendsto (fun k => ((n:ℝ)*4*(B k^n/(W k).σ)) *((4*n:ℝ)*(W k).spacing)) atTop (𝓝 0) := by
    have hh := hx.on_.const_mul ((n:ℝ)*4*(4*n))
    rw [mul_zero] at hh; exact hh.congr fun k => by ring
  filter_upwards [hx.room,hx.costs,hx.stripe.eventually (ge_mem_nhds hσ), ht.eventually (ge_mem_nhds (by positivity : 0 < ε/3)),
    hx.goes.eventually (ge_mem_nhds (by positivity : 0 < ε/3)),hx.stripe.eventually (gt_mem_nhds hδ),hx.pos] with k hk hc hd he' he hd' hP 𝓛 hQ hp Y ha x hh hg
  rw [← dist_eq_norm]
  let X := W k
  let p := address X.spacing x
  let y := tag X.spacing p
  have hb : dist y x ≤ X.σ := (approximate X.space _).trans hk
  have hu : y∈s := hW (mem_cthickening_of_dist_le _ x _ _ hh (hb.trans hd))
  have ht : dist (Q y) (Q x) ≤ ε/3 := (hY _ hu _ (hW (self_subset_cthickening _ hh)) (hb.trans_lt hd')).le
  have hh' := X.stripe
  have hs := glide X 𝓛 hp w hC H h ha hc hP.2 x hg hk |>.trans he'
  change dist (glow X S Y y) (glow X S Y x) ≤ _ at hs
  have hz' : y∈generic n := open_fit _ (by positivity : 0 ≤ 4*X.σ) (closed_thin hh'.le x hg hb)
  have hz : dist (glow X S Y y) (Q y) ≤ ε/3 := by rw [dist_eq_norm]; exact (match_phase X 𝓛 hp w H ha hc p hu hz').trans he
  rw [dist_comm] at hs
  exact (dist_triangle4 (glow X S Y x) (glow X S Y y) (Q y) (Q x)).trans
    ((add_le_add (add_le_add hs hz) ht).trans_eq (by ring))

theorem pays_film (ε : ℝ) (he : 0<ε) : ∀ᶠ k : ℕ in atTop, ∀ (𝓛 : Filter (ℕ×ℕ)) (_ : 𝓛.NeBot),
    𝓛 ≤ F.fuse → ∀ Y : Bud C t,Tendsto ((W k).tones u w) 𝓛 (𝓝 Y) →
      ∀ f : Test n, tsupport f ⊆ Scaling.window R n → ∀ M : ℝ,0<M → (∀ x, ‖f x‖ ≤ M) →
       ‖f.applyTo (glow (W k) S Y)- f.applyTo (disc (hang t w))‖ ≤ M*ε := by
  let Q := disc (hang t w)
  let Ω := Scaling.window R n
  have hp : ContinuousOn Q (conf n) := (smoothDisc hP _).continuousOn
  have hs : Ω ⊆ conf n := fun x hx => spaced_conf (by positivity : 0 < R⁻¹) hx.1
  obtain ⟨y,hy⟩ := ((window_closed R n).image_of_continuousOn ((hp.mono hs).norm)).bddAbove
  let c := max y 0
  have hc : 0≤c := le_max_right ..
  let p (k) := (A k^n+c)*(cost_band n R*(W k).σ)
  have ht : Tendsto p atTop (𝓝 0) := by
    have he := (hx.off.add (hx.stripe.const_mul c)).mul_const (cost_band n R)
    rw [mul_zero,add_zero,zero_mul] at he; exact he.congr fun k => by unfold p; ring
  let α := (ε/2)/(1+volume.real Ω)
  have ha : 0<α := by dsimp only [α]; positivity
  filter_upwards [opens_clear W hC hr H h hP u w hx α ha,hx.costs,hx.pos,ht.eventually (ge_mem_nhds (half_pos he))] with k hk hb hh hE L hL hv Y hQ f hw M hM hf
  change ‖f.applyTo _-f.applyTo Q‖ ≤ _
  have hu := (glow_smooth (W k) h Y).continuousOn
  rw [← test_sub _ Q hu hp f]; apply (spot_high R hr.le _ f hw α (W k).σ (A k^n+c) M
    (W k).stripe.le ha.le (add_nonneg (pow_nonneg hh.1 _) hc) hM.le hf (fun x hx => ?_) (hk L hL hv _ hQ) (hu.sub hp)).trans
  · apply mul_le_mul_of_nonneg_left _ hM.le
    have hh : α*(1+volume.real Ω)= ε/2 := div_mul_cancel₀ _ (by positivity : 1+volume.real Ω ≠ 0)
    change α*volume.real Ω + p k ≤ _
    linarith
  exact (norm_sub_le ..).trans (add_le_add (covers_cost _ L hv w hC H h hr hQ hb x hx)
    (le_trans (hy (mem_image_of_mem _ hx)) (le_max_left ..)))

/-- Pay for the actual smears with subfilter convergence and uniform estimate. -/
theorem cutoff_balance (hb : F.Ordered C S) (hc : ∀ᶠ k in atTop, ∃ y : ℝ,F.late fun N p => ‖(W k).atCut (N,p)‖ ≤ y)
    (ε : ℝ) (he : 0<ε) : ∀ᶠ k in atTop, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ, 0<M → (∀ x, ‖f x‖ ≤ M) → F.upper (fun N p => ‖(W k).paid (hang t w) u f N p- f.applyTo (disc (hang t w))‖) (M*ε) := by
  filter_upwards [hc,pays_film W hC hr H h hP u w hx ε he] with k hk ht f hf M hM hp
  intro η hη
  let A := disc (hang t w)
  let T (i : ℕ×ℕ) := (W k).paid (hang t w) u f i.1 i.2
  change ∀ᶠ i in F.fuse, ‖T i-f.applyTo A‖ ≤ M*ε+η
  by_contra H'
  have hx : ∃ᶠ i in F.fuse, M*ε+η < ‖T i-f.applyTo A‖ := by
    unfold Filter.Frequently; simp only [not_lt]; exact H'
  let L := F.fuse ⊓ Filter.principal {i| M*ε+η< ‖T i-f.applyTo A‖}
  haveI := frequently_iff_neBot.mp hx
  obtain ⟨y,hy⟩ := hk
  obtain ⟨b,hB,H,v,HV⟩ := finite_extract (𝓛:=L) (W k).atCut y
    ((show ∀ᶠ i : ℕ×ℕ in F.fuse, ‖(W k).atCut i‖ ≤ y from hy).filter_mono inf_le_left)
  have hy := le_trans hB (show L ≤ F.fuse from inf_le_left)
  let Y : Bud C t := fun i => v ⟨t i,Nat.lt_succ_of_le (u i)⟩ (w i)
  have hw : Tendsto ((W k).tones u w) b (𝓝 Y) := tendsto_pi_nhds.mpr fun i => Dash.arcing
    (tendsto_pi_nhds.mp HV _) tendsto_const_nhds
  have he : Tendsto T b (𝓝 (f.applyTo (glow (W k) S Y))) := by
    have hm := calibrated_smear hb b hy (dilate (W k).rad f) (tendsto_pi_nhds.mp hw)
    unfold Table.integralOn at hm; rw [zoom_integral] at hm
    exact hm
  apply not_le_of_gt (show ‖f.applyTo (glow (W k) S Y)-f.applyTo A‖ < M*ε+η from (ht b H hy Y hw f hf M hM hp).trans_lt (by linarith))
  refine ge_of_tendsto (he.sub_const (f.applyTo A)).norm ?_
  have hP : {i : ℕ × ℕ| M * ε + η < ‖T i - f.applyTo A‖} ∈ L := mem_inf_of_right (mem_principal_self ..)
  exact ((show ∀ᶠ i in L,_ from hP).filter_mono hB).mono fun _ h => h.le
end YM.Next.UVStress
