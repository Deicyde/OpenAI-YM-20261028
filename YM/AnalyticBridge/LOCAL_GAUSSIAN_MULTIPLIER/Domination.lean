import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.ReturnPrice
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.UnderIntegral


/-!
# Justify integration of the extended germ

May work with poor estimates in the neighborhood for domination.

No state that the true budgets at V also pay on a new neighborhood
(with flags/quadratic costs recomputed there, etc.).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented Metric
open Curtain Tariff Spot.Programme Spot Notice Moments Integral
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

private lemma small_basis {G : Gauge} {c : Side} (p : BudgetPoint) (o : Site c) (l : List (Directions G c)) :
    ∃ t : ℝ, 0 < t ∧ ∀ A∈l,p.dirBound o (t • A) := by
  let s := l.toFinset
  have he (A : Directions G c) : ∀ᶠ t : ℝ in nhds 0, p.dirBound o (t • A) := by
    apply eventually_all.mpr; intro e
    have ht : Tendsto (fun t : ℝ => ‖(t • A) e‖) (nhds 0) (nhds 0) := by
      have hh (t : ℝ) : (t • A) e=t • A e := rfl
      simp_rw [hh]
      simpa using! (show Continuous (fun t : ℝ => ‖t • A e‖) by fun_prop).tendsto 0
    exact ht.eventually (ge_mem_nhds (mul_pos p.threshold_pos (by positivity)))
  have hh : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), ∀ A : s,p.dirBound o (t • A.val) :=
    eventually_all.mpr (fun i => (he i).filter_mono inf_le_left)
  obtain ⟨t,ht,h⟩ := ((show ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t ∈ Ioi 0 from self_mem_nhdsWithin).and hh).exists
  exact ⟨t,ht,fun A hA => h ⟨A,by simpa [s] using hA⟩⟩

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {H R K α β γ : Type} [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
  {X : Support c} {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
  {n : q.Run α β γ} {a : Notice l}
namespace Reading

variable {B : Reading a n} {r t : ℝ} {k : ℕ} {o : Site c} {T : Tariff α β γ (Component G H R)} {Ω : Set (Config G c)}

/-- Qualitative commissioning use on V neighborhood. Need upper on inverse
coat here (positive det priced locally), without volume uniformity; see
also `entrance`. Can use separate tighter `Clearance` on the charged support
inventory only. -/
structure Rally (B : Reading a n) (o : Site c) (k : ℕ) (t r : ℝ) (Ω : Set (Config G c))
    (T : Tariff α β γ (Component G H R)) : Prop where
  ready : Ready d.chart d.g r
  border : t < r
  broad : 0 ≤ t
  always : IsOpen Ω
  attached : B.Shutter Ω t
  normalization : ∃ M : ℝ, 0 ≤ M ∧ ∀ V ∈ Ω,(coat (a.C V))⁻¹ ≤ M
  powered V : V ∈ Ω → Clearance B t T V (d.out.dirBound o) k

omit [DecidableEq H] [DecidableEq R] [Fintype H] [Fintype R] [Fintype K] in
private lemma log_small {V : Config G c} {p : Reel G H R K} (h : Needed l t V p) (ht : t < r) (hp : Ready d.chart d.g r)
    (i : H) : unlit (l.copy V) p.2.2 i ∈ closedBall 0 t := by
  let x := p.2.2 i*(l.copy V i)⁻¹
  have he : x∈patchGeom G r := escape h ht i
  obtain ⟨w,hw,hl⟩ := h i
  unfold unlit; rw [peek_ok hp.ins he, ← (show G.lieExp w=x from hl), (geom_pay hp.ins).2.2.1 (closedBall_subset_ball ht hw)]; exact hw

private lemma refund {J : ChartRatio G} (hp : LocalRatio J) (ht : 0 ≤ t) (hr : t < J.radius) :
    ∃ x : ℝ, 0 < x ∧ ∀ a∈closedBall (0:G.Color) t,x ≤ J.scale * J.J a := by
  let s := closedBall (0:G.Color) t
  have hx : s ⊆ ball 0 J.radius := closedBall_subset_ball hr
  have hh : ContinuousOn (fun a => J.scale*J.J a) s := fun a ha =>
    (continuousAt_const.mul (hp.germ a (hx ha)).continuousAt).continuousWithinAt
  obtain ⟨a,ha,h⟩ := (isCompact_closedBall _ _).exists_isMinOn ⟨0,closedBall_subset_closedBall (le_refl _) (mem_closedBall_self ht)⟩ hh
  exact ⟨_,mul_pos hp.scale (hp.pos a (hx ha)),fun b hv => h hv⟩

private def blanket (Q : ℝ) (p : Reel G H R K) := Real.exp (-(Q⁻¹/4) * load Finset.univ p.2.1)

omit [DecidableEq H] [DecidableEq R] in
private lemma accepted {Q : ℝ} (hq : 0 < Q) : Integrable (blanket Q (G:=G) (R:=R) (K:=K) (H:=H)) (pullLaw G H R K) := by
  let f (z : Prices G R) := Real.exp (-(Q⁻¹/4)*load Finset.univ z)
  have hi : Integrable f := by
    unfold f load; simp_rw [Finset.mul_sum,Real.exp_sum]
    exact Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq (by positivity : (0:ℝ)<Q⁻¹/4)
  exact (hi.comp_fst (piHaar G H)).comp_snd _

omit [Fintype K] in
private lemma subsidize (h : B.Rally o k t r Ω T) (i : ℕ) (hΩ : Ω.Nonempty) :
    ∃ x : ℝ, 0 ≤ x ∧ ∀ p W,W∈Ω → Needed l t W p →
      a.reinforce T k i 0 r W p ≤ x*blanket T.capacity p := by
  let Hc := Fintype.card H
  let Q := T.capacity
  let F := T.outside k Hc i 0
  obtain ⟨y,hy,hy'⟩ := refund h.ready.localPrice h.broad (h.border.trans_le h.ready.seen)
  obtain ⟨M,hm,hM⟩ := h.normalization
  obtain ⟨c,hc⟩ := hΩ
  let A := (y^Hc)⁻¹
  let B₀ := (d.g ^ Fintype.card (H × G.ColorIndex))⁻¹
  let σ := Q⁻¹/8
  let j := T.degreeTag i 0
  have hp := h.powered c hc
  have hq : 0 < Q := hp.leased.size
  have hf : 0 ≤ F := T.outside_nonneg hp.leased ..
  have hB : 0 ≤ B₀ := inv_nonneg.mpr (pow_nonneg h.ready.heat.le _)
  have hA : 0 ≤ A := by unfold A; positivity
  have hs : 0 < σ := by unfold σ; positivity
  let b := Moments.inflate j σ
  have hb : 0 ≤ b := zero_le_one.trans (inflate_ge j hs.le)
  refine ⟨B₀*A * (M*(F*b)),by positivity,fun p W hw hX => ?_⟩
  let C := a.C W; let z := a.imprint W p
  let v := load Finset.univ z
  let f := (-force C z)/2
  let s := unlit (l.copy W) p.2.2
  have hc := h.powered W hw
  have ht : y^Hc ≤ pay d.chart s := by
    unfold pay
    convert! (Finset.prod_le_prod (f:=fun _ : H => y) (g:=fun i => d.chart.scale*d.chart.J (s i)) (s:=Finset.univ)
      (fun _ _ => hy.le) fun k _ => hy' _ (log_small hX h.border h.ready k)) using 1
    simp [Hc]
  have ht : (pay d.chart s)⁻¹ ≤ A := inv_anti₀ (pow_pos hy _) ht
  have HH : a.strip r W p ≤ B₀*A * (M * Real.exp f) := by
    rw [Notice.strip,vested _ _ _ _ _ _ _ (escape hX h.border) h.ready hc.pane]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht hB)
      (mul_le_mul_of_nonneg_right (hM W hw) (Real.exp_pos _).le) (ratio_pos hc.pane _).le (mul_nonneg hB hA)
  have hv := hc.bought.compress_gap hc.pane hq
  have hi : Q⁻¹*v ≤ force C z := by rw [show v=_ from load_square z]; exact hv.lower z
  have H_v : load T.seat z ≤ v := load_le z (Finset.subset_univ _)
  have hinc : load Finset.univ p.2.1 ≤ v := by
    unfold v z Notice.imprint poured
    rw [load_square,load_square,join_square]; exact le_add_of_nonneg_right (YM.FreeResolvent.normSum_nn _)
  have he := mul_le_mul HH (le_refl (T.finalPower k (Fintype.card H) i 0 z)) (T.every_nonneg hc.leased ..) (by positivity)
  apply he.trans
  rw [T.beta_price]
  let U := Real.exp (σ*load T.seat z); let P := Real.exp (σ*v)
  have HZ : powers z^j ≤ b*P := inflates j (load_nonneg ..) hs
  have hx : Real.exp f*(P*U) ≤ blanket Q p := by
    unfold U P blanket; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    unfold f; rw [show Q⁻¹/4 = 2*σ by unfold σ; ring]
    -- absorb σ v + σ load
    unfold σ v at *; linarith only [hi,mul_le_mul_of_nonneg_left H_v hs.le,mul_le_mul_of_nonneg_left hinc hs.le]
  change B₀*A*(M*Real.exp f)*(F*(powers z^j*U)) ≤ _
  calc
    _ ≤ B₀*A*(M*Real.exp f)*(F*(b*P*U)) := by unfold U; gcongr
    _ = (B₀*A * (M*(F*b))) * (Real.exp f*(P*U)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)

namespace Rally
lemma paid (h : B.Rally o k t r Ω T) (hΩ : Ω.Nonempty) :
    Study (pullLaw G H R K) Ω k (fun p V => B.endorsed r V p) := by
  have hx (V : Config G c) : Measurable (B.endorsed r V) := rewrite_meas_of d.chart d.g r (l.copy V) (a.C V)
    (a.tide V) (a.readable V) (fun x y => B.word V (x,y)) (B.member V) h.ready
  have hs p V (hv : V∈Ω) := (h.powered V hv).success h.ready (h.always.mem_nhds hv) h.border h.attached p
  refine ⟨h.always,fun V _ => hx V, fun p V hv => (hs p V hv).smooth, fun L hl => ?_⟩
  obtain ⟨x0,h0⟩ := hΩ
  obtain ⟨x,hx,Hx⟩ := subsidize h L.length ⟨x0,h0⟩
  let M (p : Reel G H R K) := x*blanket T.capacity p
  have hm (p) : 0 ≤ M p := mul_nonneg hx (Real.exp_pos _).le
  obtain ⟨w,hw,hW⟩ := small_basis d.out o L
  let u := (w ^ L.length)
  have hu : 0<u := pow_pos hw _
  refine ⟨fun p => u⁻¹ * M p, ((accepted (h.powered x0 h0).leased.size).const_mul _).const_mul _,fun p V hv => ?_⟩
  let F (V : Config G c) := B.endorsed r V p
  change ‖leftDerivs F L V‖ ≤ u⁻¹*M p
  by_cases hi : Needed l t V p
  swap
  · have hb : F =ᶠ[nhds V] fun _ => 0 := by
      filter_upwards [h.always.mem_nhds hv,exterior hi] with W hw ht
      exact Classical.not_not.mp fun he => ht (B.shrinks h.ready h.attached W hw he)
    rw [identical hb,Work.G07.left_const]
    simp only [ite_self,norm_zero]; exact mul_nonneg (inv_pos.mpr hu).le (hm _)
  rw [inv_mul_eq_div,le_div_iff₀ hu,mul_comm]
  have hr := (h.powered V hv).cash h.ready (h.always.mem_nhds hv) h.border h.attached
    (L.map (w • ·)) (by simpa) (fun i hj => by obtain ⟨j,hh,rfl⟩ := List.mem_map.mp hj; exact hW j hh) p
  change ‖leftDerivs F (L.map (w • ·)) V‖ ≤ _ at hr
  rw [ProjectorNext.Equivariance.slot_scale L _ ((hs p V hv).smooth.fewer hl),norm_smul,
    Real.norm_of_nonneg (pow_nonneg hw.le _),List.length_map] at hr
  exact hr.trans (Hx p V hv hi)
end Rally
end Reading
end YM.AnalyticBridge.LocalGaussian
