import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Castro
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hallmark
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StreamsA

/-!
# Compulsory and analytic diagonal buds with payments

Keep ALL flags in Bloom. Value on each unmasked row full. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Gate Scroll Vine Tablet Metric Pulse Itinerary

lemma mistropy (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (j : ℕ) {η r Q : ℝ} (Y : ℝ)
    (ho : Torch η r Q) {V : ℝ → ℝ} (h : Rate G L (-(1/2)) V) : ∃ K W : ℝ → ℝ, Rate G L 0 K ∧
    Rate G L (-(1/2)) W ∧ ∀ᶠ s : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U : E→Config G c)
      (x:E), S.patch=D → S.patch.L=L → X.x=s → Port P L η r Q Y (vary X (U x)) →
      Mode U x j (V s) → ∀ i : Bond f, let p t:= (vary X (U t)).condensation i
      Brush j (K s) 1 p x ∧ (¬Inside (atEdge S i) X.seeds (30*X.B) → Brush j (W s) 1 p x) := by
  obtain ⟨w,hw,hq⟩:= condenses P L D hd η r Q Y
  obtain ⟨C,hC,H⟩:= bounded_stencils P D hd
  let t := P.top.width; let a:= min (t/2) (retain η r Q)
  have hv : 0 < a := lt_min (half_pos P.top.width_pos) ho.prices
  have ht : a<t := (min_le_left ..).trans_lt (by have hx : 0 < t:=P.top.width_pos; linarith)
  let A := carat D P L a C; let R:= A*A+1; let f (x:ℝ):= kernelGrowth (radiusB x) G (V x); let m:= tubularPrice G L
  let u (x:ℝ):= (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η r Q m)+crownP j (radiusB x) m G η r Q R
  let v (x:ℝ):= f x+f x; let Z x:= v x+driftP j (v x)
  have hF : Rate G L (-(1/2)) Z := (jet_growth G L h|>.add (jet_growth G L h)).add (((jet_growth G L h).add
    (jet_growth G L h)).mul_left _)
  have he : Rate G L 0 u := (Rate.const _).add (((polynomial G L j m _ _).mul_left _).mul_left (Fintype.card G.ColorIndex))
  refine ⟨fun x=> u x*(1+Z x)^j,fun x=> w x+u x*Z x,?_,?_,?_⟩
  · simpa only [zero_mul,zero_add] using! he.mul ((Rate.add (Rate.const 1) (hF.weaken (by norm_num))).pow j)
  · apply Rate.add hw; simpa only [zero_add] using! he.mul hF
  filter_upwards [hF.below (by norm_num) 1 zero_lt_one,hq] with s hx hz c f' S T F X E _ _ _ U x hS hL hX hp hu i p
  subst s
  let Y':= vary X (U x); let D:= X.shutter
  have hf := hp.sails.room
  have hP := plates X _ hS hL hf hu _ hC (H _ _ S T hS hf.accepted) hv.le ht
  have hh:= plotsB D (x:=x) (fun v=> (vary X (U v)).plate) hp.sails.scale hP (show a≤retain η r Q from min_le_right ..) ho i
  have hu := (hp.empty)
  let p₀ := Batch.joint X.blank.plate D i
  have hK : ‖p₀‖ ≤ (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η r Q m) := Batch.nearBase D ho (show Allow X.blank.plate (along S) m η r Q from hu.scale) i
  have ht : Brush j (u X.x) (Z X.x) p x := semi (((Brush.certified hh.pos p₀).climb hK le_rfl).separating hh)
  exact ⟨ht.trim, fun hy => shrinker ht ((hz _ _ S T F Y' rfl hS hL hp.sails hp.placed hp.allgauge hu).2 i hy) ((le_abs_self _).trans hx)⟩
end YM.ConnectedActivityE6.Blaze.Vine
