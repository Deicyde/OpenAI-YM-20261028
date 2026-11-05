import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc

/-!
# Warning germs share the genuine projection invoice

Vanishing with a strictly reduced margin; gives L² for score. Labels
count cardinal distinct, not even assuming tagged scans active. Value
of FINE mask, no differentiation of clipped U budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
namespace Silica.Clutch
variable {U : E → Config G c} {f' : E→ Directions G f} {w : E → Air f G} (H : Clutch X z o.a R.beta s x j U f' w)
variable (p : Cash W X.x μ L Q o α T R)

private lemma pall (d : ℝ) (t : ℝ) (χ : Chi) (h : 0<d) (ht : 0≤t) (he : t≤d) : χ.innerShare d t=1 := by
  have hv := (div_le_one h).mpr he; have hq : 0≤ t/d := div_nonneg ht h.le
  exact χ.to_one _ (by nlinarith)
include H p
-- holding ORIGINAL pulses. For budget of derivatives only.
lemma sleek (hk : Mode U x j d) (hm : Stamp T) (hp : X.manifest) (ha : X.width=o.K) (v : WarningAt c f)
    (he : X.watch (shouting S v) (o.ξ/2) R.beta (2*X.B) z) (K : Finset ℕ) :
    (fun y=> sprinkle (vary X (U y)) o.a R W (f' y) (X.input (worldZ X R.beta z)) K v)=ᶠ[𝓝 x] fun _=>0 := by
  let hI:= p.laws.intake; let Y:= X.input (X.liftA R.beta z)
  let t:=X.t; have ht:0<t:=p.laws.data.room.fiery; have hz:0<W:=p.laws.data.W_pos
  obtain ⟨ho,ho',hξ,G'⟩:=p.laws.data.safety
  obtain ⟨hc,hA⟩:= G' F X rfl ha hp
  have hγ:= hA hm
  simp_rw [← shine X p.laws.data.room hp]
  rcases v with i|i
  · by_cases hx : mandatory X.seeds X.B i
    · exact Eventually.of_forall fun t=> if_pos hx
    change (fun y=> ite (mandatory X.seeds X.B i) 0
      (_ * (Polar.veil (vary X (U y)) R W Y K i-1))) =ᶠ[𝓝 x] _
    suffices hY : (fun y=> veil (vary X (U y)) R W Y K i)=ᶠ[𝓝 x] fun _=>1 by
      filter_upwards [hY] with y hy; dsimp only at *
      rw [if_neg hx,hy, sub_self,mul_zero]
    let v:= focus_alarms S i
    have hq : ¬ Inside v X.seeds (300*X.B) := X.mandatory_far i hx
    have hw : X.watch v o.ξ R.beta (2*X.B) z := by
      intro i hi; have hs: 0 < gStep R.beta := inv_pos.mpr (Real.sqrt_pos.mpr p.laws.intake.positive)
      exact (he _ hi).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [o.rare]) ht.le) (inv_nonneg.mpr hs.le))
    have hv u (hp : separation v u ≤ X.B) := hγ u (clear hq (by omega)) R.beta hI.positive z (X.watch_turn hw (by omega))
    have hh := hv v (by rw [separation_self]; omega)
    rcases i with i|i|i|i|i
    · apply Eventually.of_forall; intro u
      have he : i∉ X.seeds.costs := fun h => hq (halo_spec.mpr ⟨v,mem_union_left _ (mem_union_left _
        (mem_biUnion.mpr ⟨i,h,home_storm S (.inl i)⟩)),by rw [separation_self]; omega⟩)
      change Mask.fine X.seeds X.χ i t Y=1
      unfold Mask.fine; dsimp only; rw [if_neg he]; exact pall _ _ _ (by positivity) (G.chord_nonneg _) (hh.2.1 i rfl).le
    · have hx: ContinuousAt (fun y=>wire (S.prediction Y X.k) (U y) i) x := by
        have hh : Brush j (royalty G) d (fun y=>G.mat (U y i * (S.prediction Y X.k i)⁻¹)) x := by
          simpa only [one_mul] using! offsetB (hk.atLink i) 1 (S.prediction Y X.k i)⁻¹
        exact (hh.smooth.continuousAt.sub_const (1:G.Mat)).norm.div_const _
      have hp : wire (S.prediction Y X.k) (U x) i < W*t := H.atV.symm ▸ (hh.2.2 i.2).2
      have hb : i ∉ X.seeds.aisles := fun h=> hq (halo_spec.mpr ⟨v,mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
        ⟨i,h,home_storm S (.inr (.inl i))⟩)),by rw [separation_self]; omega⟩)
      filter_upwards [hx (gt_mem_nhds hp)] with y hy
      change Mask.noise X.seeds X.χ i t W Y X.k (U y)=1
      unfold Mask.noise; dsimp only; rw [if_neg hb]; exact pall _ _ _ (mul_pos hz ht) (G.chord_nonneg _) (le_of_lt hy)
    · exact Eventually.of_forall fun i'=> (hh.2.2 i.2).1
    · exact Eventually.of_forall fun y=> hh.1
    apply Eventually.of_forall; intro y
    change Contract.charges R K Y i=1
    suffices he : i ∉ RG.flags R.p.threshold Y from if_neg fun z=>he z.2
    rw [hI.received.temp]; intro h
    obtain ⟨j,hJ,h⟩:= (flags_spec ..).mp h
    have he : separation v (S.ratio.parent j.1)≤ X.B := (Work.E04.parent_separation S.ratio i j.1).trans (by
      rw [separation_comm]; have he:= Work.E01.sep_touched j i hJ; have hp : 100≤X.B:=p.laws.data.room.sight.1; omega)
    have hh: toll Y j<t/4:= (hv _ he).2.1 j rfl
    change t<toll Y j at h; linarith
  have hb (y:E) : sprinkle (vary X (U y)) o.a R W (f' y) (X.input (X.liftA R.beta z)) K (.inr i)=X.aura (f' y) o.a i := rfl
  have hv : o.cap+(Fintype.card G.ColorIndex:ℝ)*(o.ξ/2) < o.a := by linarith only [ho',hξ]
  let B v:= ‖f' v i‖
  have hx: B x<o.a*t := by
    unfold B; rw [H.base0 p.laws.data.room hp]
    exact ((X.watch_bonds _ ht (half_pos o.rare).le hI.positive he i (show separation (atEdge S i) (atEdge S i)≤ _ by simp) (hc i)).2).trans_lt
      (mul_lt_mul_of_pos_right hv ht)
  filter_upwards [((H.budded i le_rfl).smooth.continuousAt).norm.eventually (gt_mem_nhds hx)] with y hy
  rw [hb,aura]; split
  next => exact sub_eq_zero.mpr (X.premiere (mul_pos o.large ht) _ _ hy.le)
  next => rfl
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
