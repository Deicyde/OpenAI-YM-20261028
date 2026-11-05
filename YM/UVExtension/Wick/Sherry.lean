import YM.UVExtension.Wick.Beryl
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Gio

/-! # Unforced occurrences with gauge-invariant germ. Price at masked field!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Stained
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}

lemma uv_rainbow (p : Molecule S) (hΘ : ∀ t,Glass P ((planted X p).taggedL t) V x j W) (hX : X.x=s) (hv : X.width=o.K) (he : (roster p).flags=∅)
    (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) : ∀ᶠ y in 𝓝 x,
      fringe (vary X (V y)) W o.a p R Q.table Q.halo = shelter (vary X (V y)) W o.a p R Q.table Q.halo := by
  let K:= (planted X p); let Y t y:= vary (K.taggedL t) (V y); have ht:= H.laws.data
  have hf t: ∀ᶠ y in 𝓝 x,Hue (Y t y):= eventual_hue (hΘ t)
    (ht.localP F (K.taggedL t) hX hv (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  let Z:= vary X (V y)
  let a (z:Coat T F):= shelter z W o.a p R Q.table Q.halo
  have hF z : a (Z.rinse z)=a Z := by
    unfold a shelter; rw [show (Z.rinse z).B=Z.B from rfl, show Z.B=radiusB s from congr_arg _ hX]; split
    next h =>
      apply congr_arg likely; funext q
      let I:=podium S G (H.unionP p) (radiusB s); let b X:= bars I (F:=F) (T:=T) X p R Q.table W o.a Q.halo
      change b ((preps (vary X (gauge z (V y))) (roster p)).taggedL q)=b ((preps Z (roster p)).taggedL q)
      have ht k : b (vary (K.taggedL q) k)=b ((preps (vary X k) (roster p)).taggedL q) := spices p H X hX k k (fun _ _ _=>rfl) hy he q
      unfold Z; rw [← ht, ← ht]
      change b ((Y q y).rinse z)=b (Y q y)
      unfold b I; rw [← chargedU];
      apply Stained.coastal (show Intake P T (Y q y).x R from hX.symm ▸ H.laws.intake)
        (show ShellAccess S G (Y q y).x W (Y q y).width o.γ from (by change ShellAccess S G X.x W X.width o.γ; rw [hX,hv]; exact H.laws.data.access))
        _ _ _ z Q.table_exists _ _ (hh q)
      · apply mul_pos o.large; unfold Coat.t; change 0<Pressure.fiery G X.x _; rw [hX]; exact H.laws.data.room.fiery
      unfold Coat.t; change 4*_ * Pressure.fiery G X.x _ < _; rw [hX,H.laws.data.funds.length_eq]; exact H.laws.data.covers
    next => rfl
  change (∫ z, a (Z.rinse z) ∂ _) = a Z; simp_rw [hF]; simp
end YM.ConnectedActivityE6.Blaze.Stained
