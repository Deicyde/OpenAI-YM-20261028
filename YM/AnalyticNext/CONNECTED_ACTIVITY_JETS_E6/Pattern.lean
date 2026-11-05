import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Chintz
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

def fringe (X : Coat T F) (W a : ℝ) (p : Molecule S) (R : Rep G f) (Ñ : ChartRatio G) (l : ℕ) :=
    ∫ z, shelter (X.rinse z) W a p R Ñ l ∂(Measure.pi fun _:Site c=>G.probHaar)
lemma frieze (X : Coat T F) (W a : ℝ) (p : Molecule S) (R : Rep G f) (Ñ : ChartRatio G) (l : ℕ) :
    GaugeInvariant (fun V=> fringe (vary X V) W a p R Ñ l) := by
  intro z V
  let f:= MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i))
  let U:=(Measure.pi fun _:Site c=>G.probHaar)
  have hp : MeasurePreserving f U U := measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right G.probHaar (z i))
  let Y:= vary X V; dsimp only [fringe]; rw [← hp.integral_comp' (fun z=> shelter (Y.rinse z) W a p R Ñ l)]
  apply integral_congr_ae; filter_upwards with u; have ht : gauge u (gauge z V) = gauge (f u) V := by
    funext i; unfold Lattice.gauge; change _= (u _*z _)* V _* (u _*z _)⁻¹; group
  unfold vary rinse; simp_rw [ht]; rfl
lemma seam (p : Molecule S) (hX : X.x=s) (hk : X.width=o.K) : Measurable (fun y=> fringe (vary X y) W o.a p R Q.table Q.halo) ∧
    LocalOn (H.unionP p) (fun y=> fringe (vary X y) W o.a p R Q.table Q.halo) := by
  let Y:= Measure.pi fun _: Site c=> G.probHaar
  have hz := H.laws.data; have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
  have ht : ShellAccess S G X.x W X.width o.γ := by rw [hX,hk]; exact hz.access
  constructor
  · have hp : Measurable fun (a:Config G c × (Site c → G.El))=> gauge a.2 a.1 := by
      refine measurable_pi_lambda _ fun i=> ?_; dsimp only [Lattice.gauge]; fun_prop
    exact (((shelterB X ht he Q.table_exists o.a p Q.halo).comp hp).stronglyMeasurable.integral_prod_right' (ν:=Y)).measurable
  intro U V hu; unfold fringe; apply integral_congr_ae; filter_upwards with z; refine Shield.shelters X he o.a W p Q.table (hX.symm ▸ hz.room)
    Q.buys (gauge z U) (gauge z V) ?_; intro i hi hj; unfold Lattice.gauge; have ht : ground R T Q.halo X.B p=H.unionP p := by unfold Coat.B; rw [hX]; rfl
  rw [ht] at hi hj; rw [hu i hi hj]

lemma rainbow (p : Molecule S) (hΘ : Oboe H j v B k A b Ξ) (hX : X.x=s) (hv : X.width=o.K) (hp : X.χ=χ) (he : (roster p).flags=∅)
    (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (hM : Mode V x j v) (hz : V x=X.V) : ∀ᶠ y in 𝓝 x,
      fringe (vary X (V y)) W o.a p R Q.table Q.halo = shelter (vary X (V y)) W o.a p R Q.table Q.halo := by
  let K:= (planted X p); let Y t y:= vary (K.taggedL t) (V y); have ht:= H.laws.data
  have hf t: ∀ᶠ y in 𝓝 x,Hue (Y t y):= eventual_hue (hΘ.flow F (K.taggedL t) hX hp hv (planted_valid X p) E V x hz hM)
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
lemma scenic (p : Molecule S) (hΘ : Oboe H j v B k A b Ξ) (hB : 0≤B) (hX : X.x=s) (hv : X.width=o.K) (hp : X.χ=χ) (he : (roster p).flags=∅)
    (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (hM : Mode V x j v) (hz : V x=X.V) :
    Brush j (B*Ξ.meant p k) 1 (fun i=> fringe (vary X (V i)) W o.a p R Q.table Q.halo) x := by
  apply (Oboe.castles hX hv p hΘ hB he hp hy hM hz).shimmy (rainbow p hΘ hX hv hp he hy hM hz)
lemma vows (p : Molecule S) (hΘ : Oboe H j v B k A b Ξ) (hV : 0≤v) (hX : X.x=s) (hv : X.width=o.K) (hp : X.χ=χ) (he : (roster p).flags=∅) :
    H.emerging X p=masked (Pressure.temp s) (H.unionP p) (fun y=> fringe (vary X y) W o.a p R Q.table Q.halo) X.V := by
  by_cases hh: Healthy (Pressure.temp s) (H.unionP p) X.V
  · have hx := (rainbow p hΘ hX hv hp he hh (x:=(0:ℝ)) (show Mode (fun _:ℝ=> X.V) _ j v from ⟨hV,fun i=> a_oneB G _ hV⟩) rfl).self_of_nhds
    rw [agreement X H hX hv p he,hX,RG.masked_eq _ _ _ _ hh,RG.masked_eq _ _ _ _ hh]; exact hx.symm
  rw [agreement X H hX hv p he,hX,RG.masked_ne _ _ _ _ hh,RG.masked_ne _ _ _ _ hh]
end YM.ConnectedActivityE6.Blaze.Stained
