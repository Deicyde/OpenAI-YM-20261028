import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Drew
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Flotsam
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet

/-!
# Solid support extension and same actual masked entry

All unforced species in sector FIRST-V proportions. Proof with scalar logs.
 Using submarginal `podium` (no positivity requirement at other V).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Shield
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*} [MeasurableSpace E]
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}
variable {X' : Coat T F} (X : Coat T F) {H : Support c} {I : Finset (Tubular f G)} (he : Intake P T X.x R)
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} (U : Cash W s μ L Q o C T R)

section density
variable {ι A : Type} [Fintype ι] [DecidableEq ι]
def lens₀ (S : Matrix ι ι ℝ) (x : Body ι) := (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp
      (-Real.log S.det/2-dotProduct (WithLp.ofLp x) (S⁻¹ *ᵥ WithLp.ofLp x)/2))
lemma magnifies (S : Matrix ι ι ℝ) (h:S.PosDef) : Poll.sweep S=volume.withDensity (fun x=> ENNReal.ofReal (lens₀ S x)) := Poll.sweep_pdf h
lemma fullFuel (S : Matrix ι ι ℝ) x : 0< lens₀ S x := by unfold lens₀; positivity
lemma bulbB {S : E → Matrix ι ι ℝ} {z : E→ Body ι} (h : Borel S) (hp : Measurable z) : Measurable (fun i=> lens₀ (S i) (z i)) := by
  have hc i : Measurable fun t=> WithLp.ofLp (z t) i := (EuclideanSpace.proj (ι:=ι) (𝕜:=ℝ) i).measurable.comp hp
  have hm : Measurable fun t=> dotProduct ((z t).ofLp) ((S t)⁻¹ *ᵥ WithLp.ofLp (z t)) := Finset.measurable_fun_sum _ fun i _=>
    (hc i).mul (Art.borel_times (Art.inverse h) (d:=fun t=> WithLp.ofLp (z t)) hc i)
  exact measurable_const.mul (Real.measurable_exp.comp ((((Real.measurable_log.comp (Art.det_m h)).neg.div_const _).sub (hm.div_const _))))
lemma recommends (S : Matrix ι ι ℝ) (h:S.PosDef) (f:Body ι → ℝ) : (∫ x, f x ∂Poll.sweep S)=∫ x, lens₀ S x * f x := by
  rw [magnifies S h]; have ht : Measurable (fun x=> lens₀ S x) := bulbB (S:=fun _ : Body ι=>S) (fun i j=> measurable_const) (z:=id) measurable_id
  rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ S x)) from ENNReal.measurable_ofReal.comp ht) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]
  exact integral_congr_ae (ae_of_all _ (fun y=> by dsimp only; rw [ENNReal.toReal_ofReal (fullFuel S y).le]; rfl))
end density

def bars (I : Finset (Tubular f G)) (X : Coat T F) (p : Molecule S) (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : ℕ) :=
    ∫ Y, (∫ z, lens₀ (Pond.circuit I X.relating) z * floating (X.wrapY Y) a R W Ñ (Pond.spill I z) (own p) l p) ∂F.order G

def seating (H : Support c) (B : ℕ) (X : Coat T F) (W a : ℝ) (l : ℕ) (p : Molecule S) (R : Rep G f) (Ñ : ChartRatio G) :=
    let Z := preps X (roster p)
    likely fun i=> bars (podium S G H B) (Z.taggedL i) p R Ñ W a l

-- unconditional extension on skeleton (test structural).
def shelter (W a : ℝ) (p : Molecule S) (R : Rep G f) (Ñ : ChartRatio G) (l : ℕ) := if Ac.Spark (areas R T l X.B) p ∧ troupe T R l X.B p
    then seating (ground R T l X.B p) X.B X W a l p R Ñ else 0
include U
lemma selfish (hx : X.x=s) (hX : X.width=o.K) (hm : X.manifest) (p : Molecule S) (H : Support c) (hP : Healthy (Pressure.temp X.x)
    (U.unionP p) X.V) (he : U.unionP p⊆H) :
    bars (podium S G H X.B) X p R Q.table W o.a Q.halo=X.attains R Q.table W o.a (own p) Q.halo p := by
  let B:=podium S G H X.B
  have ht : X.relating.PosDef := (U.laws.data.localP _ X hx hX hm).sails.fullC
  have hv : (circuit B X.relating).PosDef:= ht.submatrix Subtype.val_injective
  have hF := U.laws.data; have hg:=U.integrated X hx hX hm (own p) p
  unfold bars Coat.attains; rw [integral_prod _ hg]; apply integral_congr_ae; filter_upwards with y
  let Y:= X.wrapY y; let g (z:Air f G):= Polar.floating Y o.a R W Q.table z (own p) Q.halo p
  have hz : g=fun z=>X.body R Q.table W o.a (own p) Q.halo p (y,z) := funext fun z=> by
    refine (Polar.afterborn Y o.a R W Q.table z (own p) (show Room P S T Y.x from hx.symm ▸ U.laws.data.room) hm Q.buys p ?_).symm
    change Healthy _ (ground R T Q.halo (radiusB X.x) p) _
    have h : radiusB X.x=radiusB s := congr_arg _ hx; rw [h]; exact hP
  rw [← hz]; let W := volume (α:=Body (↥ B))
  have hζ : Measurable g := by
    rw [hz]; exact (X.body_b Q.table_exists (hx.symm ▸ U.laws.intake)
      (by rw [hx,hX]; exact U.laws.data.access) o.a (own p) Q.halo p).comp (measurable_const.prodMk measurable_id)
  symm
  refine (Pond.gathered (spill B) (spill_m B) (Pond.orbit ht.posSemidef B) (Pond.settled B) ?_ hζ).trans (Shield.recommends _ hv (fun z=>g (Pond.spill B z)))
  intro u v hu
  apply Borough.flops (X:=Y) (w:=u) (v:=v) (show Borough Y Y H u v (own p) (own p) R from ⟨Village.refl ..,(Pond.observe B).1 hu,
    fun _ _=>Iff.rfl⟩) (show Room P S T Y.x from hx.symm ▸ hF.room) Q.buys (show Intake P T Y.x R from hx.symm ▸ U.laws.intake)
  unfold ground; change p.biUnion (areas R T _ (radiusB X.x))⊆_; rw [hx]; exact he
end YM.ConnectedActivityE6.Blaze.Shield
