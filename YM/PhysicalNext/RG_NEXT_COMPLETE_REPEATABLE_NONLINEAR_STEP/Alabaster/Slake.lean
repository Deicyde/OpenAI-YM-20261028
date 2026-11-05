import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Shawl
/-!
# Angular warp weight unit estimates: same *held* tilt derivative on FULL Σ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {p μ C v D' d r D K' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} {η εK θ β a h g l b Y A q e r' : ℝ}
local notation "F₀" => (facescale (univ:Finset (Bond f)))

lemma outerZ {ι:Type} [Fintype ι] [DecidableEq ι] {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} (Ω:E→Poll.Body ι) {K:E→Matrix ι ι ℝ} {a:ι→Site c} (hp:Tablet j 0 p v K a a x) (he: Allow (K x) a m l r q) (hK:(K x).PosDef)
    (hw:∀ i,Brush j W 1 (fun y=>(Ω y).ofLp i) x) (hW:0≤ W):
    let Q:= payE l r q m; let b:= Tablet.token j p Q; let δ:= driftP j v
    let v:ℝ:=Fintype.card ι; let r:= v*(W*(b*W))*(1+(1+(δ+1)))^j
    Brush j r 1 (fun y=> dotProduct (Ω y).ofLp ((K y)⁻¹ *ᵥ (Ω y).ofLp)/2) x:= by
  intro Q b δ v r; let α y:=(Ω y).ofLp
  have hv:= Control.increase he.flatup he.weather.1.le le_rfl; have hx:= hp.inverter (isUnit_iff_ne_zero.mpr hK.det_pos.ne') hv he.disc
  have hg : 0≤δ:= hx.pos
  have hf:= Brush.trim (Brush.spree (x:=x) univ _ (fun (_:ι)=> W*(b*W)) (add_nonneg (zero_le_one (α:=ℝ)) (add_nonneg hg zero_le_one)) (fun i _=> (hw i).paints (beam_vec hx hW zero_le_one (u:=α) hw i)))
  simp only [sum_const,nsmul_eq_mul,card_univ] at hf; exact semi hf
lemma orbitSum (X : Coat T F) (I : Finset (Bond f)) {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E} (V:E→ Config G c) (U:E→Directions G f) {z:Air f G} (hc : Clutch X z a β p x j V U (fun y=> course X q β z (V y)))
    (hp : Rotator P L η r D Y (vary X (V x))) (hq : Tablet j 0 v d (fun t=> (vary X (V t)).plate) (along S) (along S) x)
    (hV : ∀ i,Brush j b 1 (fun y=>voltage (vary X (V y)) i) x) (hb : 0 ≤ b) (he : 0 ≤ W) (h : ((gStep β)⁻¹*(p+(b+b)))+facescale I z ≤ W) :
    let m:=tubularPrice G L; let A:=payE η r D m; let Z:= payE (retain η r D) (D⁻¹/2) (1+A) m
    let F:= facePrice j X.B m v A; let r:= driftP j (driftP j d)
    Brush j ( (I.card*Fintype.card G.ColorIndex:ℕ)*(W*(Tablet.token j F Z * W))*(1+(1+(r+1)))^j) 1 (fun y=> draftI X I β q (V y) z) x := by
  intro m A Z f r'; let Y t := swim (lensS I G) (course X q β z (V t)); have hi := own_mat hp I
  have hh := outerZ Y (feast X I V hp hq) hi (hp.fullC.submatrix Subtype.val_injective) (fun i=> (meager hc I hV hb i).climb h le_rfl) he -- inspect
  dsimp only at hh; rw [Fintype.card_coe, show (lensS I G).card=I.card*Fintype.card G.ColorIndex by simp [lensS]] at hh -- dependent rewrite!
  exact hh
end YM.PhysicalNext.Repeat.Alabaster
