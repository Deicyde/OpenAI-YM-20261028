import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Helices
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Slake
/-!
# Uniform charge of lifted quadratic. Reading after Gram, for any finite lattice `f`.
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
-- fixed-C constants, rectangle ON covers. Assembled by subrank only.
set_option maxHeartbeats 400000 in
lemma paysDia (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {V u : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (_hp : Rate G L (-(1/2)) u) (hv : ∀ᶠ x in atTop,0≤V x)
    {η r S' : ℝ} (Y : ℝ) (p:Torch η r S') (d : ℝ) : ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ S.patch=D → ShellAccess S G x W K γ →
      ∀ (R:RG.Rep G f), Intake P T x R → ∃ b:ℝ,0≤b∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E→ Config G c) (F:Forest S.ratio) (X:Coat T F) (z:Air f G), X.x=x → X.width=K → X.χ=χ → Port P L η r S' Y X → Mode U y j (V x) →
        Clutch X z a R.beta (|u x|) y j U (fun i=> steer X d (worldZ X R.beta z) (U i)) (fun i=>course X d R.beta z (U i)) →
        ∀ I, Brush j (b*(facescale (univ : Finset (Bond f)) z)^2) 1 (fun y=> draftI X I R.beta d (U y) z) y:= by
  obtain ⟨A,D',hA,hR,hT⟩:= Blaze.vines P L D hD K γ W χ j p h hv 1
  obtain ⟨H,hH,hP⟩:= bounded_stencils P D hD
  let m:= carat D P L 0 H; let v:= m*m+1; let k:=tubularPrice G L; let b:=payE η r S' k
  let w x:= kernelGrowth (radiusB x) G (V x); let W' x:=driftP j (w x+w x); let g x:=facePrice j (radiusB x) k v b
  let C x:= |Tablet.token j (g x) (payE (retain η r S') (S'⁻¹/2) (1+b) k)|; let J x:=|(1+(1+(driftP j (W' x)+1)))^j|
  filter_upwards [hT] with x hx c f S T hh hv hS R hp
  let v' := 1+ (gStep R.beta)⁻¹*(|u x|+(|A x|+|A x|))
  let n : ℕ:= Fintype.card (Bond f)*Fintype.card G.ColorIndex
  have he:0<R.beta:=hp.positive; have hb : 0 ≤ (gStep R.beta)⁻¹:= inv_nonneg.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _)); have hs : 0≤v':=by unfold v'; positivity
  refine ⟨n*(v'*(C x*v'))*J x,by dsimp only [C,J]; positivity,?_⟩; intro E _ _ y U F X z hX hK hχ h h' hB' I
  have hΓ:= h.sails; have hXt : X.x=x:=hX; have hL:Rotator P L η r S' Y (vary X (U y)):= by rw [hB'.tipped]; exact hΓ
  have ht' := Gate.plates X D hv hh.length_eq hΓ.room h' H hH (hP _ _ S T hv hh.funds) (le_refl 0) P.top.width_pos
  have ha : (vary X (U y)).manifest:= by rw [hB'.tipped]; exact h.placed
  have hv' := hx c _ S T hv hh hS F X E U y hX hK hχ h' ha hL.scale
  let p:= facescale (univ:Finset (Bond f)) z; have hh:1≤p:=(Flux.expenses _ z).1
  let X' := v'*p
  have he: 0 ≤ X':= mul_nonneg hs (zero_le_one.trans hh)
  apply (orbitSum X I U _ hB' hL ht' hv'.1 (abs_nonneg _) he ?_).climb _ le_rfl -- F' notation W
  · apply (add_le_add_right (lo_phi I z) _).trans; have hv:= mul_nonneg hb (add_nonneg (abs_nonneg (u x)) (add_nonneg (abs_nonneg (A x)) (abs_nonneg (A x))))
    unfold X' v'; rw [add_mul,one_mul]; exact le_trans (add_le_add_left (le_mul_of_one_le_right hv hh) _) (le_of_eq (add_comm ..))
  rw [show X.B=radiusB x from congr_arg _ hX]
  have hX':↑(I.card*Fintype.card G.ColorIndex:ℕ)≤ (n:ℝ):= by unfold n; gcongr; exact Finset.card_le_univ I
  let X'' := (1+(1+(driftP j (W' x)+1)))^j
  change _*(X'*(Tablet.token j (g x) (payE (retain η r S') (S'⁻¹/2) (1+b) k)*X')) * X'' ≤ _*p^2
  apply (le_abs_self _).trans
  let C' := C x
  have hC : 0 ≤ C':= abs_nonneg _; have hp':0≤|X''|:=abs_nonneg _
  simp_rw [abs_mul]; rw [abs_of_nonneg he,abs_of_nonneg (Nat.cast_nonneg _)] -- simp_rw abs_mul token may unfold?
  change ↑(_ : ℕ)*(X'*(C'*X')) * |X''| ≤ _
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX' (mul_nonneg he (mul_nonneg hC he))) hp').trans_eq
  unfold X'; change _ = n*(v'*(C'*v')) * |X''| * p^2; ring
end YM.PhysicalNext.Repeat.Alabaster
