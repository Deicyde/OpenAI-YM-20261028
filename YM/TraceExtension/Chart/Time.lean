import YM.TraceExtension.Chart.Scalar
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate Shelves
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
variable {X:Axis→ Logs C 5}(hp:∀ i,TravelsC (𝓛:Filter (ℕ×ℕ)) (exhibit t i) (Readout t i) (X i).v (X i).x)
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
open Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
open Spec TraceExtension Org Next.Rank Perch
-- actual readings.Annotation.One projection on Wilson prescription.
variable {X₁:Spec.Algebra S}(ho': Spec.Locals X₁ H'.spin)
include h in
lemma leaderB (R:S.Field 4) (a:(Bel C.book).Hierarchy) (v:ℕ→ℝ)(hp:∀ i,0<v i)(hz:∀ᶠ i in atTop,∃ x:CP,ZoomValue J v R i=ScalarP C x) (hx:Tendsto (ZoomValue J v R) atTop (𝓝 ((4*d2 G) • OScale C.book))):∃ d e:ℕ→ℝ, (∀ᶠ i in atTop,(J.U i 4).symm ((J.r i)^(4:ℕ) • R)=ScalarP C (![e i,d i]))∧ Tendsto (fun i=> v i*d i) atTop (𝓝 (d2 G))∧Tendsto (fun i=> v i*e i) atTop (𝓝 0):=by
    obtain ⟨Y,hY⟩:= (ScalarP C).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (Scalar_inj h a)); let f(i):= Y (ZoomValue J v R i); let y:= (![0,d2 G]:CP); have hp' : ScalarP C y=(4*d2 G) • OScale C.book:=by change (0:ℝ) • ((Bel C.book).unit 4)+d2 G • (((4:ℝ) • OScale C.book):(Bel C.book).Field 4) = _;rw [zero_smul,zero_add,smul_smul,mul_comm (d2 G) _]
    have he:Tendsto f atTop (𝓝 y):=by
         have he := Y.continuous_of_finiteDimensional.continuousAt.tendsto.comp hx; rw [← hp'] at he; rw [show Y ((ScalarP C) y)=y from LinearMap.congr_fun hY y] at he; exact he
    let d'(j)(i):= (v i)⁻¹ * f i j; have hD(j):Tendsto (fun i=> v i*d' j i) atTop (𝓝 (y j)):= (tendsto_pi_nhds.mp he j).congr fun i=>by unfold d'; rw [← mul_assoc,mul_inv_cancel₀ (hp i|>.ne'),one_mul]
    refine ⟨d' 1,d' 0, hz.mono fun i hi=>?_, hD 1,hD 0⟩; obtain ⟨x,hx⟩:=hi
    have hu:x=f i:=by unfold f; rw [hx,show Y _=x from LinearMap.congr_fun hY x]
    let F:=(J.U i 4).symm; let g:=v i; rw[show (![d' 0 i,d' 1 i]:CP)=g⁻¹ • x from ?_,(ScalarP C).map_smul,← hx];
    · unfold ZoomValue; change F ((J.r i)^ (4:ℕ) • R)=g⁻¹ • F ((g*_ ) • R); rw [mul_smul g,show ∀ x:S.Field 4,F (g • x)=g • F x from fun x=> (F.toLinearMap.restrictScalars ℝ).map_smul ..,inv_smul_smul₀ (hp i).ne']
    ext1 k; rw [hu];fin_cases k<;>rfl
structure Scribe (Q: Extraction.Order)(J:Scaling S)(V:∀ i,Vane C i)(Z:Arch C)(A':Spec.Algebra S) (𝓛: Ultrafilter (ℕ×ℕ)) (H':S.Hierarchy)(H:(Climb.Bel C.book).Hierarchy): Prop where
    grows: Tendsto (BQ Z V) atTop atTop
    clock:Tendsto (fun i=>LogZoom J i/BQ Z V i) atTop (𝓝 G.slopeConstant⁻¹)
    meters : ∃ Y,Gondola Q H J 𝓛 V Y
    monorail: StarPath Q H J H' 𝓛
    gallery(T:Table C.book)(h:T.Hierarchy): T.respects S → ∃ d e:ℕ→ℝ,(∀ᶠ i in atTop,(J.U i 4).symm ((J.r i)^(4:ℕ) • TraceExtension.theta T A'.energy)=ScalarP C (![e i,d i])) ∧ Tendsto (fun i=> (BQ Z V i)*d i) atTop (𝓝 (d2 G)) ∧ Tendsto (fun i=>BQ Z V i*e i) atTop (𝓝 0)
    main : Tendsto (fun k=>Year J k (Next.UVStress.reCenter S A'.energy)) atTop (𝓝 (Shelves.materialB C none))
    goal (T:Table C.book): Tendsto (ZoomValue J (BQ Z V) (TraceExtension.theta T A'.energy)) atTop (𝓝 ((4*d2 G) • OScale C.book))
include ho' hq' hu h hb Hδ hr hA hM hT P θ K hz hq ht
-- SOS full.Conservation.marvel
include HF hP ho
lemma Store_l (Tx:Marvel (Climb.Bel C.book) H.spin (materialB C none) P₁)(hc:CellHyp C F): Scribe F J V Z X₁ 𝓛 H' H:=by
    have he(T:Table C.book):= july P h θ K ht hM hT hb hu hz Hδ hr hA hq H' HF hq' ho'.derivatives hP ho ho'.rights X₁ rfl ho' Tx hc T
    refine ⟨?_,zoom_BQ P h θ hb hz hq,⟨_,hq⟩,hq',fun T h₀ h₁=> leaderB h (TraceExtension.theta T X₁.energy) H _ (fun i=> measured hb P hz _) (payload h (H:=H) H' ho' h₁ h₀ _ ((hq'.units 4).mono fun i hi=>hi.1)) (he T), ?_, he⟩
    · exact (cure hb P hz h).comp ((Sstar A).comp hq.growth)
    have hr:= reveals P h θ K ht hM hT hb hu hz Hδ hr hA hq H' HF hq' ho'.derivatives hP ho ho'.rights hc
    exact (year_spec H' H h ho'.derivatives hP ho _ (flavor X₁ H' ho') ho'.rights hr hq'.approach Tx).1
end YM.Trace.Over
#print axioms YM.Trace.Over.Store_l
