import YM.UVExtension.Span.Overseas
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (qV:StableR v R)
variable (Δ:κ→Directions G f) -- actual held displacement at test. no norm when prices all Compass later
open Silica Flux WithLp MeasureTheory
open Polar Silica Eider
-- arrows.
variable (hx : ∃ r:ℝ,∀ᶠ i in qq, ‖Δ i‖≤ r)
include h p he hK hx
variable (Y':κ→ Config G f)
open Mask
include qV
variable (J:κ→ Finset ℕ)
open Raw Mask
lemma mini (P:Miniature c f): Walt qq τ k (fun n b i=> Polar.whelp (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) Q.table (mobil A s U.K χ T t Δ M Y n b i) (Y' n) P):=by
   let H i := Abide s χ U.K T M t i true; let μ:= mobil A s U.K χ T t Δ M Y
   rcases P with P|i|i
   · let r i:= Shell.Inside (rowSite S P) (H i).seeds (200*radiusB s); let W i:= (H i).booth (rowSite S P)
     have hp:= (parka p h he hK Δ hx (2*U.a) W).times (p.speckle h he hK qV Δ hx Y' P.1 P.2 true)
     apply (Walt.choose r (Walt.ready 0) ((((Walt.stamp ((qV.pricesBet h).continuous continuous_neg)).times (Walt.ready orientation)).times (hp.sums (p.costsW h he hK P.1 P.2 (p.pulses h he hK)))).excuse _)).same; filter_upwards with n b; filter_upwards with i; unfold whelp hover; simp only [H,r,Abide,Hat.order,Coat.B,vary,W,booth,Sum.elim_inl]; congr 1
   · exact Walt.choose (fun n=>Coat.voyage (H n).seeds (200*radiusB s) i) (Walt.ready _) ((logPins p h he hK i).excuse _)
   apply (Walt.choose (fun n=> i∉ (H n).plaza ((H n).seeds.dome (304*radiusB s))∧ (H n).Hot i) ((p.cliffA h he hK Δ hx i).excuse _) (Walt.ready 0)).same; filter_upwards with n b; filter_upwards with i; unfold whelp solo; simp only [H,Abide,vary,Hat.order,Coat.B,Coat.Hot,plaza,Sum.elim_inr]
lemma tokenK (P:ℕ): Walt qq τ k (fun n b i=> Polar.sheath (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) (mobil A s U.K χ T t Δ M Y n b i) (Y' n) P):=by
   let W i:=(Abide s χ U.K T M t i true).plaza (forcedFoot S.ratio 0 (radiusB s) (R (t i true)) P)
   refine ((Walt.stamp ((qV.real_arrays h P Y').1)).times (p.parka h he hK Δ hx (2*U.a) W)).same ?_
   filter_upwards with i n; filter_upwards with z; unfold Polar.sheath W
   change _ *enforce _ _ _ (plaza _ (forcedFoot _ _ (radiusB s) _ _))=_
   rw [(p.core qV.toKept (t i n) (t i true) (radiusB s) 0).1]; rfl
lemma petals (P:LogLetter c f): Walt qq τ k (fun n b i=> Polar.frost (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) (mobil A s U.K χ T t Δ M Y n b i) (Y' n) P):=by
   let W i:=(Abide s χ U.K T M t i true).plaza (Raw.space (T (t i true)) 0 (radiusB s) (R (t i true)) P)
   refine ((nesting p h he qV Y' P).times (p.parka h he hK Δ hx (2*U.a) W)).same ?_
   filter_upwards with i n; filter_upwards with z; unfold Polar.frost W
   change _ *enforce _ _ _ (plaza _ (Raw.space _ _ (radiusB s) _ _))=_
   rw [(p.receipts qV.toKept (t i n) (t i true) (radiusB s) 0).1]; rfl
lemma orange (P: Panic c f): Walt qq τ k (fun n b i=> Polar.veil (vary (Abide s χ U.K T M t n b) (Y n i)) (R (t n b)) w (Y' n) (J n) P):=by
   let X n b y:= vary (Abide s χ U.K T M t n b) (Y n y)
   have h {a:κ→ℝ} (f: κ→Bool→E→ℝ){b:ℝ}(hp:∀ i, 0≤a i∧ a i≤b)(hx:∀ n b y,f n b y=a n): Walt qq τ k f:=by simp_rw [show f=(fun i b y=> a i) from funext fun i=>funext fun j=>funext fun y=>hx ..]; apply Walt.twin b 1; filter_upwards with i; exact ⟨(Brush.certified zero_le_one _).climb (by rw [Real.norm_of_nonneg (hp _).1]; exact (hp _).2) le_rfl,rfl⟩
   rcases P with P|i|i|i|i
   · exact tickF (χ:=χ) he Y' (fun i=>(M i).seeds) (fiery G s S.patch.L) _
   · exact ticksB (χ:=χ) he Y' (fun i=>(M i).seeds) (fiery G s S.patch.L) (fun n=>(M n).tag) _
   · exact h _ (a:=fun j=> Tags.pinMass (Y' j) (M j).tag i) (fun j=>⟨Tags.pin_nn (Y' j) (M j).tag i,Tags.pin_cap (Y' j) (M j).tag i⟩) (fun n b y=>rfl)
   · exact h _ (a:=fun j=> Tags.siteMass (Y' j) (M j).tag i) (fun j=>⟨Tags.site_nn (Y' j) (M j).tag i,Tags.site_cap ..⟩) (fun n b y=> rfl)
   apply h _ (a:=fun j=> Contract.charges (R (t j true)) (J j) (Y' j) i) (b:=1); intro v; rcases Contract.ordinary (R (t v true)) (J v) (Y' v) i with h|h<;>rw [h]<;>simp
   exact fun n b y=> congr_fun (qV.toKept.charged (t n b) (t n true) (J n) _) _
lemma warning (P: WarningAt c f): Walt qq τ k (fun n b i=> Polar.sprinkle (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) w (mobil A s U.K χ T t Δ M Y n b i) (Y' n) (J n) P):=by
   let X i:=Abide s χ U.K T M t i true
   rcases P with p'|i
   · exact Walt.choose (fun n=> mandatory (M n).seeds (radiusB s) p') (Walt.ready _) (((p.parka h he hK Δ hx (2*U.a) (fun i=> (X i).plaza (halo (radiusB s) (districts S p')))).times ((orange p h he hK qV Δ hx Y' J p').minus (Walt.ready 1))).excuse _)
   apply (Walt.choose (fun n=> (X n).Hot i∧ i∉ (X n).plaza ((M n).seeds.dome (304*radiusB s))) (((pools p h he hK Δ hx i U.a).minus (Walt.ready 1)).excuse _) (Walt.ready 0)).same; filter_upwards with n b; filter_upwards with x; unfold sprinkle aura; simp only [X,Abide,vary,Hat.order,Coat.B,Coat.Hot,plaza,Sum.elim_inr]
lemma logsP (P: LogIndex c f): Walt qq τ k (fun n b i=> logMoment (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) Q.table (mobil A s U.K χ T t Δ M Y n b i) (Y' n) (course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n i)) P):=by
   rcases P with i|i|i; exact petals p h he hK qV Δ hx Y' i; exact mini p h he hK qV Δ hx Y' i; exact pledge p h he hK qV Δ hx i
lemma cooks (P:Head S): Walt qq τ k (fun n b i=> Polar.ember (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) w Q.table (mobil A s U.K χ T t Δ M Y n b i) (Y' n) (course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n i)) (J n) Q.halo P):=by
   rcases P with i|i|i|i
   · exact Walt.choose (fun (_:κ)=> Packets.connected S Q.halo (radiusB s) i) ((p.nozzle h he hK qV Δ hx Y' J i).excuse _) (Walt.ready _)
   · exact tokenK p h he hK qV Δ hx Y' i
   · exact (logsP p h he hK qV Δ hx Y' i|>.exponential).minus (Walt.ready 1)
   exact warning p h he hK qV Δ hx Y' J i
-- floating: atmosphere transformed mobility. frees & rolling Boltz. Does not probe masks
lemma standsP (P:Molecule S): Walt qq τ k (fun n b i=> Polar.floating (vary (Abide s χ U.K T M t n b) (Y n i)) U.a (R (t n b)) w Q.table (course (Abide s χ U.K T M t n b) A (R (t n b)).beta (prize s χ U.K T R M t Δ n b) (Y n i)) (J n) Q.halo P):=by
   let f i:=(Abide s χ U.K T M t i true).input (Δ i); refine (caraffa P _ (fun i (_:i∈P)=> cooks p h he hK qV Δ hx f J i)).same ?_
   filter_upwards [rights p h he hK Δ] with i hz b; have hp:= hz b
   filter_upwards [hp.patch] with n hn; unfold Polar.floating; rw [hp.moving]
   have ht:= H (t i b); let v:=(prize s χ U.K T R M t Δ i b); let X:=Abide s χ U.K T M t i b; let Y':=(vary X (Y i n)); have hm:Intake _ _ Y'.x (R (t i b)):= ht.laws.intake
   refine Finset.prod_congr rfl fun j _=>?_ ; unfold f
   change _=Polar.ember _ _ _ _ _ _ (X.input (Δ i)) _ _ _ _
   have he':X.input (worldZ X _ v)=X.input (Δ i):= congr_arg (X.input) (rent_bill (R (t i b)).beta X ht.laws.intake.positive _)
   rw [←he']; exact (plastic hn hp.pulse).reeled (show Room _ S _ Y'.x from ht.laws.data.room) w Q.table _ _ hm j _
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.standsP
