import YM.TraceExtension.Chart.Orr
import YM.TraceExtension.Centered
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
open Set UVNext.FreeStress Org Spec Table TraceExtension
-- centered.IN UR
lemma flavor(X:Spec.Algebra S)(he:S.Hierarchy)(h:Spec.Locals X he.spin): Marvel S he.spin (reCenter S X.energy) X.derivatives:=by
    let J:=X.energy;let V:= X.turns;let W:= X.derivatives; let R:= reCenter S J
    have he' := h.conserved
    have hs: J ∈ SymSpace he.spin:=by
        refine sym_mem.mpr ⟨he'.symmetric,he'.real,fun u i j=>?_⟩; rw [← h.spots.signed,h.spin u.ortho i j];
        rfl
    have hu : R∈ KernelSpace he.spin:= enters he _ hs
    refine ⟨⟨hu, ⟨(sym_mem.mp (kernel_mem.mp hu).1).1,(sym_mem.mp (kernel_mem.mp hu).1).2.1,fun i=>?_⟩⟩,V.lie,?_⟩
    · refine Eq.trans (b:=∑ j:Axis,W.deriv 4 j (J j i)) (Finset.sum_congr rfl (fun j _=> ?_)) (he'.divergence i)
      change W.deriv 4 j (centering S 4 _)=_; rw [value_center,map_sub,map_smul,W.unit_drop he.laws h.derivatives he.smooth]
      simp; rfl
    let t(i j:Axis):= -(expectation S 4 (J i j))
    have hp : ∀ i j,t i j=t j i:=by intro i j; unfold t; rw[show J i j=J j i from h.conserved.symmetric i j]
    have hc : R=J+fossil t:=by funext i j; change centering S 4 (J i j)=J i j+t i j • _;rw[value_center]; unfold t; rw [neg_smul];abel
    rw [show reCenter S X.energy=_ from hc]; exact add_unit he h.charges t hp
lemma center_plus(X:Spec.Algebra S) (T:Table C.book): ∃ c:ℂ, stressTrace (reCenter S X.energy)=TraceExtension.theta T X.energy+c • S.unit 4:=by
    let v:= stressTrace X.energy; let f:=S.unit 4; refine ⟨euclideanVEV S T v- expectation S 4 v,?_⟩
    have he: stressTrace (reCenter S X.energy)=centering S 4 v:=by unfold v stressTrace; rw [map_sum]; rfl
    rw [he]; change centering S 4 v= v - _+ _; rw[value_center,sub_smul];abel
abbrev b0(G:Gauge):= 11*G.casimir/(48*Real.pi^2)
lemma beta_eq(G:Gauge): G.slopeConstant=2*b0 G:=by unfold b0 Gauge.slopeConstant;ring
abbrev d2 (G:Gauge):=forceR G
lemma force_b (G:Gauge): d2 G= -b0 G/2:=by unfold d2 forceR; rw [beta_eq];ring
abbrev ZoomValue(X: Scaling S)(B : ℕ → ℝ)(v:S.Field 4)(k:ℕ):= ( (X.U k 4).symm ( (B k * X.r k^ (4:ℕ)) • v))
lemma trace_Year(R:S.Stress)(p:ℕ→ℝ)(k:ℕ): p k • ∑ j:Axis, (Year J k R) j j=ZoomValue J p (stressTrace R) k:=by
    unfold ZoomValue stressTrace; let U:=(J.U k 4).symm; rw [Finset.smul_sum,Finset.smul_sum,map_sum]; exact Finset.sum_congr rfl (fun i _=> by change p k • (J.r k^ (4:ℕ) • U _)=U ((p k*J.r k^ (4:ℕ)) • _); rw [smul_smul]; exact (U.toLinearMap.restrictScalars ℝ|>.map_smul ..).symm)
lemma zoom_sub (x y:S.Field 4) (k:ℕ)(p:ℕ→ℝ): ZoomValue J p (x-y) k= ZoomValue J p x k-ZoomValue J p y k:=by unfold ZoomValue; rw[smul_sub,map_sub]
include H' hz P hb h hq hq' θ
lemma shift_unit (c:ℂ): Tendsto (ZoomValue J (BQ Z V) (c • S.unit 4)) atTop (𝓝 0):=by
    let F:= Bel C.book; let h(k):= BQ Z V k* J.r k^(4:ℕ); have ht:=band_cost P ‹G.Simple› θ hb hz hq
    have he:Tendsto (fun k=> h k • (c • F.unit 4)) atTop (𝓝 0):= by simpa only[zero_smul] using! ht.smul (show Tendsto (_root_.Function.const ℕ (c • F.unit 4)) atTop (𝓝 (c • F.unit 4)) from tendsto_const_nhds)
    refine he.congr' ?_; filter_upwards [hq'.units 4] with k hk; unfold ZoomValue; let U:= J.U k 4; change _= U.symm (h k • (c • _)); apply U.injective; rw[LinearEquiv.apply_symm_apply,show U _=h k • U (c • F.unit 4) from (U.toLinearMap.restrictScalars ℝ).map_smul ..,map_smul]; exact congr_arg _ (congr_arg _ hk.2)
-- trace read earned for all chambers with these identities & representatives.
variable (o:S₁.Orientation H'.spin)
variable (X':Spec.Algebra S)(Hσ: X'.derivatives=S₁)(Hx:Spec.Locals X' H'.spin)(hT':Marvel (Bel C.book) H.spin (materialB C none) P₁)
include X' Hx hT' Hσ ht hM hT K HF Hδ hr hA ho hu hJ hP o
variable (hc:CellHyp C F)
include hc
lemma july (T:Table C.book): Tendsto (ZoomValue J (BQ Z V) (TraceExtension.theta T X'.energy)) atTop (𝓝 ((4*d2 G) • OScale C.book)):=by
    have hr:= reveals P h θ K ht hM hT hb hu hz Hδ hr hA hq H' HF hq' hJ hP ho o hc
    let v:= reCenter S X'.energy; let u:= TraceExtension.theta T X'.energy
    have ht:= year_spec H' H h hJ hP ho v (Hσ ▸ flavor X' H' Hx) o hr hq'.approach hT'
    obtain ⟨x,hx⟩:= center_plus X' T; have he:u=stressTrace v- x • S.unit 4:= by rw[show stressTrace v=u+_ from hx,add_sub_cancel_right]
    have hM:= shift_unit P h θ hb hz hq H' hq' x; have hH:= ht.2.sub hM; rw [sub_zero] at hH; exact hH.congr (fun k=> by rw[trace_Year]; change _=ZoomValue _ _ u k; rw [he,zoom_sub])
end YM.Trace.Over
