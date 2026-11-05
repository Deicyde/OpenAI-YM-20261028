import YM.TraceExtension.Shelves.Dream
import YM.TraceExtension.Slate.Garnet
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate
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
-- Fast absolute survives converting at these moving measured points
lemma swiftC {V:Type*}[NormedAddCommGroup V]{A':Schedule}{f:ℕ→ V}(h:Fast A' f): Tendsto f atTop (𝓝 0):=by
    obtain ⟨b,hb,h⟩:=h; apply h.trans_tendsto
    exact Real.tendsto_exp_atBot.comp (by simpa [mul_comm b] using! A'.divergent.const_mul_atTop_of_neg hb)
lemma capped {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{A':Schedule}{f:ℕ→ V}{g:ℕ→ℝ}(h:Fast A' f)(hp:Calms A' 0 g): Fast A' fun i=>g i • f i:=by
    have hx: Fast A' (fun i=> ‖f i‖):= h.smaller (isBigO_norm_left.mpr (isBigO_refl ..)); refine (hx.mul hp).smaller (isBigO_iff.mpr ⟨1,Eventually.of_forall (fun i=>?_)⟩); simp [norm_smul, mul_comm]
lemma hawker (A':Levels G): Calms A'.S 0 A'.clock.hatBeta:=by
    let f(i:ℕ):=A'.S.scale i; suffices h : Calms A'.S 0 f from ((show Calms _ 0 (fun _=> A'.clock.bar) from fun a h=> factor_const _ _ _ h).add (fun a ha=> (h _ ha).const_mul_left G.slopeConstant))
    intro a ha;
    refine (isBigO_iff.mpr ⟨a⁻¹, Eventually.of_forall fun i=> ?_⟩); rw[Real.norm_of_nonneg ?_, Real.norm_of_nonneg (Real.exp_pos ..|>.le)]; swap; · exact Shoot.scale_nn A' i
    unfold f; rw [mul_comm a⁻¹,← div_eq_mul_inv]; apply (le_div_iff₀ ha).mpr; linarith only [Real.add_one_le_exp (A'.S.scale i*a)]
include hz P hb
lemma simG(k:ℕ)(v:C.label d)(hk:C.ref d ≤ k) :
    ‖swale Z d k v‖≤ H! k*( Real.exp (Work.D01.columnLogs (A) k)*((C.labels.level d).extra+1:ℕ))*‖v‖:=by
    let F':= (C.labels.level d); let T':=barter A k; let U:= Real.exp (Work.D01.columnLogs A k)
    have ht:Tendsto (fun i:ℕ×ℕ=> spine C d k i.1 i.2 v) b! (𝓝 (swale Z d k v)):=topPitch hz hk (v:=fun _=>v) tendsto_const_nhds; apply le_of_tendsto ht.norm
    filter_upwards [(link_mesh hb).eventually_ge_atTop k] with i hi; have hu:= Work.D01.back_budget C P v hk hi (p:=i.2); have he:0 ≤ T':=by unfold T' barter;positivity
    rw [spine,norm_smul,Real.norm_of_nonneg he]; have hT:=cheap_theta A k; let x:=Cturn C d k i.1 i.2 v
    apply (mul_le_mul_of_nonneg_left ((cost_range F' x).trans ((Push.Local.norm_le_size ..).trans hu)) he).trans; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Push.Local.size_le_norm F' v) (Real.exp_pos _|>.le)) he).trans
    rw[mul_assoc (H! k),mul_assoc (Real.exp _)]; exact mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ U * ((↑(F'.extra+1):ℝ)*‖v‖))
include h in
lemma cine {f : ℕ→ C.label d}(hv:Fast C.S f)(p:ℕ): Fast C.S fun i=> ( (H! i)^p) • swale Z d i (f i):=by
    have hX(j:ℕ):Calms C.S 0 fun i=>(H! i)^j:=by induction j with
       | zero=>simpa using show Calms C.S 0 (fun _ => (1:ℝ)) from fun a ha=> factor_const _ _ _ ha
       | succ j ih=> simpa only [pow_succ,zero_add] using! ih.mul (hawker A)
    apply capped _ (hX p)
    let K:= C.labels.level d; let g i:= H! i * ( Real.exp (Work.D01.columnLogs (A) i)*((K.extra+1:ℕ):ℝ));
    have hG:Calms C.S 0 g:=by simpa only[add_zero, Pi.mul_apply] using! ((hawker A).mul ((Pull.curtain A).mul (show Calms C.S 0 (fun _=>((K.extra+1:ℕ):ℝ)) from fun a ha=> factor_const _ _ _ ha)))
    apply (capped hv hG).smaller; refine isBigO_iff.mpr ⟨1, ?_⟩; filter_upwards [eventually_ge_atTop (C.ref d)] with i hi; rw [one_mul, norm_smul, Real.norm_of_nonneg (by unfold g; positivity [bell A i])]; exact simG P hb hz i (f i) hi
-- choose linear operation for output independent angles.
def Hero (J:Scaling S)(V:∀ i,Vane C i)(Z:Arch C)(d i:ℕ): S.Field d→ₗ[ℂ] (Cells.standard C).Field d:= crown Z J (Stern V) d i • (J.U i d).symm.toLinearMap
include H'
lemma heroicB(i:ℕ)(v:C.label 4)(hq:C.ref 4≤ P! i): Hero J V Z 4 i (centering S 4 (S.project 4 v))= Moment4 Z J V i (swale Z 4 (P! i) v):=by
   let F:= Moment4 Z J V i; let U:=(J.U i 4).symm; let c:= crown Z J (Stern V) 4 i; change c • U _ = U (centering S 4 (Vault S Z 4 (P! i) c _)); rw [cash_pinc hz P hb S H'.laws v c hq]; exact ( (U.toLinearMap.restrictScalars ℝ).map_smul _ _).symm
end YM.Trace.Shelves
