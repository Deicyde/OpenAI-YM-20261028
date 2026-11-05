import YM.TraceExtension.Chart.North
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
variable (ho': S₁.Orientation H'.spin)(hc:CellHyp C F) {i:Bend} {P':PaceBook C}(hv:Rod t i (𝓛:Filter (ℕ×ℕ)) P') (he:Prosper V h H s)
open Asymptotics Next.Rank
abbrev LogZoom (X:Scaling S) := fun i=> Real.log (X.r i)⁻¹
include P hz hb h hq θ
lemma zoom_BQ : Tendsto (fun i=> LogZoom J i / BQ Z V i) atTop (𝓝 G.slopeConstant⁻¹):=by
    let P':= A;let k(i):=(V i).k;let Q:=Stern V; let B:=P'.clock.hatBeta;let m(i):= B (k i); let L:= Lyra (A);let g:= G.slopeConstant; have hg:0 < g := Gauge.slopeConstant_pos h
    let f(i:ℕ):=b_zoom V i;have hb'(i):0 < f i:= shine i
    have hx:Tendsto (fun i=> Real.log (f i)/m i) atTop (𝓝 0):=by
        refine squeeze_zero' ?_ ?_ (show Tendsto (fun i=> Gate (m i)/m i) atTop (𝓝 0) from Gate_calm.comp ((hrate A h).comp hq.growth))
        · filter_upwards [(grow_big hq h).eventually_ge_atTop 1] with i hi; exact div_nonneg (Real.log_nonneg hi) (bell ..|>.le)
        filter_upwards [hq.growth.eventually (titles P' h 1 zero_lt_one)] with i hi; apply div_le_div_of_nonneg_right _ (bell ..|>.le); apply Real.log_le_iff_le_exp (hb' i)|>.2
        have hv: f i ≤ Terrace.watch _ 1 (k i):= (show f i ≤ tilt_cap P' (k i) from tiltP _ ((hq.season i).1.high.2)).trans hi.2
        simpa only [Terrace.watch, one_mul] using hv
    have hz₁:Tendsto (fun i=>P'.S.scale (k i)/m i) atTop (𝓝 g⁻¹):=by
        have he(i): P'.S.scale (k i)/m i=(1-P'.clock.bar/m i)/g:=by
            have hb:m i=P'.clock.bar+g*P'.S.scale (k i):=rfl; have hx:= bell P' (k i); field_simp [show m i≠ 0 from hx.ne'];linarith only [hb]
        simp_rw [he]; have he:= ((tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:=P'.clock.bar)).div_atTop ((hrate P' h).comp hq.growth))).div_const g; simpa only[sub_zero,one_div] using! he
    have hT : Tendsto (fun i=> LogZoom J i/m i) atTop (𝓝 g⁻¹):=by
        have he(i): LogZoom J i/m i= P'.S.scale (k i)/m i- Real.log (f i)/m i:=by
             unfold LogZoom; rw [Real.log_inv,show J.r i = P'.S.a (k i)*f i from (hq.season i).2.symm, Real.log_mul (P'.S.a_pos _).ne' (hb' i).ne']; unfold Schedule.scale; rw[Real.log_inv];ring
        simp_rw [he]; simpa only[sub_zero] using! hz₁.sub hx
    let b(i):= Z.β (k i); let t:= BQ Z V; have hp:= hq.growth
    have hz₀:Tendsto (fun i=> b i/m i) atTop (𝓝 1):= (gamut hb P hz h).comp hp; have hr:Tendsto (fun i=> b i/t i) atTop (𝓝 1):=(Barry hz P hb h θ).comp hp
    have he:= (hT.div hz₀ one_ne_zero).mul hr; rw [div_one,mul_one] at he
    exact he.congr (fun i=>by have hb:t i > 0:= measured hb P hz _; have hp:b i > 0:= measured ‹_› P hz _; have hv:m i > 0:= bell ..; change LogZoom J i/m i / (b i/m i) * (b i/t i) = _/t i; field_simp)
omit P hz hb h hq θ
lemma a_clock : Tendsto (LogZoom J) atTop atTop:=by
    apply Real.tendsto_log_atTop.comp
    apply Tendsto.inv_tendsto_nhdsGT_zero; exact tendsto_nhdsWithin_iff.mpr ⟨J.drips,Eventually.of_forall fun i=>J.positive i⟩
lemma clock_cost : Tendsto (fun i=>LogZoom J i* J.r i^ (4:ℕ)) atTop (𝓝 0):=by
    have hp (i): (J.r i)^ (4:ℕ)= (Real.exp (4*LogZoom J i))⁻¹:=by rw [show (4:ℝ) = ↑(4:ℕ) from rfl,Real.exp_nat_mul, show Real.exp (LogZoom J i)= (J.r i)⁻¹ from Real.exp_log (inv_pos.mpr (J.positive i)),inv_pow (_:ℝ) 4,inv_inv]
    have hr:= (isLittleO_rpow_exp_atTop (1:ℝ)).tendsto_div_nhds_zero
    have he:= ((show Tendsto _ _ _ from hr.comp (a_clock (J:=J)|>.const_mul_atTop (show 0 < (4:ℝ) by norm_num)))).const_mul (1/4:ℝ)
    rw[mul_zero] at he; apply he.congr; intro i;rw[hp]; change (1/4:ℝ)*(((4:ℝ)*LogZoom J i)^ (1:ℝ) / _) = _; rw [Real.rpow_one]; ring
include P hz hb h hq θ
lemma band_cost:Tendsto (fun i=>BQ Z V i * J.r i^(4:ℕ)) atTop (𝓝 0):=by
   have hw:= (Gauge.slopeConstant_pos h).ne'; have hp:= clock_cost (J:=J)|>.div (zoom_BQ P h θ hb hz hq) (inv_ne_zero hw)
   rw[zero_div] at hp; refine hp.congr' ?_; filter_upwards [a_clock (J:=J)|>.eventually_gt_atTop 0] with i hi
   have hv:BQ Z V i ≠0:= (measured hb P hz _|>.ne'); dsimp only [Pi.div_apply];field_simp
end YM.Trace.Over
