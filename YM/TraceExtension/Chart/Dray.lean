import YM.TraceExtension.Chart.Token
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
-- coarse bill signs canonical bare divergence. Lens overlay.S.
abbrev TQ (V:∀ i,Vane C i):= taxA C.path.levels ∘ Stern V
abbrev RQ (V:∀ i,Vane C i):= Pig C.path.levels ∘ Stern V
abbrev BQ(Z: Arch C)(V:∀ i,Vane C i):= Z.β ∘ Stern V
lemma river_k(Y:Levels G)(k:ℕ): Pig Y k≤taxA Y k:= Zn.wane _ (by norm_num)
include P θ K ht hT h hM hb hu hp Hδ hr hA hL he hz hq H' HF hq' hP ho hJ hY ho' hc
set_option maxRecDepth 2048 in
lemma pairingD : Tendsto (fun i=> BQ Z V i • BeamC (H:=H) H' J V Z ho' i L - s i (Shine5 Z X (P! i))) atTop (𝓝 0):=by
    let b:= BQ Z V; let R:=fun i=> H! (P! i); let x:=fun i=> BeamC (H:=H) H' J V Z ho' i L; let z(i):= s i (Shine5 Z L.Z (P! i));let v(i):= s i (Shine5 Z X (P! i)); let y:=fun i=>s i (medium L X Z (P! i))
    have hg (i:ℕ):0<b i:=measured hb P hz _
    have hB(i): |b i|≤2*(R i)^1:=by rw[abs_of_pos (hg i),pow_one];exact dex hb P hz _
    have hζ:∀ᶠ i:ℕ in atTop, 0 ≤ R i^(1:ℕ):=Eventually.of_forall fun i=>pow_nonneg (bell ..|>.le) _
    have hz₁:= invest (X:=fun i=> x i-z i) (c:=2) (E:=TableOne H.spin) zero_le_two (Eventually.of_forall hB) hζ (gapC P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hL he 1)
    have hz₂:= invest (X:=y) (c:=2) (E:=TableOne H.spin) zero_le_two (Eventually.of_forall hB) hζ (legacy P h θ K ht hM hb hu hz hp Hδ hr hA hL hq H' HF hq' hJ hP ho hY 1)
    have hz(i): b i • y i=v i-b i • z i:=by
        let f:=P! i;change b i • s i ((b i)⁻¹ • Shine5 Z X f - _)= _; rw [map_sub,map_smul,smul_sub,smul_inv_smul₀ (hg i).ne']
    have ht:= hz₁.sub hz₂; rw [sub_zero] at ht; exact ht.congr (fun i=>by change b i • (x i-z i) - b i • y i=b i • x i-v i; rw[hz,smul_sub];abel)
variable {μ:ℕ→TableOne H.spin→ₗ[ℝ] ℝ}(hm:PaymentR (H:=H) s h V μ)
lemma sizeQ' : ∃ c:ℝ,0 ≤ c∧∀ᶠ i in atTop, ‖BQ Z V i • BeamC (H:=H) H' J V Z ho' i L‖ ≤ c*RQ V i:=by
    obtain ⟨q,hq',hq₁,hq₂⟩:= penumbra P h hb hu hz hp; obtain ⟨c,hc₁,hc₂⟩:= shady (X:=fun i=> Shine5 Z X (P! i)) (E:=Bowl Zᵣ) (F:=TableOne H.spin) he.alpha hq' ((Sstar A).comp hq.growth|>.eventually hq₁)
    have ht:= pairingD P h θ K ht hM hT hb hu hz hp Hδ hr hA hL hq H' HF ‹StarPath F H J H' 𝓛› hJ hP ho hY ho' hc he
    refine ⟨1+c,add_nonneg zero_le_one hc₁,?_⟩; filter_upwards [hc₂,ht.norm.eventually (ge_mem_nhds (show ‖(0:TableOne H.spin)‖ < 1 by simp))] with i hi hv; let k:= P! i
    change ‖_‖ ≤ (1+c)*RQ V i; rw[add_mul,one_mul]; exact (norm_le_norm_sub_add ..).trans (add_le_add (hv.trans (Zn.wok _ _ (by norm_num:(0:ℝ)≤1/6))) hi)
include hm
lemma transferX : Tendsto (fun i=> μ i (BQ Z V i • BeamC (H:=H) H' J V Z ho' i L)) atTop (𝓝 (-G.slopeConstant)) := by
    let X' i:= BQ Z V i • BeamC (H:=H) H' J V Z ho' i L; let Y i:= Shine5 Z X (P! i); let u(i):=Lease Zᵣ h (Y i)
    let V'(i):=s i (Y i);have hv:Tendsto (Stern V) atTop atTop:=(Sstar A).comp hq.growth
    obtain ⟨q,Hq,hQ⟩:=hm.lean; obtain ⟨c,hc',hc₁,hc₂⟩:=penumbra P h hb hu hz hp
    have hc₃:Tendsto (fun i=> μ i (X' i)-μ i (V' i)) atTop (𝓝 0):=by
        have hx:Tendsto (fun i=>(1:ℝ) • (X' i-V' i)) atTop (𝓝 0):=by simp only[one_smul]; exact pairingD P h θ K ht hM hT hb hu hz hp Hδ hr hA hL hq H' HF hq' hJ hP ho hY ho' hc he
        have h:= liftB (E:=TableOne H.spin) hQ hx; simpa only [one_mul, map_sub] using! h
    have hP:Tendsto u atTop (𝓝 (-G.slopeConstant)):= hc₂.comp hv
    have hp₁:Tendsto (fun i=> μ i (V' i)-u i) atTop (𝓝 0):=by
       apply Metric.tendsto_nhds.mpr; intro ε hε; let d:= ε/(1+c); have he0:0< d:= div_pos hε (add_pos_of_pos_of_nonneg zero_lt_one hc');
       filter_upwards [hv.eventually hc₁,hm.lead d he0] with i hi hI; let k:= (P! i); have ht :0< taxA A k:= Zn.wake ..; have hx:= hI (Y i); rw[dist_zero_right]; apply lt_of_mul_lt_mul_left (a:=taxA A k) _ ht.le
       apply lt_of_le_of_lt (b:=d*c*taxA A k)
       · rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ taxA A (P! i) from ht.le)] at hx; exact le_trans (le_trans hx (mul_le_mul_of_nonneg_left (le_trans hi (mul_le_mul_of_nonneg_left (river_k ..) hc')) he0.le)) (mul_assoc ..).symm.le
       have hy := div_mul_cancel₀ ε (show 1+c≠0 from (add_pos_of_pos_of_nonneg zero_lt_one hc').ne'); change d*(1+c)=ε at hy; rw [mul_comm _ ε]; gcongr; linarith only [hy,he0]
    have hx:=(hc₃.add hp₁).add hP; rw[add_zero, zero_add] at hx; exact hx.congr (fun i=>by change _-_+(_-_)+u i= _; abel)
end YM.Trace.Over
