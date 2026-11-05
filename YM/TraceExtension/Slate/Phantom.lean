import YM.TraceExtension.Slate.Pony
import YM.TraceExtension.Terrace.Terrain
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
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
-- key EL combination. Main Z f retained.
def medium (L: PaceBook C)(X:Axis→Logs C 5)(Z:Arch C)(k:ℕ): Bowl (C.labels.level 5):= (Z.β k)⁻¹ • Shine5 Z X k - Shine5 Z L.Z k
def coreF(Z:Arch C)(X Y:Axis→ Logs C 5)(k:ℕ): Bowl (C.labels.level 5):= OrbitR (Zᵣ) ((fun i=> (X i).x k) - Z.β k • (fun i=> (Y i).x k))
include hp Hδ hr hA P h ht θ K hq hb hz hL hu
lemma hullage : ∃ t,Mission V 𝓛 t (fun i=> (coreF Z X L.Z (Stern V i)).val (0:Axis)):=by
    let P':=Stern V; let A' k (p:ℕ×ℕ):= OrbitR (Zᵣ) ((fun i=>(X i).v k p)-C.path.β p.1 p.2 k • (fun i=> (L.Z i).v k p));
    let l(i)(p):= (A' (Stern V i) p).val 0
    have hx := (Sstar A).comp hq.growth
    refine ⟨l,⟨hx.eventually (p:=fun k=> Tendsto (fun p=> (A' k p|>.val 0)) b! (𝓝 ((coreF Z X L.Z k).val 0))) ?_, 4,?_⟩⟩;
    · show ∀ᶠ k:ℕ in atTop,Tendsto (fun p=> (A' k p).val 0) b! (𝓝 ((coreF Z X L.Z k).val 0))
      filter_upwards [eventually_all.mpr (fun i=> (hp i).lands),eventually_all.mpr (fun i=>TravelsC.lands (hL.bend i))] with i hi hP
      let v(p:ℕ×ℕ):= fun j=> (X j).v i p; let g(p:ℕ×ℕ):=fun j=> (L.Z j).v i p; have hv :Tendsto v b! (𝓝 fun j=>(X j).x i):= tendsto_pi_nhds.mpr hi; have hg :Tendsto g b! (𝓝 fun j=>(L.Z j).x i):= tendsto_pi_nhds.mpr hP; have hT:Tendsto (A' i) b! (𝓝 (coreF Z X L.Z i)):= ((OrbitR (Zᵣ)).continuous.continuousAt.tendsto).comp (hv.sub ((hz.mintS i).smul hg)); exact tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hT) 0
    filter_upwards [ hq.growth.eventually (crestship P h θ K Hδ hr hA ht 48),hx.eventually hu,hx.eventually (eventually_all.mpr (fun i=> (hp i).state)),hx.eventually (eventually_all.mpr (fun i=> TravelsC.state (hL.bend i))) ] with i hi hk hx hΩ j k
    filter_upwards[hk,eventually_all.mpr hx,eventually_all.mpr hΩ,(link_mesh hb).eventually_gt_atTop k,(link_mesh hb).eventually (Stock.clear_interior C P (V i|>.k) 5)] with p hK hQ hP hm hY
    let Q:= t k p.1 p.2
    obtain ⟨s,v,c,h'⟩:= hK.cover
    refine ⟨hm,hi p.2 p.1 hm s v c Q.J hK.age h' Q.B Q.V Q.U hK.ready Q.X (fun i=>hK.boat i) (fun i=> (X i).v k p) (fun i=>(L.Z i).v k p) (fun i=>⟨_,hQ i⟩) (fun i=>⟨_,hP i⟩) (?_) 0 ⟩
    intro x; obtain ⟨hx,hf⟩:=hY; exact hf p.2 0 x
omit hp Hδ hr hA θ K hL hu h in
lemma canal (L:PaceBook C)(x: Axis→ Logs C 5): ∀ᶠ i in atTop,∀ a:Axis, (medium L x Z (Stern V i)).val a=(Z.β (Stern V i))⁻¹ • swale Z 5 (Stern V i) ((coreF Z x L.Z (Stern V i)).val a):=by
    filter_upwards [hq.growth.eventually ((Sstar ..).eventually_ge_atTop (C.ref 5))] with i hi a
    let k:= Stern V i;let v:=Z.β k; have hv:=measured hb P hz k; let Q:= OrbitR (Zᵣ); let f:= fun j=>(x j).x k; let g:= fun j=>(L.Z j).x k; let V':= (swale Z 5 k).restrictScalars ℝ
    change ((v⁻¹:ℝ) • Shine5 Z x k-Shine5 Z L.Z k).val a= v⁻¹ • V' ((Q (f-v • g)).val a); rw [map_sub,map_smul]; change v⁻¹ • (Q _).val a-(Q _).val a= v⁻¹ • V' ((Q f).val a-v • (Q g).val a); rw [map_sub V',map_smul V',smul_sub, inv_smul_smul₀ (show v ≠ 0 from hv.ne')]; change v⁻¹ • _-_=v⁻¹ • swale Z 5 k _-swale Z 5 k _; rw[stroke P ht hb hz k hi f a,stroke P ht hb hz k hi g a]
end YM.Trace.Slate
