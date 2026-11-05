import YM.TraceExtension.Shelves.Pear
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
variable (ho': S₁.Orientation H'.spin)(hc:CellHyp C F) {i:Bend} {P':PaceBook C}(hv:Rod t i (𝓛:Filter (ℕ×ℕ)) P') (he:Prosper V h H s)
-- dynamic rank valuations on Kernel.Auth.Compare with ∆. identify oriented endpoint.
abbrev DSeed (o:S₁.Orientation H'.spin): KernelSpace H'.spin→ₗ[ℝ] TableOne H'.spin:= (rankOp S₁ o).comp (({
 toFun:=fun v=>⟨v.val,(Further.PhysicalPeriodLimitF933.two _ _).mpr ((kernel_mem.mp v.property).1)⟩
 map_add':=fun _ _=>rfl
 map_smul':=fun _ _=>rfl } : KernelSpace H'.spin→ₗ[ℝ] TableTwo H'.spin))
lemma DSeed_pay(o:S₁.Orientation H'.spin)(v:KernelSpace H'.spin): (DSeed H' o v).val= nabla S₁ v.val:=rfl
include hz P h ht hb hY hq H'
lemma bridge5 (L:PaceBook C): ∀ᶠ k:ℕ in atTop, ∀ a:Axis,(s k (Shine5 Z L.Z (P! k))).val a= Hero J V Z 5 k (S.project 5 (Pole L (P! k) a)):=by
    filter_upwards [hY.starts, hq.growth.eventually ((Sstar A).eventually_ge_atTop (C.ref 5))] with k hi ht'; intro a; let F:=Zᵣ; let i:=P! k; let X:=Pole L i; let f(j):=(L.Z j).x i; have he : X∈Bowl F:= blade F f; have hn:night F (X a):=frames_night F ⟨X,he⟩ a
    rw [stem_eq P h ht hb hz hq H' hY k ht' _ hn, hi]; exact congr_arg ((J.U k 5).symm) (congr_arg _ ((show swale Z 5 i (X a)=_ from stroke P ht hb hz i ht' f a).symm))
lemma triad(i:ℕ): (fun a=>S.project 5 (Pole P' i a))∈ TableOne H'.spin:=by
    let Z:= OrbitR (Zᵣ) (fun j=> (P'.Z j).x i); let C':= plate (Zᵣ) Z; let p:= vectorProjection H'.spin C'; suffices hh:p.val=fun a=>S.project 5 (Pole P' i a) from hh ▸ p.property
    ext1 a; change fromPol S ( (C.labels.level 5).coords.symm _)=_; rw[fromPol_formula, show S.project 5 _= _ from rfl]; exact congr_arg _ ((C.labels.level 5).coords.apply_symm_apply _)
include hv hu
include hJ ho' HF hc he hM hT θ K
lemma careers (p:ℕ)(a:Axis): Tendsto (fun i=> H! (P! i)^p • (Hero J V Z 5 i (nabla S₁ (baron S P' (P! i)) a) - (s i (Shine5 Z P'.Z (P! i))).val a)) atTop (𝓝 0):=by
    let v(k): KernelSpace H'.spin:= ⟨baron S P' k,stitch_k H' P' k⟩
    let U k:= DSeed H' ho' (v k); let L(k):TableOne H'.spin:=⟨_, triad P h ht hb hz hq H' hY (P':=P') k⟩
    have hx(a:Axis):Fast C.S (fun k=>(U k-L k).val a):= curtain' P h θ K ht hM hT hb H' hc HF hJ ho' hu i P' hv a
    refine (syl P h ht hb hz hq H' hY (fun i=> U i-L i) hx p he a).congr' ?_; filter_upwards [bridge5 P h ht hb hz hq H' hY P'] with i hi
    rw[hi]; exact congr_arg ((H! (P! i)^p) • · ) ((Hero J V Z 5 i).map_sub ((U (P! i)|>.val a)) ((L (P! i)|>.val a)))
end YM.Trace.Shelves
