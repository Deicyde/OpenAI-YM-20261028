import YM.TraceExtension.Shelves.Height
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Slate Perfect Turret Margin
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
open Next.UVStress Asymptotics
variable {S: Table C.book} (HE:S.Hierarchy)(hx:CellHyp C F)(hp:F.PointLimits C S) {Y:DiffPlan S}(hf:Y.Derivatives S)
abbrev Portrait(S:Table C.book) (L:Logs C d):=fun k=> S.project d (L.x k)
-- cash warp.PD.HE
include hb P K h HE hx hp hu hf
lemma scores (i:Bend)(b c:Axis)(L:PaceBook C)(hv:Rod t i b! L): Fast C.S (fun k=>Y.deriv 4 b (Portrait S (L.T b c) k)-Portrait S (L.Zp b c) k):=by
    have hz:= eager hu i; let X:= Pick t i b c; let W:= PeakPart t i b c; have he : Credible X b!:= hz.mono fun i h=> h.mono fun p hp=>hp.peek b c; have hm :Credible W b!:= hz.mono fun i h=> h.mono fun p ht=> ht.piece b c; let H:=L.T b c;let H':=L.Zp b c
    apply differentiation HE Y hf b (by norm_num: 4≤7) (Trespass P h K hb HE hp hx he (hv.pole b c)) ?_ (Trespass P h K hb HE hp hx hm (hv.bare b c))
    swap
    · let U:= (S.project 4).toContinuousLinearMap; have hv:Calms C.S 4 H.x:= TravelsC.charge (hv.pole b c); change Calms C.S (↑(4:ℕ)) (fun k=>S.project 4 _); refine (Calms.smaller (v:=(4:ℕ)) (by simpa using hv :Calms C.S (↑(4:ℕ)) H.x) (isBigO_iff.mpr ⟨_, Eventually.of_forall (fun i=> U.le_opNorm (H.x i))⟩))
    intro I; filter_upwards [hz] with k hk; filter_upwards [(link_mesh hb).eventually_ge_atTop k,hk] with p hp h l
    let Fm:= rally t i k p.1 p.2 b c; have ht':Envelope (filmR (Fm 0)):=cylinder_env (lumen (h.peek b c)); have hu := beacon_h I 4 Fm hp (h.pose b c) ht' b l
    rw [Fold_eq I _ _ _ _ _ _ hp]; simp_rw [Fold_eq I _ _ _ _ X _ hp]; exact hu.2
omit hf
include ht θ hM hT
abbrev Crux (C:Family G):= ∀ (k _N p:ℕ), CrG G (C.side k p)
def Bake (V:Crux C):Guilds C:= fun k N p=> V k N p 0
def Clutch(V:Crux C)(a:Axis): Guilds C:=fun k N p=> twig a (V k N p) 0
lemma microphone (V: Crux C) (a:Axis) (he:∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ×ℕ in (𝓛: Filter (ℕ×ℕ)), Jade (C.path.rep i.1 i.2 k) (H! k) (V k i.1 i.2) a):∃ L:Logs C 4, Loan (Clutch V a) b! L ∧ Fast C.S (Portrait S L):=by
    let U:= Bake V; let Z':=Clutch V a; have ht₁:Credible U b!:=he.mono fun i h=>h.mono fun p hp=>hp.pace; have he₁ : Credible Z' b!:=he.mono fun i h=>h.mono fun p hp=>hp.heart
    obtain ⟨H,hH⟩:=Slate.bank P h θ K ht hM hT hb hu _ (d:=3) (by norm_num) ht₁; obtain ⟨L,hL⟩:=Slate.bank P h θ K ht hM hT hb hu _ (d:=4) (by norm_num) he₁; refine ⟨L,hL,?_⟩
    refine lent HE a h (Trespass P h K hb HE hp hx ht₁ hH) (Trespass P h K hb HE hp hx he₁ hL) ?_
    intro I; filter_upwards [he] with k hk; filter_upwards [(link_mesh hb).eventually_ge_atTop k,hk] with p hp ht l; have he:=beacon_h I 3 (V k p.1 p.2) hp ht.holds (cylinder_env (lumen ht.pace)) a l
    simp_rw [Fold_eq I _ _ _ _ U _ hp,Fold_eq I _ _ _ _ Z' _ hp]; exact he.1
end YM.Trace.Shelves
