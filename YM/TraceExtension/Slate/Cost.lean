import YM.TraceExtension.Margin.Stand
import YM.TraceExtension.Terrace.CabinBook
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
variable {d:ℕ}
abbrev Guilds(C:Family G):=∀ (k _N p:ℕ), Peat G (C.side k p)
def Tales(q:Guilds C): Films C:=fun k N p=> filmR (q k N p)
def Credible(q:Guilds C)(𝓛:Filter (ℕ×ℕ)):=∀ᶠ k:ℕ in atTop,∀ᶠ i in 𝓛,Cubc (C.path.rep i.1 i.2 k) (C.path.levels.clock.hatBeta k) (q k i.1 i.2)
def readsC (q:Guilds C)(d:ℕ): ProbesC C d:= fun k i=> Triple C.params (C.labels.level d) (H! k) (C.path.rep i.1 i.2 k) (q k i.1 i.2)
structure Logs(C:Family G)(d:ℕ) where
    v: ProbesC C d
    x: ℕ → C.label d
def Loan(q:Guilds C)(𝓛:Filter (ℕ×ℕ))(L:Logs C d):Prop:= TravelsC 𝓛 (Tales q) (readsC q d) L.v L.x
include P h θ K ht hM hb hT
variable {t:Tickets C}(hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
include hu
lemma bank (q:Guilds C)(hd:d≤5)(he:Credible q (𝓛:Filter (ℕ×ℕ))):∃ L:Logs C d, Loan q b! L:=by
    let Pm:= A
    obtain ⟨v,x,hx⟩:= recordsC P h θ K ht hM hb 1 zero_lt_one hT d (Tales q) (readsC q d) (by
        filter_upwards [he,hu] with k hi ht; filter_upwards [hi,ht] with p hp hv; rw[one_mul,← Harmony A k]; exact hv.earnings d hd _ hp)
    exact ⟨⟨v,x⟩,hx⟩
def exhibit(t:Tickets C)(a:Axis): Films C:=fun k N p=> ((t k N p).X a).exponentialEntry 0 (C.localSection 5) ((V!).rep N p k)
def Readout(t:Tickets C)(a:Axis): ProbesC C 5:=fun k i=> ((t k i.1 i.2).X a).x
lemma firm(a:Axis):∃ p:Logs C 5, TravelsC b! (exhibit t a) (Readout t a) p.v p.x:=by
    obtain ⟨v,x,hx⟩:= recordsC P h θ K ht hM hb 1 zero_lt_one hT 5 (exhibit t a) (Readout t a) (by
        filter_upwards [hu] with k ht;filter_upwards [ht] with i ht; rw [one_mul,← Harmony A k]; exact ⟨_,veil (proxD (C.localSection 5) C.params _ (ht.boat a|>.charge)) le_rfl (bell ..|>.le),rfl⟩)
    exact ⟨⟨v,x⟩,hx⟩
omit hM ht hT hu θ in
lemma Trespass {S:Table C.book}(hS:S.Hierarchy)(hs:F.PointLimits C S)(HP: CellHyp C F) {q:Guilds C} (he:Credible q b!){L:Logs C d}(hx:Loan q b! L): Book b! (beamC C d (Tales q)) (fun k=> S.project d (L.x k)):=by
    let l(k):= Sliver (H! k); refine recordsBook P h K hb (q:=l) ?_ (he.mono (fun i hi=> hi.mono fun j hj=> lumen hj)) hx HP hs hS
    filter_upwards [(hrate A h).eventually ((ferry slit) 4 (by norm_num))] with i hi; exact hi.2.trans (Real.rpow_ofNat ..).le
end YM.Trace.Slate
