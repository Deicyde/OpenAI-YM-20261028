import YM.TraceExtension.Slate.Cost
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
-- main channel 'none'. additional shear false, scalar true.
abbrev Bend:= Option Bool
def rally(t:Tickets C)(i:Bend)(k N p:ℕ): Sway G (C.side k p):= i.elim (Zn.Meld (t k N p).J (H! k)) (fun i=> Plint G _ i)
def Pick(t:Tickets C)(i:Bend)(a b:Axis): Guilds C:=fun k N p=> rally t i k N p a b 0
def PeakG(t:Tickets C)(i:Bend)(a:Axis):Guilds C:= fun k N p=> boom (rally t i k N p) a 0
def PeakPart(t:Tickets C)(i:Bend)(a b:Axis):Guilds C:= fun k N p=> elm a (rally t i k N p a b) 0
structure PaceBook(C:Family G) where
    T : Axis → Axis→ Logs C 4
    Zp : Axis → Axis → Logs C 5
    Z : Axis → Logs C 5
structure Rod(Q: Tickets C)(i:Bend)(𝓛:Filter (ℕ×ℕ))(t:PaceBook C):Prop where
    pole(b c:Axis): Loan (Pick Q i b c) 𝓛 (t.T b c)
    bare(a b:Axis): Loan (PeakPart Q i a b) 𝓛 (t.Zp a b)
    bend(b:Axis): Loan (PeakG Q i b) 𝓛 (t.Z b)
include hu
lemma eager(i:Bend) : ∀ᶠ k:ℕ in atTop,∀ᶠ x:ℕ×ℕ in b!, Club (C.path.rep x.1 x.2 k) (H! k) (rally t i k x.1 x.2):=by
    cases i; exact hu.mono fun k hi=> hi.mono fun p hp=>hp.sea.club
    exact hu.mono fun k hi=> hi.mono fun p hp=>hp.bases _
include hb h hM θ K ht hT P in
lemma bingo(i:Bend):∃ X:PaceBook C,Rod t i b! X:=by
    have he:= eager hu i
    choose g hg using fun a b=>Slate.bank P h θ K ht hM hT hb hu (Pick t i a b) (d:=4) (by norm_num) (he.mono fun i hi=> hi.mono fun p hp=>hp.peek a b)
    choose f hf using fun a b=>Slate.bank P h θ K ht hM hT hb hu (PeakPart t i a b) (d:=5) (by norm_num) (he.mono fun i hi=> hi.mono fun p hp=>hp.piece a b)
    choose j hj using fun a=> Slate.bank P h θ K ht hM hT hb hu (PeakG t i a) (d:=5) (by norm_num) (he.mono fun i hi=> hi.mono fun p hp=>hp.full a)
    exact ⟨⟨g,f,j⟩,hg,hf,hj⟩
lemma Unwrap:∀ᶠ k:ℕ in atTop,∀ᶠ x:ℕ×ℕ in b!, Nonwrapping (Wicket.tempQ (H! k) (n:=C.side k x.2)) 0:=by
    refine hu.mono fun k hi=> hi.mono fun p hp i hx=>?_
    have hm : separation i 0 ≤ Zn.high (H! k)+1:=by obtain ⟨v,hv,h⟩:= halo_spec.mp hx; rw [Finset.mem_singleton.mp hv,separation_comm] at h; exact h
    have ht:= hp.site; change 20*(Zn.high (H! k)+Zn.rim (H! k)+10)< (C.side k p.2).val at ht; omega
end YM.Trace.Slate
