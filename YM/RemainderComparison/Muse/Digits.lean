import YM.RemainderComparison.Muse.Troupe

/-!
# With rendered LENGTH and legacy fees. Optional subsidies kept separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Muse
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Mixed
open Cascade Halo Height Opacity
local notation "LT"=> sits Z l δ
open Sleet Next.Foundations
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "q'"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)

variable [Fintype ι] (P':BudgetPoint)(hx:P'.B=radiusB x)(ht:P'.threshold=Pressure.temp x)(hn:P'.order≤j)(hk:P'.power≤J)
local notation "G'" => gStep R.beta
local notation "Pv" => Muse.Pure M H χ Z k

variable (E:Set ℕ)(w:ℕ→ℝ)(g:ℝ)
local notation "L₂"=> Muse.song M H χ U.T E w

def Elder (c:ℕ)(p:Staff M H):= Halo.dyed M H E p.1 p.2∧1+c ≤ Halo.gross M H p.1 p.2
include h hx ht hn hk hh
lemma prowess (hp: Halo.Presents R E w g)(he:g ≤ incomingE G L x) (c':ℕ): Network M H χ (sits Z l δ) P' {z|Pv z ∧ Elder M H E c' z} (Muse.toll M H l L₂ j J) a (V*T0^c' *g):=by
    obtain ⟨X,hX,sx,P,hQ⟩:= hh.claim
    obtain ⟨hc,hT⟩:=h.digest ι _ M sx P l _ E w g hQ hh.target hp he
    apply Muse.enclosure M H χ Z l δ
    · exact Muse.reunion M H χ U.T.T.N l P' hx ht hn hk L₂ hc _ (fun z i=> (Halo.dyed M H E z i ∧ 1+c' ≤ Halo.gross M H z i) ∧ Lyric.notes M H z i≤ k) (fun z ⟨hz,he⟩=>⟨he,recalls M H χ Z _ hz⟩) (hT c') hQ.currency
    intro z ⟨h,hp⟩; exact h.1
omit h hx ht hn hk hh
omit [Fintype ι] in
lemma Elders (z:Staff M H) (h: Halo.dyed M H E z.1 z.2) : Elder M H E 0 z:=by
    refine ⟨h,?_⟩; obtain ⟨j,k,-,h⟩:= h; exact (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨_,h⟩)).trans (Finset.single_le_sum (f:=fun j=>((z.fst.snd j).val\ Tickets.reach (z.snd j)).card) (fun _ _=>Nat.zero_le _) (mem_univ j))
include h hx ht hn hk hh
lemma cork (Z':ℕ)(wK:ℕ→ℝ)(hS: Sleet.Cost R E Z' x d σ wK) : Network M H χ (sits Z l δ) P' {z| Pv z ∧ Halo.dyed M H (ridge R Z' E) z.1 z.2} (Muse.toll M H l (Muse.song M H χ U.T (ridge R Z' E) wK) j J) a (gStep R.beta^s):=by
    refine Muse.advance M H χ _ P' _ (Muse.prowess M H χ Z l δ U h hh P' hx ht hn hk (ridge R Z' E) wK _ (Sleet.sails E wK hS) h.crop.2.1 0) (fun i h=> ?_) ?_
    · obtain ⟨z,hz⟩:=h; exact ⟨z,Elders M H _ i hz⟩
    rw [pow_zero,mul_one]; exact h.crop.2.2.1

local notation "l'"=> sits Z l 0
def Pale (Y:ℕ)(d b K:ℝ)(I:ℕ) (H':Cash W x μ L Q o C T R):Prop:= let _:=H';∃ (E:Type)(_:Fintype E)(X:E→Site f)(p:ι→ Finset E),Lyric.Scale X p M (pigmentY R Y M x d (sits Z l 0)) I b K S
-- Sales needed MARK.CLOUD only. Input can pay exponential tails in path.T.
include h hx ht hn hk hh
lemma muddyline (X':ℕ)(hm:Muse.Pale M Z l X' d τ K I H) : Network M H χ (sits Z l δ) P' {z|Pv z∧muddy R X' M (Lyric.page M H z.1 z.2)} (Muse.toll M H (sits Z l 0) L₁ j J) a (gStep R.beta^s) :=by
    obtain ⟨X,hX,sx,p,hc⟩:= hm
    obtain ⟨hzW,hT⟩:=h.answer _ M
    let g:=pigmentY R X' M x d l'; have hQ := hT X sx p _ τ hc hh.target
    have hv:= Halo.remits M H χ U.V.T.N g L₁ (fun _ _=> True) (show Ac.Hit _ _ _ a γ from by simpa only [↓reduceIte] using! hQ) hc.currency h.allowed hzW k
    simp only [true_and] at hv
    have hf:= (Sleet.Scale.clear M (sits Z l 0) hc h.crop.1) -- fix
    have hf : ∀ i,0 ≤ sits Z l 0 i:= hf.currency
    have hp:= Sleet.color M H χ U.V.T.N l' hzW h.crop.1 hf hv
    refine Muse.abroad (k:=k) M H χ Z l δ (Muse.reunion M H χ U.V.T.N l' P' hx ht hn hk L₁ hzW _ (fun z i=> Lyric.notes M H z i≤ k ∧ muddy R X' M (Lyric.page M H z i)) (fun i ⟨hi,hL⟩=> ⟨recalls M H χ Z _ hi,hL⟩) (fun i=> budget_loosen (hp i) h.crop.2.2.2) hf) ?_
    exact fun i hi=> (show _∧_ from hi).1
end YM.RemainderComparison.Muse
