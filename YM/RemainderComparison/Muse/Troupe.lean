import YM.RemainderComparison.Muse.Register

/-!
# Per-stage Epoch producer, earns K law from Rough probe
Doesn't require analytic cost on eN. At any SAME Local.Calibrator with specified roots/markers registers. Constituents independent of Aux Crown radius. Don't assume convergence costs to prove these.
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
variable (N:Captain H j q d v u A b r B e n χ)
local notation "sx"=> radiusB x
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Mixed
open Cascade Halo Height Opacity
local notation "LT"=> sits Z l δ
open Sleet Next.Foundations

-- finite sets.square-zero only through capacity k on COUNT of mark occurrences; last transfer polynomials rely on plugging M alignment by same Marker owner. Not assuming any output cap reshape.
-- Predicates.S.Stamp purely ∈ S.X. No dependence on M.ingredient(uniform sup). Replace XM.Length test concentration later.

def Pure (k:ℕ)(p:Staff M H):= virgin M H χ Z p.1 p.2 ∧ arity M H χ Z p.1 p.2≤ k
def impure (k:ℕ)(p:Staff M H):= ¬ virgin M H χ Z p.1 p.2 ∧ arity M H χ Z p.1 p.2 ≤ k
lemma recalls (p:Staff M H)(h:Pure M H χ Z k p): notes M H p.1 p.2≤ k:=by rw [← harmonic M H χ Z p.1 p.2,show Verse.load _ _ = 0 from h.1,add_zero]; exact h.2
lemma abroad {P':BudgetPoint}{Y_:Set (Staff M H)}{V:Staff M H→ℝ}(h: Network M H χ (sits Z l 0) P' Y_ V a b) (hv:Y_ ⊆ {p| Pure M H χ Z k p}): Network M H χ (sits Z l δ) P' Y_ V a b:=by
   refine ⟨fun p hp=> ?_,h.costs⟩
   let f:= Mosaic.etude M H χ p.1 p.2
   have he (x:ℝ): f.emit (sits Z l x)= f.emit l:=by
      funext y; rw [sits,Verse.excursion, show Verse.load Zᶜ f.letters= 0 from (show Pure M H χ Z k p from hv hp).1,pow_zero,one_mul]
   rw [show _=f.emit l from he δ,←he 0]; exact h.mark _ hp

structure Motto (H':Cash W x μ L Q o C T R)(b a Y : ℝ) (I:ℕ) : Prop where
   claim : ∃ (P':Type) (_:Fintype P') (X:P'→Site f) (p:ι→ Finset P'), Lyric.Scale X p M l I b a S
   target : radiusCost Q L b
   positive : 0≤δ
   emit : Y*δ ≤ 1
   grew : Lyric.tax G L x*δ ≤ 1

variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "L₂"=> floats M H χ U.S.N
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)

variable [Fintype ι]
local notation "l'" => desk Z l δ (P₀)
include h hh
lemma enrolled : Plot M H l' :=by
    obtain ⟨P',hp,X,p',hc⟩:= hh.claim
    have hY:1≤P₀:= one_le_pow₀ h.price.roll
    obtain ⟨hx,hS⟩:= descans Z l δ hh.positive hh.grew (zero_lt_one.trans_le hY) hc.currency
    refine lessen M H _ ?_ _ hx hS
    exact (concert M H χ l U.S.N h.price hc ⟨h.hero,(Sleet.narrow H χ _ h.view h.price.roll)⟩ hh.target).1

variable (P':BudgetPoint)(hx:P'.B=radiusB x)(ht:P'.threshold=Pressure.temp x)(hn:P'.order≤j)(hk:P'.power≤J)
local notation "G'" => gStep R.beta
local notation "PV" => Pure M H χ Z k
local notation "UV" => impure M H χ Z k
include hx ht hn hk

structure Ballad (U:Pad H j χ)(l:ι→ ℝ)(k s J:ℕ)(a δ Y γ:ℝ):Prop where
   high₁ : Network M H χ (sits Z l δ) P' {p|Pure M H χ Z k p∧Sleet.tumble H p.1} (Muse.toll M H l (floats M H χ U.S.N) j J) a (gStep R.beta^s)
   high₂ : Network M H χ (sits Z l δ) P' {p|Pure M H χ Z k p∧Sleet.Flurry H p.1 k s} (Muse.toll M H l (floats M H χ U.S.N) j J) a (gStep R.beta^s)
   dry : Network M H χ (sits Z l δ) P' {p|Pure M H χ Z k p} (Muse.toll M H l (Muse.song M H χ U.V ∅ 0) j J) a (Y^k*γ)
   wet : Network M H χ (sits Z l δ) P' {p| impure M H χ Z k p} (Muse.toll M H (sits Z l δ) (Muse.song M H χ U.V ∅ 0) j J) a (Y^k*Y*γ*δ)

lemma awards : Ballad M H χ Z P' U l k s J a δ Y γ :=by
    obtain ⟨X,hX,s',p',hc⟩:=hh.claim
    obtain ⟨hzW,hT⟩:=h.answer _ M
    have hz:= Lyric.rocketing M H χ F' h.hero
    have hQ : Ac.Hit (Captain.reachability (H:=H)) sx (fun z=>∑ i:Syllable M H z,Lyric.Bill M H L₁ z (Lyric.mulScale Y⁻¹ l) j i J) a γ:= hT X s' p' l τ hc hh.target
    apply Ballad.mk
    · refine Muse.enclosure M H χ Z l δ P' _ (Muse.reunion M H χ _ l P' hx ht hn hk L₂ hz _ (fun z i=>tumble H z∧ Lyric.notes M H z i≤k) ?_ (Sleet.tempest M H χ _ l hc hh.target h.price h.view h.hero) hc.currency) ?_
      · intro z ⟨hv,hw⟩; exact ⟨hw, recalls M H χ Z z hv⟩
      exact fun i (h : Pure M H χ Z k i∧ _) => h.1.1
    · refine Muse.enclosure M H χ Z l δ P' _ (Muse.reunion M H χ _ l P' hx ht hn hk L₂ hz _ (fun z i=>Flurry H z k s∧Lyric.notes M H z i≤k) ?_ (Sleet.snow M H χ _ l hc hh.target h.price h.hail h.hero h.view) hc.currency) ?_
      · exact fun i h=>⟨(show _∧_ from h).2,recalls M H χ Z i (show Pure M H χ Z k i from (show _∧_ from h).1)⟩ -- edit
      exact fun i (h : Pure M H χ Z k i∧ _) => h.1.1
    · have hv:= Halo.remits M H χ U.V.T.N l L₁ (fun _ _=> True) (show Ac.Hit _ _ _ a γ from by simpa only [↓reduceIte] using! hQ) hc.currency h.allowed hzW k
      simp only [true_and] at hv
      exact Muse.enclosure M H χ Z l δ P' _ (Muse.reunion M H χ _ l P' hx ht hn hk L₁ hzW _ (fun z i=> Lyric.notes M H z i≤k) (recalls M H χ Z) hv hc.currency) (fun i (hi : Pure M H χ Z k i)=> hi.1)
    · have he':= orders (I:=k) M H χ _ Z l δ L₁ hzW hc.currency hh.positive Y h.allowed hh.emit hQ
      have hb i: 0 ≤ sits Z l δ i:=by unfold sits; apply mul_nonneg _ (hc.currency i); unfold Verse.marked; split; exact hh.positive; exact zero_le_one
      exact Muse.reunion M H χ _ (sits Z l δ) P' hx ht hn hk L₁ hzW _ (fun z i=> ¬ virgin M H χ Z z i ∧ arity M H χ Z z i ≤ k) (fun i hi=>hi) he' hb
end YM.RemainderComparison.Muse
