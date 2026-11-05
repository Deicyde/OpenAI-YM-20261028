import YM.RemainderComparison.Portal.Lamps
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Portal
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x





open Marker Next.Rank.Glyph Next.Rank.Exponential Sleet
local notation "Yv" => veil ι
local notation "cardboard" => Stock.census ι
open Aux Fare Lapis Sienna Boulevard Exchange Push.Uniform Lantern
variable (V:BudgetPoint)(E:modes ι→ Config G f →ℝ)
variable (k':S.Choices) (ρ: Bid.Dir G c→ AxisChart G F) (B':BudgetPoint)
local notation "Vc" => Positions (Uniform.Primary c G)
local notation "Σ₀" => Poll.Body (Precision.Key F G)
local notation "g'" => gStep R.beta
local notation "E₀" => E (quiet ι)
local notation "Σu" => (Arc.route (c:=c) G R.beta)
variable (U:modes ι→ (ℝ×Positions (Uniform.Primary c G))→ Poll.Body (Precision.Key F G) →ℝ)
local notation "W'" => U (quiet ι)
variable {j' n' r' l' K:ℕ} {B₀ f₀ c₀ R₀ D v' u' ε e' x' C₁ C₂:ℝ} {K₁ : KernelChoices}


-- Given one physical torus and a reference from registered analytic germ
-- (source notation includes real alphabet bookkeeping q.Budget.L). Width alert
-- explicit. Absolute chartwise precision in left derivatives.
variable {v₀ y₀ z₀:ℝ}
local notation "T'" => Aux.tower T F Q.table k' ρ R.beta
local notation "W₀" => Song.weighty H χ F * Fintype.card (Site c)
-- MUST use independent reference, never overwrite unmasked model. RG02 supplies
-- JMatch. Permit later transfer to rotated ROOT at additional Rune costs.

variable {B'' Cw:ℝ} (Y:modes ι)(Φ:Config G c→ℝ)
variable (W₁ : ℝ × Positions (Uniform.Primary c G)→ℝ)
variable (hκ : Parade M T B' l E)
variable (hf:V.B=radiusB x) (hs:V.supportExponent≤a){P':Type}[Fintype P'] {X:P'→Site f} {p':ι→ Finset P'} (h:Premium Q L x a μ ε B j n k s J m Gp)(hl:Scale X p' M l m σ Gp S)(hh: Heroes H N.conduit A B n) (hH:Heavy N.conduit)(hr:radiusCost Q L σ)(hx:V.threshold=Pressure.temp x)
variable (hβ:gStep R.beta ≤1)(hK:Fintype.card ι≤K)
-- b shadow! Premium params choose b vs ε independent
variable (c₀:ℝ)
variable (HP: Pan (R:=R) (Q:=Q) (T:=T) V E k' ρ B' U R₀ C₁ B₀ n' r' V.order D f₀ v₀ B'' v' u' l' Y Φ c₀ Cw W₁)



-- in absence of wires meaning ordinary rooted moment Ledger.H support obligation.
-- must use the SAME independent Φ and primitive core offer.
structure Mare (V:BudgetPoint) (g: Config G c→ℝ) (β R' B:ℝ):Prop where
    valid : ∀ x:Positions (Uniform.Primary c G), ‖x‖ ≤ R'→ flags V.threshold (Arc.route G β x)=∅ →∀ t: List (Directions G c),t.length ≤ V.order→ (∀ i∈t,‖i‖≤V.threshold) →
      ‖leftDerivs g t (Arc.route G β x)‖ ≤ B

lemma rise (g : Config G c → ℝ)(hp:Arc.Tracer V G b R₀)
    (hy:∀ y:Config G c, flags V.threshold y=∅ → Push.Local.Chart V.order g y)
    (hf : ∀ w: Positions (Uniform.Primary c G), ‖w‖ ≤ R₀→ Arc.route G b w∈Boulevard.sunny V → ∀ p: List (Directions G c),p.length≤V.order→ (∀ i∈p, ‖i‖≤ V.threshold) → ‖leftDerivs g p (Arc.route G b w)‖ ≤B) : Mare V g b R₀ B:=by
   constructor; intro W he hV l hl hC; let G' (x:ℝ):= leftDerivs g l (Arc.route G b (x • W)); have hv:G' 1=leftDerivs g l (Arc.route G b W):=by unfold G'; rw [one_smul]
   have hg : Push.Local.Chart 0 (leftDerivs g l) (Arc.route G b W) := Next.Foundations.leftDerivs_chart _ _ ((hy _ hV).of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl))
   have hk : ContinuousAt G' 1:= by
     apply ContDiffAt.continuousAt (n:=0) (𝕜:=ℝ)
     refine Push.Local.chart_comp (W:=fun x=> Arc.route G b (x • W)) (k:=0) (x:=(1:ℝ)) (by rw [one_smul]; exact hg) ?_
     intro i; unfold Arc.route; simp_rw [smul_comm (gStep b)]
     exact Boulevard.radiator 1 (gStep b • W) i
   rw [← hv]; apply le_of_tendsto (hk.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds))
   filter_upwards [hp.lean c W he hV, self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with x hx hs hX
   refine hf _ ?_ hx l hl hC; rw [norm_smul,Real.norm_of_nonneg hX]; exact (mul_le_of_le_one_left (norm_nonneg _) (show x≤1 from le_of_lt hs)).trans he

-- Partial restored result regular up to seam; test on strict then closure. Keep scalar outside until RF registration. `Tally`s consumed.
local notation "fΩ" => (fun x=> shelf M H χ l x Y -Φ x- put H χ k' ρ c₀ Y)
local notation "pay" => resale V C₁ B'' Cw g' r' K
local notation "Z'" => Arc.budgetizer V.order R₀ pay
variable (α₀ : Set (Staff M H)) (μp : Config G c→ℝ){B1 B2 B3:ℝ}(hT:Arc.Tracer V G R.beta R₀)
include h hf hs h hl hx hκ H HP hr hβ hK hh hH hT
open AnalyticBridge VerifiedReset
set_option maxHeartbeats 500000 in
lemma delta (hA : α₀ ⊆ ringSet M H Y)
     (hv:Tally V (Staff M H) (heed M H χ l α₀) B1)(hy:Tally V (Staff M H) (heed M H χ l (ringSet M H Y \ α₀)) B2) {R':Type} {Xc:R'→ Config G c→ℝ}
     (hPi : Tally V R' Xc B3)(hE: ∀ U∈Boulevard.sunny V,Φ U= μp U+Portal.unite Xc U)
     (F:=(bar M H χ l α₀- μp) - fun _=> put H χ k' ρ c₀ Y)
     (ht:F=(bar M H χ l α₀ - μp)-fun _=> put H χ k' ρ c₀ Y)
     (hI: ∀ y:Config G c, flags V.threshold y=∅ → Push.Local.Chart V.order F y) :
     Mare V F R.beta R₀ (Z'+B2+B3):=by
    apply rise _ F hT hI
    intro p hz hs z hm he
    have hm' := hT.pay c p hz fΩ _ (Portal.earns M H χ N l V E k' ρ B' U Y Φ W₁ hκ hf ‹_› h hl hh hH hr hx hβ hK c₀ HP p hz hs)
    obtain ⟨h₁,h₂⟩:= hm'; let F' x:=bar M H χ l (ringSet M H Y \ α₀) x; let E' x:= Portal.unite Xc x; let v:= Σu p
    have hH' : F =ᶠ[𝓝 v] (((fΩ)-F')+E'):=by
        filter_upwards [(sky V).mem_nhds hs] with U hu; rw [ht]; dsimp only [Pi.add_apply,Pi.sub_apply]
        rw [lock M H χ l V α₀ hx hA hy hv U hu,hE U hu]; unfold F' E'; ring
    rw [(UVNext.PricedKernels.left_congr hH' z).self_of_nhds]
    obtain ⟨-,ht,hv⟩:= levy hPi _ hs; obtain ⟨-,hf,hZ⟩:= levy hy _ hs
    rw [Local.left_add z (show Push.Local.Chart _ ((fΩ)-F') _ from h₁.sub (g:=F'∘increment v) hf) (show Push.Local.Chart V.order E' _ from ht) hm, VerifiedReset.left_sub h₁ (show Push.Local.Chart V.order F' _ from hf) hm]; exact (norm_add_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (h₂ z hm he) (hZ z hm he))) (hv z hm he))
end YM.RemainderComparison.Portal
