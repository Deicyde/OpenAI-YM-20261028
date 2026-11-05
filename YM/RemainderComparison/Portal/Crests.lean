import YM.RemainderComparison.Portal.Cup
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

-- cofinite approximation of paid letters gets cost tol. Needed as seam doesn't
-- assume open beyond equality for every letter uniformly. Purchases can demand any
-- extra letters to be included before RU alignment. No finiteness assumption on
-- labels in the analytic contour & count bound. Doesn’t claim RU has selected the common
-- letters on all AUX copies (further compat proof).
section card
omit [Fintype ι] in
lemma cofinite {X:Set (Staff M H)} (h:Rendition M H χ l V X a B)(u:ℝ)(hu:0<u) : ∀ᶠ s:Finset (Staff M H) in atTop,
    Rendition M H χ l V (X\ (s:Set (Staff M H))) a u := by
   obtain ⟨w,h,hZ,hp,hQ⟩:= h.receipt
   let p i z:= if i∈ Base M H z then w z*Real.exp (a*coverNumber V.B (Base M H z)) else 0
   let f (s:Finset (Staff M H))(z:Staff M H):= if z∉s then w z else 0; have hf s z:0≤f s z:=by unfold f; split; exact h z; exact le_rfl
   have hh (i:Site c): Tendsto (fun s:Finset (Staff M H)=> ∑' j:↥((s:Set (Staff M H))ᶜ), p i j.val) atTop (𝓝 0):= tendsto_tsum_compl_atTop_zero (p i)
   filter_upwards [eventually_all.mpr (fun i=> (hh i).eventually_lt_const hu)] with s hs
   refine ⟨f s,hf s,fun i hi=>?_,fun i hi=>?_,fun x=>?_⟩
   · unfold f; split; next hg=> exact hZ i (fun h=>hi ⟨h,hg⟩)
     next=>rfl
   · rw [show f s i= _ from if_pos (show i∉s from hi.2)]; exact hp i hi.1
   let q:=fun i=> if x∈Base M H i then f s i *Real.exp (a*coverNumber V.B (Base M H i)) else 0
   have hz i:0≤ q i:=by unfold q; split; exact mul_nonneg (hf _ _) (Real.exp_pos _).le; exact le_rfl
   let S':= ((s:Set (Staff M H))ᶜ)
   have hy i : q (i:S').1=p x i.val:=by unfold q; rw [show f s i.val= w i.val from if_pos (show i.val∉s from i.2)]
   have he : Function.support q⊆ S':=by
      intro i hi; by_contra hg; apply hi
      have hs:i∈s:= not_not.mp hg; unfold q f; simp [hs]

   have hg:= ((hasSum_subtype_iff_of_support_subset he).1 (show HasSum (fun i:S'=>q i.val) _ from (show HasSum (fun i:S'=>q i.val) (∑' i:S', p x i.val) from (Summable.hasSum ((hQ x).2.1.subtype S')).congr_fun fun i=> hy i))) -- orientation
   exact ⟨hz,hg.summable,hg.tsum_eq.trans_le (hs x|>.le)⟩
end card

structure Board (V:BudgetPoint)(Ψ Γ: Config G c→ℝ) (b:ℝ):Prop where
   money : ∃ (J:ℕ → Config G c →ℝ), Tally V ℕ J b ∧ ∀ U∈Boulevard.sunny V, Ψ U=Γ U+Portal.unite J U
   chart : V.Regular univ Γ

open AnalyticBridge VerifiedReset
local notation "pay0" => resale V C₁ B'' Cw g' r' K
variable (E₁ : Set (Staff M H))(Ψ: Config G c→ℝ) {Y₀:ℝ} (Hτ:Board V Φ Ψ Y₀)
omit [Fintype ι] in
lemma capacity {z: Finset (Staff M H)} (p:Rendition M H χ l V ↑z a B) : V.Regular univ (bar M H χ l z):=by
   let f i:= Sleet.charge M H χ l i
   have ht : bar M H χ l z= ∑ i∈z, f i:= by ext x; unfold bar unite; rw [tsum_eq_sum (s:=z), Finset.sum_apply]; exact sum_congr rfl (fun i hi=>if_pos hi); exact fun i hi=> if_neg hi
   rw [ht]; apply Meadow.regularA z; intro i hi; exact CouplingShape.reg_extend ((p.receipt.choose_spec.2.2.1 i hi).1) (subset_univ _)

def pitch (v n k : ℕ)(R A P' D:ℝ) := Arc.budgetizer v R (2*(A+rehearsal v n k A)+P'+(n+1:ℕ)*D)
lemma posture_charge (k n j:ℕ){g a' b c:ℝ→ℝ}(hp:Reserve G L g)(ha:Reserve G L a')(hb:Reserve G L b)(hc:Reserve G L c) : Reserve G L fun x=> pitch j n k (g x) (a' x) (b x) (c x) := Arc.fee_rate hp ((Reserve.add ((Reserve.const _).mul (ha.add (Portal.stanza ha))) hb).add ((Reserve.const _).mul hc))
lemma clarified (hq : 1≤ R₀) (hX:Cw ≤ g' ^(r'+1)*C₂) : Arc.budgetizer V.order R₀ pay0 ≤ g'^(r'+1)*pitch V.order r' K R₀ C₁ B'' C₂:= by
   let q:=2*(C₁+rehearsal V.order r' K C₁)+B''+(r'+1:ℕ)*C₂
   have he : pay0 ≤ g' ^ (r'+1)* q:= by unfold resale q; push_cast; nlinarith only [mul_le_mul_of_nonneg_left hX (show 0≤(r':ℝ)+1 by positivity)]
   calc _ ≤ Arc.budgetizer V.order R₀ (g'^(r'+1)*q) := by unfold Arc.budgetizer Boulevard.ticket; gcongr
        _ = _ := by unfold pitch q Arc.budgetizer Boulevard.ticket; ring

local notation "ⵓ" => Staff M H
local notation "β₂" => (gStep R.beta)^(r'+1)
variable {c':ℝ}
variable (ht:Arc.Tracer V G R.beta R₀)
section
-- rg03 prepares anchored tiling using these unmasked letters. Costs include centered Ω subtract via possible RU hold rights.
include V hκ hf hs h hl hh hH hr hx hβ hK HP Hτ ht
set_option maxHeartbeats 500000 in
lemma allWeather {C₃:ℝ} (hP:Rendition M H χ l V (ringSet M H Y) a C₃)(hA:E₁ ⊆ ringSet M H Y)(hq: 1 ≤ R₀)(hX:Cw ≤ g'^(r'+1)*C₂)(hp:Rendition M H χ l V (ringSet M H Y \ E₁) a (β₂ *c')) :
      ∀ᶠ S:Finset (Staff M H) in atTop, ∀ (A:Finset (Staff M H)),(A:Set (Staff M H)) ⊆ E₁→(S:Set (Staff M H))∩ E₁ ⊆ (A:Set (Staff M H)) →
        let f:= (bar M H χ l (A:Set (Staff M H)) -Ψ) -fun _=> put H χ k' ρ c₀ Y
        let q:=β₂*(pitch V.order r' K R₀ C₁ B'' C₂ + (Fintype.card (Site c):ℝ)*(c'+1))+Y₀
        Rendition M H χ l V (ringSet M H Y \ (A:Set (Staff M H))) a (β₂*(c'+1)) ∧ V.Regular univ f∧ Mare V f R.beta R₀ q:=by
   have hu:0<β₂:= pow_pos (Fare.gS _ H.laws.intake.positive).1 _
   have he':= h.visit.posts
   filter_upwards [cofinite M H χ l V hP _ hu] with S hx' A hA' hB
   intro f v; have hv : Rendition M H χ l V (ringSet M H Y\ (A:Set (Staff M H))) a (β₂*(c'+1)):=by
      refine Rendition.weaken _ _ _ _ _ (Rendition.plus _ _ _ _ _ hp hx') (le_of_eq (by ring)) (fun i hi=>?_) le_rfl
      by_cases hz:i∈ E₁
      · exact Or.inr (And.intro hi.1 fun hi'=>hi.2 (hB ⟨hi',hz⟩))
      exact Or.inl ⟨hi.1,hz⟩
   obtain ⟨g,hT,hG⟩:=Hτ.money
   have hxA:= Rendition.weaken M H χ l V hP (B':=C₃) le_rfl (hA'.trans hA) (v:=a) le_rfl
   have hh':Tally V (Staff M H) (heed M H χ l (A:Set (Staff M H))) _:= heat M H χ l V _ hxA he'
   have hg': V.Regular univ f:= CouplingShape.reg_sub (CouplingShape.reg_sub (capacity M H χ l V hxA) Hτ.chart) (CouplingShape.reg_const _) -- edit
   refine ⟨hv,hg',⟨fun x' h' ha' z hz hy'=>?_⟩⟩ -- Mare constructor
   have hL:= delta M H χ N l V E k' ρ B' U Y Φ W₁ hκ hf hs h hl hh hH hr hx hβ hK c₀ HP (A:Set (Staff M H)) Ψ ht (hA'.trans hA) hh' (Portal.heat M H χ l V _ hv he') hT hG f rfl (fun y hy=>hg'.smooth y (by unfold Healthy; rw [hy]; simp))
   apply (hL.valid x' h' ha' z hz hy').trans; apply le_trans (add_le_add_left (add_le_add_left (clarified V hq hX) _) _); unfold v; apply le_of_eq; ring
end
end YM.RemainderComparison.Portal
