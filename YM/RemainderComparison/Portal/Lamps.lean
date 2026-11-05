import YM.RemainderComparison.Portal.Wire
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
structure Pan (R₀ A B:ℝ) (n r j:ℕ) (D f₀ z:ℝ) (d' v' u':ℝ) (l':ℕ)
       (i:modes ι) (Φ:Config G c→ℝ) (C d:ℝ) -- R shadows Rep.edit
       (W: ℝ×Positions (Uniform.Primary c G)→ℝ) : Prop where
    view (p:Positions (Uniform.Primary c G)) : ‖p‖ ≤ R₀ → Arc.route G R.beta p∈ Boulevard.sunny V →
      Council T F Q.table k' ρ B' R.beta E₀ W' v' u' D z A p r j n l' B f₀ ∧
      (∀ i,Playing F ρ R.beta (U i) (E i) p D z u' v' B f₀ n l') ∧
      Script V R T Φ W C i p (j+(r+1)) v' u' d' ∧
      JMatch (offer (Q:=Q) (T:=T) k' ρ U r i) W p r j d

local notation "h'" => gStep R.beta
variable {B'' Cw:ℝ} (Y:modes ι)(Φ:Config G c→ℝ)
variable (W₁ : ℝ × Positions (Uniform.Primary c G)→ℝ)
variable (hκ : Parade M T B' l E)
variable (hf:V.B=radiusB x) (hs:V.supportExponent≤a){P':Type}[Fintype P'] {X:P'→Site f} {p':ι→ Finset P'} (h:Premium Q L x a μ ε B j n k s J m Gp)(hl:Scale X p' M l m σ Gp S)(hh: Heroes H N.conduit A B n) (hH:Heavy N.conduit)(hr:radiusCost Q L σ)(hx:V.threshold=Pressure.temp x)
variable (hβ:gStep R.beta ≤1)(hK:Fintype.card ι≤K)
-- b shadow! Premium params choose b vs ε independent
variable (c₀:ℝ)
variable (HP: Pan (R:=R) (Q:=Q) (T:=T) V E k' ρ B' U R₀ C₁ B₀ n' r' V.order D f₀ v₀ B'' v' u' l' Y Φ c₀ Cw W₁)


def put (C:ℝ)(y:modes ι):=chronos (T' - W₀ +C) y

def resale (V:BudgetPoint) (A B D g:ℝ) (r K:ℕ):= g^(r+1)*(2*(A+rehearsal V.order r K A)+B)+((r:ℝ)+1)*D
include V N h hr hh hl hH HP hf hs hx hβ hK hκ
lemma earns (p : Positions (Uniform.Primary c G)) (hp : ‖p‖ ≤ R₀)(hX:Σu p∈Boulevard.sunny V):
    Brush V.order (resale V C₁ B'' Cw h' r' K) 1 (fun x=> Portal.shelf M H χ l (Σu x) Y - Φ (Σu x) - put H χ k' ρ c₀ Y) p:= by
   obtain ⟨hPi,hQ,hE,hp'⟩:= HP.view p hp hX
   have H' := Quanta V E k' ρ B' U p hPi hK hβ hQ Y
   have hs₁:= H'.site; have hV:0 ≤ gStep R.beta:= H'.coupling.le
   have hr' : ∀ᶠ y in 𝓝 (gStep R.beta,p), y ∈Germ.patch (Positions (Uniform.Primary c G)) v' u':=(Germ.patch_open ..).mem_nhds hs₁
   have ht:=Trace.vertically W₁ r' (j:=V.order) (hr'.mono fun z hz i hi=> hE.account _ (Germ.keeps hz hi))
   rw [abs_of_pos H'.coupling] at ht
   have he := (H'.projects.gathering (hp'.warms _ hV hβ)).separating ht
   refine (he.climb ?_ le_rfl).shimmy ?_
   · apply le_of_eq; unfold resale; ring
   filter_upwards [hE.chart, (sky V|>.preimage (show Continuous (Σu) from (by unfold Arc.route Boulevard.actual represent increment YM.Exterior.collect; fun_prop)))|>.mem_nhds hX] with t hb ht₀ -- Arc.continuity find
   have hX:= Portal.junction M H χ N l E B' V (F:=F) hκ (hf:=hf) hs h hl hh hH hr hx _ (Boulevard.smoky ht₀)
   obtain ⟨-,hA,hB⟩:=hX
   let f:= (Portal.exact_l (Q:=Q) (R:=R) (T:=T) E k' ρ B' Y) t
   change _= (f-Trace.trunc r' _ _ + (_ - _)) - _ -- edit
   rw [← hb]
   have he' : Portal.shelf M H χ l (Σu t) Y - Φ (Σu t) - put H χ k' ρ c₀ Y= f -(ideal (T:=T) (R:=R) V Φ Y (Σu t)+chronos c₀ Y):=by
      unfold f; unfold Portal.exact_l put ideal chronos; split_ifs with h
      · change Y=quiet ι at h; subst Y; unfold Aux.reserve_l; change _= Real.log (powder T B' R.beta (Σu t) (E (quiet ι)))-_ - _; dsimp only at hA; rw [hA]; ring
      rw [← hB Y h,sub_zero,sub_zero,add_zero]; rfl -- unfold entrant
   exact he'.trans (by abel)
end YM.RemainderComparison.Portal
