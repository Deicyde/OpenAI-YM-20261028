import YM.FullVolume.Sector.Apert
/-! Real jet exact toll & application of Rebar.Health. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "ψ" => U.pole
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "Λ" => U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
variable {p:Signal j} {ν:ℝ}
abbrev stampD (p:Molecule S):= edgesM S (H.unionP p) (radiusB x₀)
set_option quotPrecheck false
local notation "μ'"=> (F.order G).prod X.dice
abbrev angled (_M:Lyre U j u d r A' χ A b L' K) (X : Coat T F) (V:E→ Config G c) (p:Molecule S) (t:ℝ) y:= rhythm (stampD (H:=H) p) X (V y) A Q.table p (U.notes t) W o.a Q.halo
def motionR (i : Molecule S) (t:ℝ) (x:E) (y:F.Slice G×Air f G):= markL X y.2 (stampD (H:=H) i) (U.pole.flow t) • M.angled X U₀ i t x (y.1, U.pole.flow t • y.2)
def shieldS (V : E→ Config G c) (i:Molecule S) (t:ℝ) (x:E):= bars (podium S G (H.unionP i) (radiusB x₀)) (vary X (V x)) i (U.notes t) Q.table W o.a Q.halo
local notation "p₀" => M.meadow ν p
include M hx he hv hm hy hU
variable (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
include hc hr
lemma tune_rhythm (i:Molecule S)(hp: troupe T R Q.halo w₀ i)(hZ : Healthy (Pressure.temp x₀) (H.unionP i) X.V) (y:F.Slice G × Air _ G):
    let J:= stampD (H:=H) i
    Weigh j s v (price J G δ j * ((X.catastrophe (o.ξ/2) R.beta (blaze i)).indicator (fun _=>∏ k∈i,p₀ k) y.2))
      (L'*2^K*facescale J y.2^K+r*(2*H.shapeW i)) (fun t x=> motionR (U₀:=U₀) M X i t x y):=by
  intro J
  let Y:= X.wrapY y.1; let d x t:= course Y A (U.notes t).beta (U.pole.flow t • y.2) (U₀ x)
  let e' t x:= Polar.floating (vary Y (U₀ x)) o.a (U.notes t) W Q.table (d x t) (own i) Q.halo i
  let f'(t : ℝ)(x:E):= printScale (A:=A) (U:=U) Y y.2 J t (U₀ x); have h': Y.x=x₀:=hx
  refine (FullVolume.Ray.Weigh.cong ((chargeD M Y h' he hv hm hy hU y.2 J).dual (ventures M Y h' he hv hm hy hU y.2 hc hr (own i) i hp (h'.symm ▸ hZ))) ?_)
  intro t ht; filter_upwards with x; change markL X y.2 J _ * (scalp J Y (U₀ x) _ _ _ * e' t x) = f' t x * e' t x
  exact (mul_assoc ..).symm

lemma sorted (i:Molecule S)(hp:troupe T R Q.halo w₀ i)(hZ:Healthy (Pressure.temp x₀) (H.unionP i) X.V) {t:ℝ} (ht:t∈sun):
    let f:= motionR (U₀:=U₀) M X i t; let g:= shieldS (U:=U) X U₀ i t
    ContDiffAt ℝ j g s ∧ ∀ k:ℕ,k ≤ j → Integrable (JetF f k s) (μ') ∧
       iteratedFDeriv ℝ k g s = ∫ y,JetF f k s y ∂ μ' := by
  intro f g; have h':= U.lay ht; let Y:=U.beams t h'; let p:= M.plot _ h'; have hh := (p.rays F X hx he hv hm E U₀ s hy hU).1
  have hp': H.unionP i= Y.unionP i:= congr_fun (U.stage _ h') _
  let A':= angled M X U₀ i t; let I:=stampD (H:=H) i; let K':= lensS I G; let P':=U.pole.flow t; have hg : 0<P':= zero_lt_one.trans_le (U.pole.moves t h').1
  have hG:g=ᶠ[𝓝 s] fun x=> ∫ y, A' x y ∂μ' := by
    unfold g A' shieldS angled stampD; rw [hp']; exact Flux.chutes Y hx hm he hh M.pole.solid M.pole.grants _
  obtain ⟨hP,hd⟩:= Meristem.calls (U:=A') (Flux.boosts Y hx hm he hh M.pole.solid M.pole.grants i I).1
  refine ⟨hP.congr_of_eventuallyEq hG,fun k hk=> ?_⟩
  obtain ⟨hy',hD⟩:= hd k hk; let T' y:= JetF A' k s y
  have hs : StronglyMeasurable T':= gstrong Y hx hm he hh M.pole.solid M.pole.grants i I k hk
  have hv' : ∀ u v, swim K' u=swim K' v→∀ a,T' (a,u)=T' (a,v):= by
    intro u v he a
    have ht (p:E) : A' p (a,u)= A' p (a,v):= by
      let X':= X.wrapY a; have h':X'.x=x₀:=hx
      have ha : I=edgesM S (Y.unionP i) X'.B := by unfold I stampD; rw [hp',show X'.B=w₀ from congr_arg _ h'] -- Coat.B
      change recoil I X' (U₀ p) _ _ _ _ _ _ _ u=recoil I X' _ _ _ _ _ _ _ _ v
      change swim (lensS I G) u= _ at he; have hv : swim (lensS (edgesM S (Y.unionP i) X'.B) G) u= swim (lensS (edgesM S (Y.unionP i) X'.B) G) v:= by rw [←ha]; exact he
      rw [ha]; apply confined_s X' _ _ (Y.unionP i) _ Q.buys ?_ (h'.symm ▸ H.laws.data.room) (h'.symm ▸ Y.laws.intake) Q.table o.a u v hv -- inspect order
      unfold Coat.B; rw [h']; exact Finset.Subset.refl _
    exact congr_arg (fun f=> iteratedFDeriv ℝ k f s) (funext ht)
  obtain ⟨hw,hV⟩:= root_lens (M:=F.order G) X K' (H.laws.data.localP F X hx he hm |>.sails.fullC) hs hv' hy' P' hg
  have hφ (y): JetF f k s y=Lyre.markL X y.2 I P' • T' (y.1,P' • y.2):= by
    let x:= (y.1,P' • y.2)
    -- real regularity at x from ventures, without determinant.
    have h0:= U.troupe_hold t h' i|>.1 hp; let X':= X.wrapY x.1; have h': X'.x=x₀:=hx
    obtain ⟨hW,hF⟩:= (p.rays F X' h' he hv hm E U₀ s hy hU).2 x.2
    have hL:= (((hF I).1.paints (p.stencil.acreage i (Matter.own i) h0 h' hv hm he (h'.symm ▸ (hp' ▸ hZ)) hU hW)).smaller hk).smooth
    apply iteratedFDeriv_const_smul_apply' (a:=markL X y.2 I P') (show ContDiffAt ℝ k (fun v=> A' v x) s from hL)
  refine ⟨(hw.congr (ae_of_all _ fun i=> (hφ i).symm)), ((hG.iteratedFDeriv ℝ k).eq_of_nhds.trans hD).trans (hV.trans (integral_congr_ae (ae_of_all _ fun i=> (hφ i).symm)))⟩
end Lyre
end YM.ConnectedActivityE6.Empire
