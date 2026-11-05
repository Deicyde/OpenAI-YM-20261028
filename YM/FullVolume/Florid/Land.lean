import YM.FullVolume.Florid.Crow
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d f')
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "τ" => (Rv).turn.badge S
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)

variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
local notation "m'"=> (F.order G).prod X.dice
local notation "m₀"=> M.meadow ν p
set_option quotPrecheck false
def anglesL (_M:Lyre U j u d r A' χ A b L' K) (V:Mill U) (X : Coat T F) (L:E→ Config G c) (p:Molecule S) (t:sun) y:= (V.flies t).carat (stampD (H:=H) p) X (L y) A Q.table p W o.a Q.halo
def skyL (i : Molecule S) (t:sun) (x:E) (y:F.Slice G×Air f G):= markL X y.2 (stampD (H:=H) i) (U.pole.flow t) • anglesL M V X U₀ i t x (y.1, U.pole.flow t • y.2)
def fence (Y : E→ Config G c) (i:Molecule S) (t:sun) (x:E):= (V.flies t).cinema (vary X (Y x)) i W o.a Q.table Q.halo (podium S G (H.unionP i) (radiusB x₀))
section
variable (H' : Cash W x₀ μ L Q o C T R)
def bankHere (h:X.x=x₀) : Cash W X.x μ L Q o C T R:= h.symm ▸ H'
lemma bankCoin (h:X.x=x₀)(i:Molecule S):(bankHere X H' h).unionP i=H'.unionP i:=by unfold Cash.unionP Cash.supportP Cash.birth; rw [h] -- no H' dependent.T
end
include hx he hv hm hy hU M
section coherence
include D hc hr
lemma orbit (i:Molecule S)(hp: troupe T R Q.halo w₀ i)(hT: (V.pole).turn.badge S∈i)(hZ : Healthy (Pressure.temp x₀) (H.unionP i) X.V) (y:F.Slice G × Air _ G):
    let J:= stampD (H:=H) i
    Weigh j s v (price J G δ j * ((X.catastrophe (o.ξ/2) R.beta (blaze i)).indicator (fun _=> V.pole.weight*∏ k∈i.erase ((V.pole).turn.badge S),m₀ k) y.2))
      (L'*2^K*facescale J y.2^K+(r+f')*(2*H.shapeW i)) (fun t x=> Jams.phraseS (fun t:sun=> skyL (U₀:=U₀) M V X i t x y) t):=by
  intro J
  let Y:= X.wrapY y.1; have h':Y.x=x₀:=hx
  refine (((chargeD M Y h' he hv hm hy hU y.2 J).dual (plume M V D Y h' he hv hm hy hU _ hc hr i hT hp (hx.symm ▸ hZ))).cong ?_)
  intro t ht; let t':sun:=⟨t,ht⟩
  filter_upwards with x; unfold Jams.phraseS pinch; rw [dif_pos ht]; unfold skyL anglesL printScale Leaf.carat Leaf.chimes; dsimp only; rw [smul_eq_mul,← mul_assoc] <;> rfl
omit D hc hr
end coherence
include D in
lemma cleaned (i:Molecule S)(hp:troupe T R Q.halo w₀ i)(hZ:Healthy (Pressure.temp x₀) (H.unionP i) X.V) (t:sun)(hk': V.pole.turn.badge S∈i):
    let f:= skyL (U₀:=U₀) M V X i t; let g:= fence V X U₀ i t
    ContDiffAt ℝ j g s ∧ ∀ k:ℕ,k ≤ j → Integrable (JetF f k s) (m') ∧
       iteratedFDeriv ℝ k g s = ∫ y,JetF f k s y ∂ m' := by
  intro f g; have h':= U.lay t.property; let Y:=U.beams t h'; let p:= M.plot _ h'; have hh := (p.rays F X hx he hv hm E U₀ s hy hU).1
  have hp': H.unionP i= Y.unionP i:= congr_fun (U.stage _ h') _
  let A':= anglesL M V X U₀ i t; let I:=stampD (H:=H) i; let K':= lensS I G; let P':=U.pole.flow t; have hg : 0<P':= zero_lt_one.trans_le (U.pole.moves t h').1
  let hB:=H.laws.data.funds.length_eq; let J:=bankHere X Y hx; have hA:8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2:= by rw [hx,hB];exact M.pole.grants
  have hG:g=ᶠ[𝓝 s] fun x=> ∫ y, A' x y ∂m' := by
    -- Align charged head, since Grass sees TRUE Coat budget on H.beams but stamped by exact sum.
    let hE : X.B=w₀:= congr_arg _ hx
    -- Cash path. Cast for any P.
    let J:= bankHere X Y hx
    have hf:= (V.flies t).chutes X i J he hm hh M.pole.solid (show 8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2 from by rw [hx,H.laws.data.funds.length_eq]; exact M.pole.grants)
    rw [hE,show J.unionP i= _ from (bankCoin X Y hx i).trans hp'.symm] at hf; exact hf
  obtain ⟨hP,hd⟩:= Meristem.calls (U:=A') ((V.flies t).boosts X i J he hm I hh M.pole.solid hA).1
  refine ⟨hP.congr_of_eventuallyEq hG,fun k hk=> ?_⟩
  obtain ⟨hy',hD⟩:= hd k hk; let T' y:= JetF A' k s y
  have hs : StronglyMeasurable T':= (V.flies t).lstrong X i J he hm I hh M.pole.solid hA k hk
  have hv' : ∀ u v, swim K' u=swim K' v→∀ a,T' (a,u)=T' (a,v):= by
    intro u v he a
    have ht (p:E) : A' p (a,u)= A' p (a,v):= by
      let X':= X.wrapY a; have h':X'.x=x₀:=hx
      have ha : I=edgesM S (Y.unionP i) X'.B := by unfold I stampD; rw [hp',show X'.B=w₀ from congr_arg _ h'] -- Coat.B
      change (V.flies t).chimes X' i I (U₀ p) _ _ _ _ _ u=(V.flies t).chimes X' i I (U₀ p) _ _ _ _ _ v
      change swim (lensS I G) u= _ at he; have hv : swim (lensS (edgesM S (Y.unionP i) X'.B) G) u= swim (lensS (edgesM S (Y.unionP i) X'.B) G) v:= by rw [←ha]; exact he
      exact Leaf.confined_s (V.flies t) X' i J I (d:=A) (Y.unionP i) (show ground (U.notes t) T Q.halo X'.B i⊆ Y.unionP i from by rw [show X'.B=w₀ from congr_arg _ h']; exact Subset.refl _) (U₀ p) ha o.a u v he
    exact congr_arg (fun f=> iteratedFDeriv ℝ k f s) (funext ht)
  obtain ⟨hw,hV⟩:= root_lens (M:=F.order G) X K' (H.laws.data.localP F X hx he hm |>.sails.fullC) hs hv' hy' P' hg
  have hφ (y): JetF f k s y=Lyre.markL X y.2 I P' • T' (y.1,P' • y.2):= by
    let x:= (y.1,P' • y.2)
    -- real regularity at x from ventures, without determinant.
    have h0:= U.troupe_hold t h' i|>.1 hp; let X':= X.wrapY x.1; have h': X'.x=x₀:=hx
    obtain ⟨hW,hF⟩:= (p.rays F X' h' he hv hm E U₀ s hy hU).2 x.2
    let l:= V.flies t
    have hD:=blooms (Ra:=l) (H:=Y) X' _ D hW h' hv; rw [← show X'.B=w₀ from congr_arg _ h'] at hD
    have hL:= (((hF I).1.paints (Daisy.acreage l X' Y p.stencil h0 (show l.turn.badge S∈ i from (V.kind t).symm ▸ hk') (Matter.own i) h' he hv hm (h'.symm ▸ (hp' ▸ hZ)) hU hW D.1 hD)).smaller hk).smooth
    apply iteratedFDeriv_const_smul_apply' (a:=markL X y.2 I P') (show ContDiffAt ℝ k (fun v=> A' v x) s from hL)
  refine ⟨(hw.congr (ae_of_all _ fun i=> (hφ i).symm)), ((hG.iteratedFDeriv ℝ k).eq_of_nhds.trans hD).trans (hV.trans (integral_congr_ae (ae_of_all _ fun i=> (hφ i).symm)))⟩
end Mill
end YM.ConnectedActivityE6.Empire.Imago
