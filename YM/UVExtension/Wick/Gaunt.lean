import YM.UVExtension.Wick.Grains

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)

variable {z : Vines ι} {hv:z∈parade (betaF G x L) g}
namespace Lush
variable {J : Mixed.Costs} {v₀ : ℝ} (hK:Lush N hF z hv v₀ J) (hp:0≤v₀)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E} (he:V' τ=X.V) (hc': X.χ=χ)
    (hV:Mode V' τ j u)

set_option quotPrecheck false
local notation "φ"=> cockpit X A o.a W
local notation "ψ'"=> hK.peeled
local notation "μ'"=> (F.order G).prod X.dice
local notation "θ"=> (z none).re
variable (x' : Molecule S)
-- Brush on normalized real at ζ. use each label tested by many z's BUT one tag sample. partition q* bound.
include he hm hS hc' hr hp hV hX hK

omit he hm hS hc' hr hp hV hX hK

def Shirts (o : Target.Order G W) (L : Side) (B:ℕ) (p : ℝ) (j k : ℕ) := let g:=payE o.eta o.gap o.ample (tubularPrice G L)
    ∀ (ι κ e:ℝ),1≤e → 0≤ι → ι≤e*ballCost B*(Itinerary.density L:ℝ) → κ=ι*(Fintype.card G.ColorIndex) →
    (1+ι+κ+κ)^j*(1+κ*(2*Real.exp (g*(j:ℝ)^2/2))) ≤ p*e^k
lemma flutes (L:Side) (o : Target.Order G W) (j:ℕ):∃ (p : ℝ→ℝ) (k:ℕ), Rate G L 0 p ∧ ∀ x:ℝ,1 ≤ p x ∧ Shirts o L (radiusB x) (p x) j k:= by
  obtain ⟨A,n,h,hp⟩:= walksW G L (payE o.eta o.gap o.ample (tubularPrice G L)) j; have hy:=h.compare (v:=fun x=>|A x|) (Eventually.of_forall fun i=> (abs_abs _).le)
  refine ⟨(fun x=> 1+|A x|),n,(Rate.const 1).add hy,fun x=>⟨le_add_of_nonneg_right (abs_nonneg _),?_⟩⟩
  intro i k e he hh hq hg
  exact (hp x i k e he hh hq hg).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans he) n))

include he hm hS hc' hr hp hV hX hK

lemma booths (p:Molecule S) (hq:Healthy (temp X.x) (H.unionP p) X.V) (hs:troupe T R Q.halo (radiusB x) p) (k:ℕ) (U : ℝ) (hh:1≤U) (hx:Shirts o L (radiusB x) U (K*j*2) k) :
    let I:= edgesM S (H.unionP p) (radiusB x); let Γ:= (F.order G).prod X.dice
    ∃ f, Integrable f Γ ∧ (∫ i, f i ∂Γ)≤ U*(1+v₀+2*r)^j*(1+H.shapeW p)^(k+j)*(∏ i∈p,tabs S J (radiusB x) Q.halo hK.toll i) ∧
       ∀ x', Brush j (f x') 1 (fun i=> cockpit X A o.a W p R Q.table Q.halo V z I (V' i) (x'.1,gStep ((z none).re) • x'.2)) τ:= by
  intro I Γ
  let s:= X.catastrophe (o.ξ/2) (z none).re (blaze p); let V₀:= ∏ i∈p, tabs S J (radiusB x) Q.halo hK.peeled i
  let f (x:F.Slice G × Air f G):= facescale I x.2^(K*j)
  let Q':=1+H.shapeW p; let A:= V₀*(1+v₀+2*r)^j*Q'^j
  let g (x:Air _ G):= facescale I x^(K*j); let g' := s.indicator g
  let r' := hK.conduit.rad
  have he' : MeasurableSet s:=Poll.sounded ..
  have h':= (H.laws.data.localP _ X hX hr hm).sails
  have hi := Flux.globes I h' (K*j); obtain ⟨hp',hU⟩:= Flux.globes I h' (K*j*2)
  have hg : Integrable g' X.dice:= hi.1.indicator he'
  have hV₀ :0 ≤ V₀ := by
    refine prod_nonneg fun i _=>?_ ; rcases i with i|i; unfold tabs Mixed.costs; dsimp only [Sum.elim]; split <;> first | exact mul_nonneg hK.pair.capture (Real.exp_pos _).le | exact le_rfl
    exact hK.nonneg i
  have hY:1≤ Q':= le_add_of_nonneg_right (H.positive_volume p)
  have hA:0 ≤ A:= by unfold A; have hh:= hK.conduit.active; positivity
  let C_i:ℝ:= I.card; let J':ℝ:= (lensS I G).card
  have hS': C_i ≤ Q'*ballCost (radiusB x)*(Itinerary.density L:ℝ) := by
    have h:= crewsC H p; rw [H.laws.data.funds.length_eq] at h; refine h.trans ?_; dsimp only [Q']; gcongr; linarith
  have hJ:J'=C_i*Fintype.card G.ColorIndex:= by simp [J',C_i,lensS]
  have hD: ∫ x,g x^2 ∂X.dice ≤ (U*Q'^k)^2:= by
    unfold g; simp_rw [← pow_mul]; exact hU.trans ((hx C_i J' Q' hY (Nat.cast_nonneg _) hS' hJ).trans (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hY)) (by decide)))
  have he :∫ x,g' x ∂X.dice≤ (U*Q'^k)*r'^(blaze p).card:= by
    apply divideC _ g hi.1 _ (by positivity) _ he' _ (pow_nonneg hK.conduit.awake _) _ hD
    · rw [← pow_mul,Nat.mul_comm,pow_mul]; exact hK.conduit.ship _ X hX hr hc' hm _
    unfold g; simp_rw [← pow_mul]; exact hp'
  let Y(x:F.Slice G× Air _ G):= A*g' x.2; have hs': Integrable Y Γ:=(hg.const_mul A).comp_snd _
  refine ⟨Y,hs',?_,?_⟩
  · rw [integral_prod _ hs']; change (∫ u, (∫ z', A*g' z' ∂X.dice) ∂F.order G)≤ _
    simp_rw [integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]
    refine (mul_le_mul_of_nonneg_left he hA).trans_eq ?_
    rw [← hK.tabs_m p]; unfold A r' Q' V₀; rw [pow_add]; ring
  intro v'; refine (shawl N hS hF hX hm hr hK hp ‹_› hc' hV p hq hs I _).climb ?_ le_rfl -- arguments
  by_cases ht:v'.2∈s
  · rw [Set.indicator_of_mem ht]; change _ ≤ A*g' v'.2; unfold g'; rw [Set.indicator_of_mem ht]
  rw [Set.indicator_of_notMem ht]; unfold Y g'; rw [Set.indicator_of_notMem ht,mul_zero]
end Lush
end Bower
end YM.UVExtension.Wick
