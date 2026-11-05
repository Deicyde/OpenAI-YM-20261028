import YM.UVExtension.Linden.Plait
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
local notation "bX"=> M.turn.badge S
local notation "Σ"=> parade (ι:=ι) (betaF G x L) g
variable (p:Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
include B₀ hS hp ht hV hX hm hc hr h₀ Y
lemma nestling (hW:bX∈p) (hs:troupe T R Q.halo (radiusB x) p) (k:ℕ) (price : ℝ) (hh:1≤price) (hx:Lush.Shirts o L (radiusB x) price (K*j*2) k) :
    let I:= edgesM S (H.unionP p) (radiusB x); let Γ:= (F.order G).prod X.dice
    ∃ f, Integrable f Γ ∧ (∫ i, f i ∂Γ)≤ price*(1+v₀+2*(v₁+r))^j*(1+H.shapeW p)^(k+j)*(M.weight*∏ i∈p.erase bX,tabs S U (radiusB x) Q.halo B₀.toll i) ∧
       ∀ x', Brush j (f x') 1 (fun i=> cA z I (V' i) (x'.1,gStep ((z none).re) • x'.2)) τ:= by
  intro I Γ
  let s:= X.catastrophe (o.ξ/2) (z none).re (blaze (p.erase bX)); let V₀:= M.weight*∏ i∈p.erase bX, tabs S U (radiusB x) Q.halo B₀.peeled i
  let f (x:F.Slice G × Air f G):= facescale I x.2^(K*j)
  let Q':=1+H.shapeW p; let A:= V₀*(1+v₀+2*(v₁+r))^j*Q'^j
  let g (x:Air _ G):= facescale I x^(K*j); let g' := s.indicator g
  let r' := B₀.conduit.rad
  have he' : MeasurableSet s:=Poll.sounded ..
  have h':= (H.laws.data.localP _ X hX hr hm).sails
  have hi := Flux.globes I h' (K*j); obtain ⟨hp',hprice⟩:= Flux.globes I h' (K*j*2)
  have hg : Integrable g' X.dice:= hi.1.indicator he'
  have hV₀ :0 ≤ V₀ := by
    refine mul_nonneg M.profit (prod_nonneg fun i _=>?_) ; rcases i with i|i; unfold tabs Mixed.costs; dsimp only [Sum.elim]; split <;> first | exact mul_nonneg B₀.pair.capture (Real.exp_pos _).le | exact le_rfl
    exact B₀.nonneg i
  have hY:1≤ Q':= le_add_of_nonneg_right (H.positive_volume p)
  have hA:0 ≤ A:= by unfold A; have hh:= B₀.conduit.active; have h:= Y.funded; positivity
  let C_i:ℝ:= I.card; let J':ℝ:= (lensS I G).card
  have hS': C_i ≤ Q'*ballCost (radiusB x)*(Itinerary.density L:ℝ) := by
    have h:= crewsC H p; rw [H.laws.data.funds.length_eq] at h; refine h.trans ?_; dsimp only [Q']; gcongr; linarith
  have hJ:J'=C_i*Fintype.card G.ColorIndex:= by simp [J',C_i,lensS]
  have hD: ∫ x,g x^2 ∂X.dice ≤ (price*Q'^k)^2:= by
    unfold g; simp_rw [← pow_mul]; exact hprice.trans ((hx C_i J' Q' hY (Nat.cast_nonneg _) hS' hJ).trans (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hY)) (by decide)))
  have he :∫ x,g' x ∂X.dice≤ (price*Q'^k)*r'^(blaze (p.erase bX)).card:= by
    apply divideC _ g hi.1 _ (by positivity) _ he' _ (pow_nonneg B₀.conduit.awake _) _ hD
    · rw [← pow_mul,Nat.mul_comm,pow_mul]; exact B₀.conduit.ship _ X hX hr hc hm _
    unfold g; simp_rw [← pow_mul]; exact hp'
  let Ypx(x:F.Slice G× Air _ G):= A*g' x.2; have hs': Integrable Ypx Γ:=(hg.const_mul A).comp_snd _
  refine ⟨Ypx,hs',?_,?_⟩
  · rw [integral_prod _ hs']; change (∫ u, (∫ z', A*g' z' ∂X.dice) ∂F.order G)≤ _
    simp_rw [integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]
    refine (mul_le_mul_of_nonneg_left he hA).trans_eq ?_
    rw [← B₀.tabs_m (p.erase bX)]; unfold A r' Q' V₀; rw [pow_add]; ring
  intro v'; refine (pricesB N hS hF M hX hm hc hr p hp ht hV Y B₀ h₀ hs hW I v').climb ?_ le_rfl -- arguments
  by_cases ht:v'.2∈s
  · rw [Set.indicator_of_mem ht]; change _ ≤ A*g' v'.2; unfold g'; rw [Set.indicator_of_mem ht]
  rw [Set.indicator_of_notMem ht]; unfold Ypx g'; rw [Set.indicator_of_notMem ht,mul_zero]

end YM.UVExtension.Linden
