import YM.UVExtension.Linden.Rail
import YM.UVExtension.Copse.Pence
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
variable {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Γ'"=> (F.order G).prod X.dice
local notation "Λx"=> flax (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
local notation "P'"=> (F.order G).prod (volume : Measure (Body (↥ X')))
variable {q':Q.rate≤γ} {h':γ<0} {σ ω' C₀ U0:ℝ} (D': Outliner N hF γ q' h' U0 v₀ C₀ σ k)
local notation "ZV"=> Wick.stalk Q q' h'
local notation "b₁"=> Outliner.dealP N hF D'
open Lush
local notation "b'"=> radiusB x
local notation "bM"=> H.supportP bX
include D' hz Y
def titleP (p: Molecule S) :ℝ := let f:= U0*(1+v₀+2*(v₁+r))^j*M.weight; let U:= (stalk Q q' h'|>.costs L μ (z none).re x C₀); if bX ∈p ∧ Ac.Spark H.supportP p then
    f*(1+H.shapeW p)^(k+j)*(∏ i∈p.erase bX,tabs S U b' Q.halo (b₁ z hz).toll i)*Real.exp (σ* coverNumber b' (H.unionP p)) else 0
local notation "Ψ"=> titleP N hF M (v₁:=v₁) (hz:=hz) D'
-- #check signature hz likely implicit
open Push.AbsoluteSums.Trees
-- exact.N.Poster 
abbrev reasons (M: PhysicalNext.Repeat.Lotus.Leaf R) (k j:ℕ) (U v₀ v r:ℝ):= U*(1+v₀+2*(v+r))^j*M.weight*(Trees.currency b' Q.relative (H.supportP (M.turn.badge S))*polyPrice Q.ε (k+j)*Real.exp (2*Q.ε*(coverNumber R.p.B M.crest)))
set_option pp.universes false
lemma styles : SumBudget (fun i:Molecule S=> Ψ i* Real.exp ((Q.exp-σ)*coverNumber b' (H.unionP i))) (reasons (H:=H) M k j U0 v₀ v₁ r):=by
   let b:= b₁ z hz; let Q':= Wick.stalk Q q' h'; let u:= (Q'|>.costs L μ (z none).re x C₀); let d i:= Mixed.lengths S u (lengths T R) i; let g i:= tabs S u b' Q.halo b.toll i
   have hm : u.Buy S.patch.L Q.halo b':=by rw [H.laws.data.funds.length_eq]; exact b.pair
   have hp:= Mixed.ready_vertices S _ _ u H.birth b.toll _ _ hm b.acct; let v:= U0*(1+v₀+2*(v₁+r))^j*M.weight; have hr:= b.conduit.active; have hf:0≤ v:=by
      have ht:= D'.good; have hh:= D'.size; have hv:= Y.funded; have hz:= M.profit; unfold v; positivity
   have hg(i):0≤g i:=(royalties (H:=H) b.acct hm).1 _
   have hq(i): 0≤d i:=by rcases i with i|i; exact mul_nonneg hm.extra (Nat.cast_nonneg _); exact b.acct.extra i
   have hU:= Copse.salvo H.supportP b' hg bX (k+j) d (Mixed.stamp S u) hq (fun i=> mul_nonneg hm.marked (by positivity)) Q.usable Q.bound (show Trees.Ready H.supportP (radiusB x) (tariff g d (Mixed.stamp S u) Q.ε) (Q.exp+2*Q.ε) u.rootHit u.reserveTree u.q from hp)
   have ht:= budget_scale hf hU; convert! ht using 1
   · ext1 i; unfold titleP Copse.spannedW; dsimp only; split; next h=>
      let w i:= coverNumber b' (H.unionP i); change v*_ * _ * _ *_=v*(Real.exp (Q.exp* (w i:ℝ))*(1+H.shapeW i)^_*(∏ j∈i.erase bX,g j)); rw [mul_assoc _ (Real.exp ..),←Real.exp_add]; unfold w v g u Q' b; ring_nf
     ring
   change v*(currency b' Q.relative bM* _*_) =_
   have hd : d bX=(coverNumber R.p.B M.crest:ℝ):= by rw [← Daisy.sparkPath]; exact Daisy.sparkExp (T:=T) M
   unfold Reserves.weight; rw [hd]
   unfold Target.relative currency; rw [show u.reserveTree=Q.δ from rfl]; simp_rw [add_mul,mul_add,Real.exp_add]; ring

lemma affluent (p:Molecule S):0 ≤ Ψ p := nonneg_of_mul_nonneg_left ((styles N hF M Y (hz:=hz) D').1 p) (Real.exp_pos _)
local notation "p''"=> foamF (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
local notation "M!"=> marsh (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
variable (hv:Ac.Spark H.supportP p) (hW:M.turn.badge S∈p)(hw:troupe T R Q.halo (radiusB x) p)
include hX hm hc hr ht hV hS hi hv hw hp hW hl
lemma targetW : Integrable (p'' z) P' ∧ (∫ y, ‖p'' z y‖ ∂ P') ≤ Ψ p * (∏ i, ‖Z i‖):=by
    obtain ⟨ha,h⟩:= blastP N hS hF M hl hX hm hc hr p hp ht hV Y (b₁ z hz) D'.good hi Z k U0 D'.size D'.suits hW hw
    unfold titleP; dsimp only; rw [if_pos (show bX∈p∧Ac.Spark H.supportP p from ⟨hW,hv⟩)]
    have hk:= D'.boxes z hz p; rw [← chargedU (H.unionP p)] at hk
    refine ⟨ha,h.trans ((mul_le_mul_of_nonneg_right hk ?_).trans_eq ?_)⟩
    rotate_left; · ring
    let b:= b₁ z hz; let u:= (stalk Q q' h'|>.costs L μ (z none).re x C₀)
    have hm:u.Buy S.patch.L Q.halo b':=by rw [H.laws.data.funds.length_eq]; exact b.pair
    have hh:0≤(∏ i∈p.erase bX,tabs S u (radiusB x) Q.halo b.toll i):= Finset.prod_nonneg fun i _=> (royalties (H:=H) b.acct hm).1 _
    have h0 : 0≤1+H.shapeW p:= add_nonneg zero_le_one (H.positive_volume p)
    have h₀:= Y.funded; have hf:= b.conduit.active; have he:=D'.good; have hx:=D'.size; exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg M.profit hh)) (Finset.prod_nonneg fun _ _=>norm_nonneg _)
omit hz
lemma flowers : Bumps Σ M! := by
    let d':Vines ι:= fun i=> Option.elim' ((betaF G x L:ℝ):ℂ) (fun _=>0) i; have hx:d'∈parade (betaF G x L) g:= marching _|>.2 ⟨seat_in (Festa.altitude (H:=H)),fun i=> by change ‖(0:ℂ)‖<g; rw [norm_zero]; exact hF.margin.trans_le hF.bound⟩
    intro S' f h hp' ht'
    have he (i:ℂ)(hh:i∈ S') : Integrable (p'' (f i)) P' ∧ (∫ y, ‖p'' (f i) y‖ ∂P') ≤ reasons (H:=H) M k j U0 v₀ v₁ r*(∏ i, ‖Z i‖):=by
       have hz:= hp' hh; let U:= titleP N hF M (v₁:=v₁) (hz:=hz) D' p; obtain ⟨hR,hT⟩ := targetW N hS hF M hl hX hm hc hr p hp ht hV Y (z:=f i) (hz:=hz) hi Z D' hv hW hw
       refine ⟨hR,hT.trans ?_⟩; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=>norm_nonneg _)
       exact (le_mul_of_one_le_right (affluent N hF M Y (hz:=hz) D' p) (Real.one_le_exp (mul_nonneg D'.margin (Nat.cast_nonneg _)))).trans (budget_single (styles N hF M Y (hz:=hz) D') p)
    refine Lamppost.tint (F:=fun z=> p'' (f z)) (μ:=P') h (fun i=>?_ ) (fun i hi=> (he i hi).1) (fun i hi=> (he i hi).2)
    apply DifferentiableOn.mul _ (gilt N hS hF M hX hm hc hr p hp ht hV Y (b₁ d' hx) hi Z _ S' f h hp' ht'); exact bulbs_hol _ _ ((ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn ht') (fun z hz=> breath (altitude (H:=H)) ((marching _|>.1 (hp' hz)).1))
end YM.UVExtension.Linden
