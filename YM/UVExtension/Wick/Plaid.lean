import YM.UVExtension.Wick.Cashmere

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
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' t n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable (z : Vines ι) (hv:z∈parade (ι:=ι) (betaF G x L) g)
set_option quotPrecheck false
local notation "β" => z none
local notation "θ" => (z none).re
local notation "Ψ" => z ∘ some
variable (hq : ‖z none‖/ (z none).re≤2)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E}
    (ht:V' τ=X.V) (hM:Mode V' τ j u)
local notation "S₁"=> steer X A
local notation "P₁"=> warmth X
variable {Bay : Set ℂ} {wave:ℂ→ Vines ι} (hU: Stamp T) -- already hS
variable (hj:IsOpen Bay) (hY: Set.MapsTo wave Bay (parade (betaF G x L) g)) (hy:DifferentiableOn ℂ wave Bay)
variable (y':Air f G)
local notation "S'"=> fun i:E=> steer X A (loom X y') (V' i)
local notation "F'"=> fun i:E=> sailplane X A y' (V' i)
local notation "X'"=>fun i:E=> vary X (V' i)
local notation "U"=>X.input (loom X y')
local notation "b₁"=>fun z:ℂ=> wave z none

-- assumes sample z0 real comparison. 
variable {Z:Cash W x μ L Q o a T (flight R (z none).re)} (Ξ:Utopia Z j u d r C χ)
include hX hr ht hm hF hS hY hy hc hM N hv

omit hy hv hF hY in
lemma torus (y :ℝ) {R':Rep G f} (h:R'.beta=y) (H':Cash W x μ L Q o a T R') (Ψ':Utopia H' j u d r C χ)
    (i:LogIndex c f) (hp:Healthy (temp X.x) (H'.supportP (.inr (.inr (.inl i)))) X.V) :
    ContDiffAt ℝ (↑j) (fun t=> logMoment (X' t) o.a R' Q.table (S' t) U (scaled y (F' t)) i) τ:= by
  let q t:=logMoment (X' t) o.a R' Q.table (S' t) U (scaled y (F' t)) i
  have h := (ornate N hS hX hm hc hr ht hM y' ∅ h H' Ψ' (.inr (.inl i)) hp).smooth
  have hh:ContDiffAt ℝ (↑j) (fun t=>Real.exp (q t)-1) τ:=h
  have hv:ContDiffAt ℝ (↑j) (fun t=>Real.exp (q t)) τ:=by
    refine (hh.add (contDiffAt_const (c:=1))).congr_of_eventuallyEq (Eventually.of_forall fun i=> (sub_add_cancel _ _).symm)
  change ContDiffAt ℝ (↑j) q τ; exact (hv.log (Real.exp_pos _).ne').congr_of_eventuallyEq (Eventually.of_forall fun i=>(Real.log_exp _).symm)
include Ξ hj
lemma bazar (p: Alphabet c f) (h:Healthy (temp X.x) (H.supportP (.inr p)) X.V) (k: Finset ℕ): Luster Bay τ j
    (fun t i=> amberP (X' i) R Q.table W o.a k Q.halo V (b₁ t) (wave t∘some) (F' i) (S' i) U (.inr p)):= by
  have he:= marching z|>.1 hv; let A' i:= (hF.kin i _ he.1).some; let y:=θ; have hp:0<y:= breath (Festa.altitude (H:=H)) he.1
  let Z₀ i:= ((N.granted _ _ S T _ _ (A' i) hS rfl).1).some
  rcases p with i|i|i
  · unfold amberP; dsimp only [Sum.elim]
    apply Luster.pluses; intro t _; apply (Luster.summit (procDiff hy (some t))).times (Luster.resting ?_)
    exact (rises (ornate N hS hX hm hc hr ht hM y' k rfl (A' t) (Z₀ t) (.inl i) h)).smooth
  · let f t j:= valRay (X' j) R V o.a Q.table (S' j) U (F' j) (b₁ t) (wave t∘some) i
    let g R t:= logMoment (X' t) o.a R Q.table (S' t) U (scaled y (F' t)) i
    have hp' t j: f t j=(if madeE i then ∑ v, wave t (some v)*(g (chunk R (V v) y) j:ℂ) else (if betaBit i then wave t none/(y:ℂ) else 1)*(g (flight R y) j:ℂ)):= (loftR (X' j) V R (a:=o.a) (Z:=Q.table) (z:=F' j) (S' j) U (wave t none) hp (wave t∘some) i).2
    have hF : Luster Bay τ j f:= by
      have hh:=torus N hS hX hm hc hr ht hM y' y rfl Z Ξ i h
      rw [show f=_ from funext (fun i=> funext fun j=> hp' i j)]; split_ifs
      · apply Luster.pluses; intro t _
        exact (Luster.summit (procDiff hy (some t))).times (Luster.resting (Complex.ofRealCLM.contDiff.contDiffAt.comp τ (torus N hS hX hm hc hr ht hM y' y rfl (A' t) (Z₀ t) i h)))
      all_goals apply (Luster.summit ?_).times (Luster.resting (Complex.ofRealCLM.contDiff.contDiffAt.comp τ hh)); first | exact (procDiff hy none).div_const _ | exact differentiableOn_const _
    have hx: Luster Bay τ j (fun t i=> Complex.exp (f t i)+(-1:ℂ)):= hF.powered.plus (Luster.resting contDiffAt_const)
    simp only [amberP,sub_eq_add_neg,Sum.elim]; exact hx
  exact Luster.resting (rises (ornate N hS hX hm hc hr ht hM y' k rfl Z Ξ (.inr (.inr i)) h)).smooth
lemma crests (p : Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V) (Y:F.Slice G × Air f G) (I : Finset (Bond f)) :
    Luster Bay τ j (fun t i=> cockpit X A o.a W p R Q.table Q.halo V (wave t) I (V' i) Y):= by
  rcases Y with ⟨y,z'⟩; let T':= X.wrapY y
  refine Luster.mask (f:=fun t i=> held X A o.a W p R Q.table Q.halo V (wave t) I (V' i) (y,z')) ?_ (fun t ht'=> (hF.hovers hX hr hm hM ht p N.bay N.foot (hY ht') I (y,z')).symm)
  unfold held; dsimp only
  apply (ringlet (X:=T') N hS hF hX hm hc hr z hv ht hM hy z' I).times (Luster.poll p _ ?_)
  intro i hi
  have hp : Healthy (temp T'.x) (H.supportP i) T'.V := Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hp
  rcases i with i|i; swap; · exact bazar (X:=T') N hS hF hX hm hc hr z hv ht hM hj hY hy z' Ξ i hp (Matter.own p)
  by_cases hh: Packets.connected S Q.halo X.B i
  · exact pinion (X:=T') N hS hF hX hm hc hr z hv ht hM hY hy z' Ξ i hh hp (Matter.own p)
  refine (Luster.resting (f:=fun _:E=>(0:ℂ)) contDiffAt_const).mask (fun i _=> Eventually.of_forall fun y=> ?_); exact if_neg hh
end Bower
end YM.UVExtension.Wick
