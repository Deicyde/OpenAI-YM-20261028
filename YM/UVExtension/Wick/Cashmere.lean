import YM.UVExtension.Wick.Curls

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
lemma procDiff (hp:DifferentiableOn ℂ wave Bay) (i: Option ι):DifferentiableOn ℂ (fun x=> wave x i) Bay:= (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) i).differentiable.comp_differentiableOn hp
variable (y':Air f G)
local notation "S'"=> fun i:E=> steer X A (loom X y') (V' i)
local notation "F'"=> fun i:E=> sailplane X A y' (V' i)
local notation "X'"=>fun i:E=> vary X (V' i)
local notation "U"=>X.input (loom X y')
local notation "b₁"=>fun z:ℂ=> wave z none

-- assumes sample z0 real comparison. 
variable {Z:Cash W x μ L Q o a T (flight R (z none).re)} (Ξ:Utopia Z j u d r C χ)
include hX hr ht hm hF hS hY hy hc hM N hv
omit hY in
lemma ringlet (I : Finset (Bond f)) : Luster Bay τ j (fun p t=> scorched X A I (V' t) (b₁ p) y'):= by
  have h:= drift hF z hv
  have hh:= marching z|>.1 hv; have hL:= Festa.altitude (H:=H); let k:= θ; have hp:0<k:= breath hL hh.1
  obtain ⟨y,hv,h,hk,⟨H'⟩⟩:= h; let r u i:=scalp I X (V' i) u A (scaled u y')
  have he u (W : Cash W x μ L Q o a T (flight R u)): ContDiffAt ℝ (↑j) (r u) τ:=((((N.granted _ _ S T _ _ W hS rfl).2 E V' F X τ hX hc hr hm ht hM).2 (scaled u y')).2.1 I).smooth
  have hx:= he θ (oneV hF z ‹_›); have hJ:= he y H'
  have hm(u)(hu:0<u) : r u τ=1:=by unfold r; rw [ht]; exact scaleV_one X I N.bay _ hu
  let P i:= rosined X A I (V' i) y'; have hf i:r y i=r k i*Real.exp ((y-k)*P i):=by unfold P r; rw [real_ears X A I hv,real_ears X A I hp,mul_assoc,← Real.exp_add]; congr 2; ring
  have hd: y-k ≠ 0:= abs_pos.mp ((div_pos hp (by norm_num : (0:ℝ)<8)).trans_le hk)
  have hP: ContDiffAt ℝ (↑j) P τ := by
    have hg:∀ᶠ i in 𝓝 τ,r k i≠0 := hx.continuousAt.eventually_ne (by rw [hm _ hp]; exact one_ne_zero)
    refine ContDiffAt.congr_of_eventuallyEq (((hJ.log (hm y hv ▸ one_ne_zero)).sub (hx.log (hm k hp ▸ one_ne_zero))).div_const (y-k)) ?_
    filter_upwards [hg] with i hi; rw [hf i,Real.log_mul hi (Real.exp_pos _).ne',Real.log_exp]; field_simp; ring
  apply (((Luster.resting (Complex.ofRealCLM.contDiff.contDiffAt.comp τ hx)).times (Luster.powered (f:=fun t i => ((b₁ t)-(k:ℂ)) * (P i:ℂ)) ?_))).mask ?_
  swap
  · intro t ht; exact Eventually.of_forall fun i=> coal X A I hp ..
  exact (Luster.summit ((procDiff hy none).sub_const _)).times (Luster.resting (Complex.ofRealCLM.contDiff.contDiffAt.comp τ hP))

include Ξ
lemma pinion (p: Stores S) (hp:Packets.connected S Q.halo X.B p) (h:Healthy (temp X.x) (H.supportP (.inl p)) X.V) (k: Finset ℕ):
    Luster Bay τ j (fun t i=> amberP (X' i) R Q.table W o.a k Q.halo V (b₁ t) (wave t∘some) (F' i) (S' i) U (.inl p)):= by
  -- identical stilly as starbud
  have hh:= marching z|>.1 hv; have hL:= Festa.altitude (H:=H); let u':= θ; have hp':0<u':= breath hL hh.1
  obtain ⟨y,hv,hG,hK,⟨H'⟩⟩:= drift hF z hv
  have he:worldZ X (flight R θ).beta (scaled θ y')=loom X y':= fanned X y' hp'
  have hh := (N.granted _ _ S T _ _ Z hS rfl).2 E V' F X τ hX hc hr hm ht hM |>.2 (scaled θ y')
  let f i:= Polar.stock (X' i) o.a (flight R θ) W Q.table (S' i) U k p; let P i:= roots (X' i) (S' i) U p
  have hf:ContDiffAt ℝ (↑j) f τ:= by
    have ht:= (Ξ.stream E F X V' _ _ τ (scaled θ y') hX hr hc hm hM hh.1 k (.inl p) h).smooth
    apply ht.congr_of_eventuallyEq; filter_upwards with y; symm; change (if Packets.connected S Q.halo X.B p then Polar.stock _ _ _ _ _ _ _ _ _ else 0)= _; rw [if_pos hp,he]
  have hT (t i) : amberP (X' i) R Q.table W o.a k Q.halo V (b₁ t) (wave t∘some) (F' i) (S' i) U (.inl p)=warmth X θ (b₁ t) p (P i)*(f i:ℂ) := by
    unfold amberP; dsimp only [Sum.elim]; rw [if_pos (show Packets.connected S Q.halo ((vary X (V' i)).B) p from hp)]
    rw [warmth_same (vary X (V' i)) (v:=θ) _ _ _ hp', mul_comm (warmth _ 1 _ _ _),mul_assoc,
      ← plume_warm _ _ _ p zero_lt_one hp' Q.table_exists]; rfl
  let H₀ i:= X.enforce o.a (S' i) (X.plaza (p.dome (304*X.B)))
  simp_rw [hT]
  by_cases hz : H₀ =ᶠ[𝓝 τ] fun _=>0
  · have hp : f =ᶠ[𝓝 τ] fun _=>0:= by
      filter_upwards [hz] with i hi; unfold f Polar.stock; dsimp only; split; swap; · exact rfl
      change _ * H₀ i=0; rw [hi,mul_zero]
    refine (Luster.resting (f:=fun _:E=>(0:ℂ)) contDiffAt_const).mask ?_; intro t ht; filter_upwards [hp] with i hi; rw [hi,Complex.ofReal_zero,mul_zero]
  let I (z t):= plumeLog (X' t) o.a (flight R z) Q.table (S' t) U p
  have hI (z':ℝ) (hp:0<z') (Xu:Cash W x μ L Q o a T (flight R z')):ContDiffAt ℝ (↑j) (I z') τ:= by
    have he' := (((N.granted _ _ S T _ _ Xu hS rfl).2 E V' F X τ hX hc hr hm ht hM).2 (scaled z' y')).2.2
    have hv:worldZ X (flight R z').beta (scaled z' y')=loom X y':= fanned X y' hp
    simp_rw [hv] at he'; have hb : ContDiffAt ℝ (↑j) (fun i=> I z' i-I z' τ) τ:=(he' p hz U).smooth
    exact (hb.add (contDiffAt_const (c:=I z' τ))).congr_of_eventuallyEq (Eventually.of_forall fun i=>(sub_add_cancel ..).symm)
  have hd:y-θ≠0:=abs_pos.mp ((div_pos hp' (by norm_num : (0:ℝ)<8)).trans_le hK)
  let d:=amber X p*(Real.log y-Real.log u')
  have hP:P=fun t=> (I y t-I u' t-d)/(y-u'):= by
    ext i; have ht':I y i=I u' i+(y-u')*P i +d:= steer_plume (X' i) _ _ _ hp' hv Q.table_exists
    rw [ht', eq_div_iff (show y-u'≠0 from hd)]; ring
  have he : Luster Bay τ j (fun t i=> warmth X θ (b₁ t) p (P i)) := by
    unfold warmth; apply Luster.powered; apply Luster.plus; swap
    · refine Luster.summit ?_; apply DifferentiableOn.const_mul (((procDiff hy none).clog ?_).sub_const _); exact fun i hi=> Or.inl (breath hL (marching _|>.1 (hY hi)).1)
    apply (Luster.summit ((procDiff hy none).sub_const _)).times; apply Luster.resting; apply Complex.ofRealCLM.contDiff.contDiffAt.comp
    change ContDiffAt ℝ (↑j) P τ; rw [hP]; exact ((((hI y hv H').sub (hI _ hp' Z)).sub contDiffAt_const).div_const (y-u'))
  exact he.times (Luster.resting (Complex.ofRealCLM.contDiff.contDiffAt.comp τ hf))

-- write optional separately
end Bower
end YM.UVExtension.Wick
