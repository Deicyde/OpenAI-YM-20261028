import YM.UVExtension.Wick.Stature

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
variable {q : Q.rate≤γ} {hh: γ<0} {v₀ C₀ U q'' : ℝ}
local notation "Z₁"=> stalk Q q hh
namespace Outliner
variable {k:ℕ} (p'M : Outliner N hF γ q hh U v₀ C₀ q'' k)
local notation "Σ" => parade (ι:=ι) (betaF G x L) g
local notation "B'"=> radiusB x
set_option quotPrecheck false

open Stained
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E} {i:ℕ}
    (he:V' τ=X.V) (hV:Mode V' τ j u) (p:Molecule S) (hp : Healthy (temp X.x) (H.unionP p) X.V)
    (hP:(H.unionP p).Nonempty) (hΩ:(roster p).flags=∅) (Z:Fin i→ E) (hi:i≤j)

def badgeP (X:Coat T F) (_A':A=A) (s: Vines ι) := if Ac.Spark H.supportP p ∧ troupe T R Q.halo (radiusB x) p then (Fintype.card S.Choices:ℂ)⁻¹*∑ t,
    Lush.mercury (A:=A) (V:=V) (τ:=τ) (V':=V') (X:=(planted X p).taggedL t) (H:=H) p Z s else 0
local notation "Δ"=> badgeP (A:=A) (V:=V) (V':=V') (H:=H) (τ:=τ) p Z X rfl
include hi N hF hV he hc hr hX hS hp p'M
lemma lap (s : Vines ι) (hx:s∈parade (betaF G x L) g) : ‖Δ s‖ ≤ paint N hF p'M s hx p * (∏ i, ‖Z i‖):= by
  unfold badgeP; split
  next Hh =>
    let K:ℝ:=Fintype.card S.Choices; have ht' : 0<K:= by unfold K; positivity
    rw [norm_mul,norm_inv,Complex.norm_natCast]; let T':=planted X p; let M t:= Lush.mercury (τ:=τ) (A:=A) (V:=V) (V':=V') (X:=T'.taggedL t) (H:=H) p Z s
    let f:= paint N hF p'M s hx p * ∏ i, ‖Z i‖
    have hm i:‖M i‖≤f:= by
      apply (norm_integral_le_integral_norm _).trans ((cargo (X:=T'.taggedL i) N hS hF hX (planted_valid ..) hc hr p'M s hx he hV p Hh.1 hp Hh.2 Z hi).2)
    apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (s:=Finset.univ) (fun i _=> hm i))) (inv_nonneg.mpr ht'.le)).trans_eq
    rw [Finset.sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ ht'.ne']
  rw [norm_zero]; exact mul_nonneg (jetbook N hF p'M s hx|>.1 _) (prod_nonneg (fun i _=>norm_nonneg _))
include hΩ
lemma garnet (z:Drums ι) (hz: grown (betaF G x L) w z): let f t:= fringe (vary X (V' t)) W o.a p (chunk R (blend V (z∘some)) (z none)) Q.table Q.halo
    ContDiffAt ℝ (↑j) f τ ∧ Δ (hoist z)=Complex.ofReal (iteratedFDeriv ℝ i f τ Z) := by
  intro f; let I':= (planted X p); let J t:= I'.taggedL t; let A':= chunk R (blend V (z∘some)) (z none); let H':=(hF.mixture z hz).some; let r i:=shelter (vary X (V' i)) W o.a p A' Q.table Q.halo
  let I:= podium S G (H.unionP p) (radiusB x)
  have heq t := (((N.granted _ _ S T _ _ H' hS rfl).2 E V' F (J t) τ hX hc hr (planted_valid ..) he hV).1)
  have hs: Healthy (temp x) (H.unionP p) X.V:= by rw [hX] at hp; exact hp
  have hx:f=ᶠ[𝓝 τ] r:= uv_rainbow (H:=H') p heq hX hr hΩ hs
  unfold badgeP; split
  next hy =>
    let m j t:=bars I (vary (J j) (V' t)) p A' Q.table W o.a Q.halo
    have hR:=hr
    have hr t: r t=likely (fun i=>m i t):= by
      unfold r shelter; rw [show (vary X (V' t)).B=radiusB x from congr_arg _ hX]; rw [if_pos (show Ac.Spark (areas A' T Q.halo (radiusB x)) p ∧ troupe T A' Q.halo (radiusB x) p from hy)]; apply congr_arg likely; funext i; exact (spices p H' X hX (V' t) (V' t) (fun _ _ _=>rfl) hs hΩ i).symm
    let y:ℝ:= (Fintype.card S.Choices:ℝ)⁻¹; have hg i:m i =ᶠ[𝓝 τ] (fun t=>∫ ω', rhythm (edgesM S (H.unionP p) (radiusB x)) (J i) (V' t) A Q.table p A' W o.a Q.halo ω' ∂((F.order G).prod (J i).dice)):= chutes (X:=J i) H' hX (planted_valid X p) hR (heq i) N.bay N.foot _
    have hB j': ContDiffAt ℝ (↑j) (m j') τ:= ((boosts (X:=J j') H' hX (planted_valid X p) hR (heq j') N.bay N.foot p _).1.calls.1).congr_of_eventuallyEq (hg j')
    let y' i:= y • ∑ v,m v i
    have hV:f=ᶠ[𝓝 τ] y':= hx.trans (Eventually.of_forall hr)
    have hL:= ContDiffAt.sum (s:=Finset.univ) (fun i _=> hB i)
    have h': hoist z∈parade (betaF G x L) g:= marching _|>.2 ⟨hz none,fun i=> by rw [show ‖hoist z (some i)‖=‖z (some i)‖ from Complex.norm_real _]; exact (mem_ball_zero_iff.mp (hz (some i))).trans_le hF.bound⟩
    let V'' := dealP N hF p'M _ h'
    have he (i'):= Lush.gold (X:=J i') N hS hF hX (planted_valid ..) hc hR V'' he (by assumption) p hi Z z hz -- hV shadow
    refine ⟨(show ContDiffAt ℝ (↑j) y' τ from hL.const_smul _).congr_of_eventuallyEq hV,?_⟩
    have hQ (t): Lush.mercury (A:=A) (V:=V) (τ:=τ) (V':=V') (X:=(planted X p).taggedL t) _ _ (hoist z) = ((iteratedFDeriv ℝ i (m t) τ Z:ℝ):ℂ) := he t
    simp_rw [hQ]; rw [(hV.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; unfold y'; rw [iteratedFDeriv_const_smul_apply' (hL.of_le (by exact_mod_cast hi)), iteratedFDeriv_fun_sum_apply (n:=i)]; swap; · exact fun i _ => (hB i).of_le (by exact_mod_cast hi)
    unfold y; simp; exact Or.inl rfl
  next hy =>
    have hs : f=ᶠ[𝓝 τ] fun _=> 0 := hx.trans (Eventually.of_forall (fun i=> by unfold r shelter; rw [show (vary X (V' i)).B=radiusB x from congr_arg _ hX]; exact if_neg hy))
    refine ⟨contDiffAt_const.congr_of_eventuallyEq hs,?_⟩; rw [(hs.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; cases i; simp
    rw [iteratedFDeriv_succ_const]; exact Complex.ofReal_zero.symm
omit hΩ
include hP
lemma forma:Bumps Σ Δ := by
  unfold badgeP; split_ifs with hh
  · intro S' f hs hv ht; apply DifferentiableOn.const_mul; apply DifferentiableOn.fun_sum; intro i hi'
    exact glaze (X:=((planted X p).taggedL i)) N hS hF hX (planted_valid X p) hc hr p'M he hV p hh.1 hp hh.2 hP Z hi S' f hs hv ht
  exact bumps _ _ (differentiableOn_const _)
end Outliner
end Bower
end YM.UVExtension.Wick
