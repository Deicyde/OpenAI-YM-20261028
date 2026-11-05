import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Docket
import YM.UVExtension.Concert.Trellis
import YM.UVExtension.Concert.Lyres
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
variable (N : Wick.Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
variable {q : Q.rate≤γ} {hh:γ<0} {U v₀ C₀ q'' : ℝ} {k:ℕ} (Y:Outliner N hF γ q hh U v₀ C₀ q'' k)
variable {p:BudgetPoint} {s' t c' : ℝ}
    (J : (d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V))
    (hc:p.threshold=temp x) (hP:p.B=radiusB x) (hw:p.order≤j) (hJ: Sailor G p.threshold c' j) (hY:0≤c') (hp:j*c'≤u)
    (ht : 0<t) (hs : 0<s') (hU : AnalyticBridge.VerifiedReset.Quotes.preExponent p+t+t ≤ Q.exp - q'')
    (hW : 2^j*Outliner.award G (stalk Q q hh) x U v₀ r L μ j k ≤ s') (hv:degreePrice (radiusB x) s' t ≤ 1/2)
    (z:Vines ι) (hz:z∈parade (betaF G x L) g)
open AnalyticBridge VerifiedReset Quotes
include ht hs hW hU hv hz
lemma pure_pay : Ac.Hit (Song.perf H) (radiusB x) (fun i=> mug N hF Y i z) (preExponent p+t) (s'*(1-1/2)⁻¹):=by
  let f i:=(2:ℝ)^j*ivy N hF Y z i
  let a:=preExponent p; let B₀:=radiusB x
  have he(o':Site c): SumBudget (fun v:H.ThinP=>if o'∈ H.smallAt v then f v*Real.exp ((a+t+t)*coverNumber B₀ (H.smallAt v)) else 0) s':=by
    have hp:= budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective ((Outliner.jetbook N hF Y z hz).2 o')
    have hh := budget_scale (show (0:ℝ) ≤ 2^j by positivity) hp
    apply budget_loosen _ hW; refine budget_mono hh (fun z=>?_) fun i=>?_
    · split; next => exact mul_nonneg (mul_nonneg (by positivity) (ivy_nn N hF Y _ _)) (Real.exp_pos _).le
      exact le_rfl
    split; next hx =>
      try dsimp only
      rw [if_pos (show o'∈ H.unionP i.val from hx)]; unfold f ivy; rw [dif_pos hz,← mul_assoc]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg _))) (mul_nonneg (by positivity) (Outliner.jetbook N hF Y z hz|>.1 _))
    exact hh.1 _
  have hb: Ready H.smallAt B₀ f (a+t) s' t (1/2):= ⟨hs,ht,hv,by norm_num,fun i=>mul_nonneg (by positivity) (ivy_nn N hF Y z i),he⟩
  have ha:0≤a+t:= by unfold a preExponent; linarith [p.exponent_pos]
  intro y; have hh := log_hit_tail _ _ B₀ H.testS hb ha 0 y; simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hh; exact hh
-- exponent transfer via actual cluster site bounds, retaining lift fore Atlas cost

def grove (H:Cash W x μ L Q o a T R) (i:H.fragrances): ℝ:=shiftG x * (1 + coverNumber (radiusB x) (Song.perf H i))
omit ht hs hW hU hv hz in lemma grove_ge (i:H.fragrances) : 1≤ grove H i:= by
  apply one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (le_add_of_nonneg_right (Nat.cast_nonneg _))
def day (i:H.fragrances) (z: Vines ι) (ℓ:ℕ):= 2*grove H i^(ℓ*j)*mug N hF Y i z
def guide (G:Gauge) (t:ℝ) (x:ℝ) (j k:ℕ) (s:ℝ):= 2*collars G t x j k*(s*(1-1/2)⁻¹)
include hP
lemma tabulation (ℓ : ℕ) : coinE (Beam.dashboard H) p (preExponent p) (fun i=> day N hF Y i z ℓ) (guide G t x j ℓ s'):=by
  intro d; have he:= pure_pay N hF Y ht hs hU hW hv z hz d; let a:=preExponent p
  let C:=2*collars G t x j ℓ; have hC : 0≤C:=by unfold C collars Reserves.polyPrice shiftG; positivity
  refine budget_mono (budget_scale hC he) ?_ ?_
  · intro i; split; next => exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans (grove_ge i)) _)) (mug_nn N hF Y i z)) (Real.exp_pos _).le
    exact le_refl _
  intro i; split
  next hx =>
    have hp : d∈Song.perf H i := hx ▸ ((Beam.see H i) ▸ (Beam.dashboard H i).anchor)
    rw [if_pos hp]; unfold day grove; dsimp only; rw [hP,Beam.see]; let k:ℝ:= coverNumber (radiusB x) (Song.perf H i); let L:= mug N hF Y i z
    have hz : 0≤k:= Nat.cast_nonneg _; have ha:0≤ 2*(shiftG x)^(ℓ*j):= by unfold shiftG; positivity
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_cost ht hz (ℓ*j)) ha) (mug_nn N hF Y i z)) (Real.exp_pos (a*k)).le
    change 2*(shiftG x*(1+k))^_*L*Real.exp (a*k) ≤ C*(L*Real.exp ((a+t)*k)); rw [mul_pow,← mul_assoc]; refine hb.trans_eq ?_; unfold C collars Reserves.polyPrice L; rw [add_mul, Real.exp_add]; ring
  exact (budget_scale hC he).1 _

include hJ hp hY hc hw hS Y
omit hz
-- invoices real smooth via captain deployed normally
lemma visaE (ℓ:ℕ)(hℓ:p.power≤ℓ) (hg:∀ d,smoothP p (Beam.dashboard H) (Song.sequence H (fleet d J H) χ)) : Nonempty (ticketR (aperture hF) p (Beam.dashboard H) (preExponent p) (fun d=> Song.sequence H (fleet d J H) χ) (fun _=> guide G t x j ℓ s')):=by
  let L:= Beam.dashboard H
  have hΨ (i:H.fragrances): (L i).support=Song.perf H i:= Beam.see ..
  have he(i:H.fragrances)(w:Tap p G (L i).site (L i).support) : ∃ g' : Vines ι → ℂ, Bumps (aperture hF).span g'∧ (∀ d,g' ((aperture hF).call d)= ↑(w.read (Song.sequence H (fleet d J H) χ i)))∧∀ z∈(aperture hF).span,‖g' z‖≤ day N hF Y i z ℓ:=by
    let Y':= grove H i; let f := mug N hF Y i
    have hi : 1≤ Y':= grove_ge i; let U' : ℝ:= s'*(1-1/2)⁻¹; have hk : 0≤U':= by unfold U'; positivity
    have hM(y:Vines ι)(hy:y∈(aperture hF).span): 0≤f y ∧ f y ≤ U':=by
      have hb:= mug_nn N hF Y i y
      have hx:= budget_single (pure_pay N hF Y ht hs hU hW hv y hy (L i).site) i; rw [if_pos (show (L i).site∈ Song.perf H i from hΨ i ▸ (L i).anchor)] at hx
      have ha:0≤ preExponent p+t:= by unfold preExponent; linarith [p.exponent_pos]
      exact ⟨hb,(le_mul_of_one_le_right hb (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))).trans hx⟩
    obtain ⟨g',h,hx,ha⟩:= conduct (T:=aperture hF) (fun d => Song.sequence H (fleet d J H) χ i) hJ hY hp hw (fun d=> hg d i) w f (by
      intro E A B T V τ hτ hE
      have ht : Healthy (temp x) (Song.perf H i) (V τ):= by rw [hτ, ← hc,← hΨ]; exact w.live
      obtain ⟨g',h,hK⟩:= shells N hS hF Y V τ hE J i ht
      refine ⟨fun z x'=> (((-1:ℝ):ℂ))*g' z x', (Twist.plus (-1)).times h,fun z hz=>?_⟩
      simpa only [Complex.norm_real,norm_neg,norm_one,one_mul] using! scales (hK z hz) ((-1:ℝ):ℂ)) (by
        intro y hy
        have hs: (separation y (L i).site:ℝ) ≤ (coverNumber (radiusB x) (Song.perf H i):ℝ)*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ):= by exact_mod_cast Corona.extent (Song.perf H i) (radiusB x) (hΨ i ▸ hy) (hΨ i ▸ (L i).anchor)
        unfold Y' grove shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) hi hM hk
    exact ⟨g',h,hx,fun z hz=> (ha z hz).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hi (Nat.mul_le_mul_right j hℓ)) (by norm_num)) (hM z hz|>.1))⟩
  choose g' he ha hb using he; refine ⟨⟨fun z i w=> g' i w z,fun d i w=> ha i w d, fun i w=> he i w,fun z hz=>?_⟩⟩
  refine ⟨fun i=>day N hF Y i z ℓ,fun i=> ⟨?_,fun w=> hb i w z hz⟩,(singers _ _).2 (tabulation N hF Y hP ht hs hU hW hv z hz ℓ)⟩
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans (grove_ge i)) _)) (mug_nn N hF Y i z)
end YM.UVExtension.Concert
