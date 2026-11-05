import YM.RemainderComparison.Herbal.Patch
import YM.RemainderComparison.Gaussian.Cargo
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k m : ℕ} {Z σ C D W A v u d e t a U₀:ℝ}
variable {c f : Side} {S : StepData c f}
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ)
variable (E:Config G f→ℝ) (t u : ℝ)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "ℤs" => Xs×Y
local notation "θ" => Lapis.orbit F ρ
local notation "v'" => eaves G L t
local notation "A'" => Access.apron G L t
local notation "D'" => wick G L d t
local notation "e'" => furl G L t
local notation "g₁" => gStep β

def entice := Uniform.fine G F ∘ (combineH (G:=G) F)
def models := Germ.baggage (E ∘ (entice F)) (Lapis.orbit F ρ)
def matte (r j:ℕ) := Germ.promote (models F ρ E) j r
def worn (P:Config G f →ℝ)(g':ℝ)(j r:ℕ) (U: Config G f):= (g')^r * (g'^j)⁻¹ * P U

lemma urging (x:Xs) (z:Y) : entice (G:=G) F (usage θ z (g₁,x))=F.drape (Aux.piece F ρ β (g₁ • x) z):= by
  unfold Germ.usage Germ.kite Lantern.visit; rw [one_smul]; rfl
lemma undercover (ht:PaintSupply G k Z): Inputs (entice (G:=G) F) k (fineCost G k Z) := by
  let L:=(combineH (G:=G) F).toContinuousLinearMap; have he:=feesComb (G:=G) F
  have hf:= fine_supply F ht; refine ⟨(congr_arg (Uniform.fine G F) (map_zero L)).trans hf.1,hf.2.1,?_⟩
  intro i z hz
  have h : ‖L z‖≤ 1:= (L.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans hz)
  let f' (y:Positions (Uniform.Joint F G)):= G.mat (Uniform.fine G F y i); have hg:Allows k f' (L z) _:= hf.2.2 i (L z) h
  have hP : Brush k _ 1 f' (L z):= Brush.offer.mpr ⟨hg.analytic.of_le le_top,hg.norm_le⟩
  have hH:= hP.reading L he; rw [one_mul] at hH
  exact ⟨hg.analytic.comp z L.contDiff.contDiffAt,fun i hi=> (offer.mp hH).inside i hi⟩
variable {p q U H:ℝ→ℝ} {x:Positions (Uniform.Primary c G)} {e t u β:ℝ} {K:KernelChoices} {O:Teller G}

structure Climate (G:Gauge)(L:Side)(t d u C β:ℝ):Prop where
  g_pos : 0< gStep β
  below : gStep β < Access.apron G L t
  next : Access.apron G L t < eaves G L t
  width : Access.apron G L t * u ≤ eaves G L t
  budget : C*eaves G L t+ Access.apron G L t * wick G L d t < 1
  rad : 0< furl G L t
lemma afforded {G : Gauge}(p q:ℝ→ℝ)(hp:Reserve G L p)(hq:Reserve G L q)(d : ℝ) : ∀ᶠ t in atTop,∀ β,inBand (betaF G t L) β→Climate G L t d (p t) (q t) β:=by
   have hA:=Access.wide hp.rate; let g t:= q t*eaves G L t; let u t:=Access.apron G L t* wick G L d t
   have he:= (hq.rate.mul (Sienna.edge G L)).below (by simp only [zero_add]; exact Sienna.vow_ok) (1/4:ℝ) (by norm_num)
   have hh:= (Access.rates_apron (G:=G) (L:=L)|>.mul (Reserve.wig d|>.rate)|>.below (by norm_num) (1/4:ℝ) (by norm_num))
   filter_upwards [hA,he,hh,Delay.shift_pos G L] with t hx hy hz hs β hb
   obtain ⟨hg,ht⟩:=hx.2 β hb
   refine ⟨hg,ht,hx.1.2.1,(mul_le_mul_of_nonneg_left (le_abs_self _) hx.1.1.le).trans hx.1.2.2.2.le,?_,Real.rpow_pos_of_pos hs _⟩
   exact (add_le_add ((le_abs_self _).trans hy) ((le_abs_self _).trans hz)).trans_lt (by norm_num)

section golfer
variable (hp: Weather T F Θ k' ρ B β d t a W u C K O k x L)
    (hc:Climate G L t d u C β)
    (hZ: PaintSupply G k Z)
include hp
lemma sunRoof {y:Xs} (hy:‖y‖<eaves G L t) : ‖θ y‖≤ C * ‖y‖:=by
   let ρ₀:=θ; let D'':=ball (0:Xs) (eaves G L t); have H z (hz:z∈D'') : Brush 1 C 1 ρ₀ z:=
     (hp.paint.core.curve _ (mem_ball_zero_iff.mp hz)).smaller (show 1 ≤ k+2 by omega)
   have he:= (convex_ball ..).norm_image_sub_le_of_norm_fderiv_le (f:=ρ₀) (fun z hz=> (H z hz).smooth.differentiableAt (by simp)) (fun z hz=>show ‖fderiv ℝ ρ₀ z‖ ≤ C from by rw [← norm_iteratedFDeriv_one]; exact (offer.mp (H z hz)).inside _ le_rfl) (x:=0) (mem_ball_self hp.paint.core.pos) (y:=y) (mem_ball_zero_iff.mpr hy)
   simpa only [ρ₀,hp.paint.origin,sub_zero] using he
include hc
lemma ethereal {x':ℝ×Xs} {z:Y}(hx:x'∈Germ.patch Xs (Access.apron G L t) u)(hz:‖z‖≤wick G L d t) : ‖usage θ z x'‖<1:=by
   have hh:=patch_test ..|>.1 (kite_moves hc.next.le hc.width hx)
   have hP:= hp.paint.core; have hy:= sunRoof T F Θ k' ρ B hp hh.2
   refine max_lt (hh.2.trans_le hP.small) ?_
   unfold usage Lantern.visit; rw [one_smul]; let p:=kite x'; let k'':=θ
   change ‖k'' p.2+p.1 • z‖ < _
   apply (norm_add_le ..).trans_lt
   refine lt_of_le_of_lt (add_le_add ?_ ?_) hc.budget
   · exact hy.trans (mul_le_mul_of_nonneg_left hh.2.le (hP.curve _ hh.2).nonneg)
   rw [norm_smul]; exact mul_le_mul (patch_test ..|>.1 hx|>.1.le) hz (norm_nonneg _) (hc.g_pos.le.trans hc.below.le)

omit hp hc

def skyFees (j n m:ℕ)(D u A C:ℝ) := let Z:=vest n D u A C + vest n 1 u (A+1) (C+1); (3^j)^m*(Z+1)*3^j
lemma reserve_sky {p q f h:ℝ→ℝ} (hp:Reserve G L p)(hq:Reserve G L q)(hf:Reserve G L f)(hh:Reserve G L h) (j n m:ℕ) : Reserve G L fun t=>skyFees j n m (p t) (q t) (f t) (h t):=by
   have hQ (p f h : ℝ→ℝ) (hp:Reserve G L p) (hf:Reserve G L f) (hh:Reserve G L h) : Reserve G L fun t=>vest n (p t) (q t) (f t) (h t):=by
     have h1:Reserve G L fun t=> Germ.wind n (q t):= ((Reserve.const _).mul ((Reserve.const _).add hq)).mul (Reserve.const _)
     have h2:=((Reserve.const 1).add hh).add hp
     exact Reserve.comp n (Reserve.comp n (h1.add h1) (h2.add h2)) hf
   exact ((Reserve.const _).mul (((hQ p f h hp hf hh).add (hQ (fun _=>1) (fun x=>f x+1) (fun x=>h x+1) (Reserve.const _) (hf.add (Reserve.const _)) (hh.add (Reserve.const _)))).add (Reserve.const _))).mul (Reserve.const _)
include hp hc hZ
variable (he:Sect E B.threshold n k (fineCost G k Z) A) (hy:j+n≤k)
include he hy
lemma coverage (m:ℕ) :
    let U:= matte F ρ E m n; let H':= fun x:Config G f => masked B.threshold Finset.univ (worn E (gStep β) n m) x
    let C':= skyFees j (j+n) m (wick G L d t) u A C; let K':= gStep β^m*A*(((gStep β)⁻¹*B.threshold)^n)
    Playing F ρ β U H' x (wick G L d t) (furl G L t) u (Access.apron G L t) C' K' j (j+n):=by
   intro U' H' C' K'
   have hu:= hc.g_pos; let g:=gStep β
   have hp' : 0<u:= lt_trans (add_pos_of_nonneg_of_pos (norm_nonneg _) hc.rad) hp.cabin
   let W' := E ∘ entice F; have h':= undercover F hZ
   have hA:=he.tall _ _ h'; have he₀:0 ≤ A:= (hA 0 (by simp)).nonneg
   have hK':0≤K':=mul_nonneg (mul_nonneg (pow_nonneg hu.le _) he₀) (pow_nonneg (mul_nonneg (inv_pos.mpr hu).le B.threshold_pos.le) _)
   have hP : braces W' θ (j+n) (wick G L d t) (Access.apron G L t) u A:= fun y hx z hZ=> (hA _ (ethereal T F Θ k' ρ B hp hc hx hZ)).smaller hy
   obtain ⟨hf,hF⟩:= scored (r:=m) hp.paint.core hy (hu.trans hc.below) hc.next.le hc.width hp' hP hp.paint.origin (fun i hi=> norm_eq_zero.mp ((he.mode _ _ h').2 i (by omega) hi))
   refine ⟨hf,⟨?_,?_,fun U=>?_⟩,fun y hy z hz=>?_⟩
   · apply Measurable.stronglyMeasurable; exact masked_measurable _ _ _ ((measurable_const).mul he.localM) -- edit
   · intro l U; by_cases ht: Healthy B.threshold Finset.univ U
     · rw [show H' (gauge l U)=_ from masked_eq _ _ _ _ (by simpa [Healthy] using ht),show H' U=_ from masked_eq _ _ _ _ ht]; unfold worn; rw [he.vigor]
     rw [show H' (gauge l U)=0 from masked_ne _ _ _ _ (by simpa [Healthy] using ht),show H' U=0 from masked_ne _ _ _ _ ht]
   · by_cases ht:Healthy B.threshold Finset.univ U
     · rw [show H' U= _ from masked_eq _ _ _ U ht]; unfold worn; rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤g^m * (g^n)⁻¹)]
       have ht':flags B.threshold U=∅:= by simpa only [Healthy,Finset.disjoint_iff_inter_eq_empty,Finset.univ_inter] using ht
       apply (mul_le_mul_of_nonneg_left (he.value _ ht') (by change 0≤g^m*(g^n)⁻¹; positivity)).trans_eq; unfold K'; rw [mul_pow, inv_pow]; ring
     rw [show H' U=0 from masked_ne _ _ _ _ ht,norm_zero]; exact hK'
   obtain ⟨hi,hq,hK⟩:= stamp_range (G:=G) β hp.cabin hc.rad hu (hp.paint.distance.le.trans hp.paint.core.small) ((mul_le_mul_of_nonneg_right hc.below.le hp'.le).trans hc.width) y hy
   have hs : (g,y)∈Germ.patch Xs (Access.apron G L t) u:= (patch_test ..).2 ⟨by unfold g; rw [Real.norm_of_nonneg hu.le]; exact hc.below,hi⟩
   let V:= F.drape (Aux.piece F ρ β (g • y) z); have hv : Healthy B.threshold Finset.univ V:=by unfold Healthy; rw [hp.paint.signed _ hq hK |>.healthy z hz]; exact Finset.disjoint_empty_right _
   change Germ.promote (baggage W' θ) n m (g,y) z= H' V
   rw [hF _ hs z hu.ne' hz,show H' V=_ from masked_eq _ _ _ _ hv]; unfold W' worn V g; simp only [smul_eq_mul,Function.comp_apply, urging,mul_assoc]; try rfl
end golfer
end YM.RemainderComparison.Herbal
