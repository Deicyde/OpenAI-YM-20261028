import YM.UVExtension.Hearth.Dine
import YM.UVExtension.Pier.Syrup
import YM.UVExtension.Pier.Lance
import YM.UVExtension.Pier.Vast
/-! # Bind denominator only at one volume-controlled finite resolution. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m k:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m≤N)
-- formula stripped.
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "V0"=> fun (N:ℕ)(b:Row a) => S.realBeat b.val N n m
local notation "P"=> A.B.a.budget m
local notation "T₀"=> A.B.a.S
local notation "θ"=> A.B.a.clock
local notation "Z"=> ball (0:ℂ) a
local notation "n₀"=> A.B.a.S.side m n
local notation "W"=> A.B.a.clock.forcedAllowance m
local notation "ρ"=> A.B.a.clock.allowance m
local notation "H"=> S.fits N n
private lemma castle {n:Side}(X:Rep G n)(U:Config G n): (((X.exponent U-X.scalar:ℝ):ℂ))= -(X.path.inChannels X.clip X.p X.beta U:ℂ) - (X.activities.additive X.p U:ℂ):=by
    unfold Rep.exponent Rep.scalar; push_cast; abel
include hp ha
lemma pureGrowth : ∃ p:ℝ,0<p ∧ ∀ N,m ≤ N → ∀ U:Config G (A.B.a.S.side m n), Sail T (fun d:Y=> ↑((V0 N d).exponent U - (V0 N d).scalar)) p:=by
    let x:=3*(θ).hatBeta m; let s:=a; let δ:= ((θ).params m); let Λ:=(θ).loopCap m; let u:=Fintype.card (Site n₀); let v:= ∑ j:Face (Per n₀),crust (A.B.a.S.side m n) G δ.clip P δ.paths j; let r:=δ.paths*(2:ℝ)^3+δ.paths*2^4; let t:=x*(v+∑_j:Site n₀,r)+∑ _j:Site n₀,Λ*2^2
    let q:= t*(Fintype.card Signed:ℝ)*(Fintype.card Signed:ℝ)⁻¹
    refine ⟨max 1 (q+u*ρ),by positivity,fun N' hm U=>?_⟩
    let R (d:Y):= V0 N' d; let d:Y:=⟨0,(show |(0:ℝ)|<a from (abs_zero.trans_lt ha))⟩; let B:= A.B.kin.path N' m; have hx:0≤x:= mul_nonneg (by norm_num) (zero_le_one.trans (A.B.a.fits.delayed m).le)
    have hp' : Sail T (fun d:Y=>(R d|>.beta :ℂ)) x:=by
       let H':= S.fits N' n; let V':= S.cart N' n; let L:= S.grove.coins; have h:= H'|>.nowBeta V' L m hm; exact ⟨_,bumps _ _ (h.1.mono hp),fun i=> (H'.really V' (S.token N' n) L (hp (T|>.within i)) m hm).1,fun i hi=> h.2 _ (hp hi)⟩
    have hb: B.Bounds δ.clip δ.width δ.paths Λ:= (liveR S N' n m (roseK S ha hp d) hm).paths
    have hf:=potion n₀ (P) δ.clip δ.width δ.paths Λ B hb T (fun i=> (R i).beta) hp' hx U
    have he:= fundsG S N' n m ha hp hm U
    have hh:(fun d:Y=> (((V0 N' d).exponent U - (V0 N' d).scalar:ℝ):ℂ))=(fun j=> - (B.inChannels δ.clip P ((R j).beta) U:ℂ) - ((R j).activities.additive P U:ℂ)):=by
       funext j; exact castle (R j) U
    rw [hh]; exact (hf.negative.sub he).mono (le_max_right ..)

omit ha hp
variable {o:Side}
def faded (R: Rep G o)(i: Wing)(U:Config G o):= (Real.exp (-R.scalar):ℂ)*port R i U
lemma hitStrip (R: Rep G o)(i: Wing)(F: Config G o→ℂ): hit R i F= (((∫ U,stripped R U ∂prior G o):ℝ):ℂ)⁻¹ * ∫ U,faded R i U* F U ∂prior G o:=by
   have he: (Real.exp (-R.scalar):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'; unfold hit total stripped faded; rw [integral_complex_ofReal, integral_const_mul,Complex.ofReal_mul]; simp_rw [mul_assoc (Real.exp (-R.scalar):ℂ), integral_const_mul]; rw [mul_inv_rev,mul_assoc,inv_mul_cancel_left₀ he]; rfl
lemma strips {α C Λ v b:ℝ}(R:Rep G o) (h:R.Lawful α C Λ v b) (i:Wing) : Envelope (faded R i):=by
   obtain ⟨p,hp⟩:= (portEnv i R h).cost; exact ⟨(portEnv i R h).meas.const_mul _,_, fun U=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (hp U) (norm_nonneg _))⟩

private lemma floorR (z:ℝ) (Q: BudgetPoint):∃ p:ℝ,0< p∧ ∀ R:Rep G o, (R.p=Q) → (∀ U, 0≤ R.eval U) → Integrable (stripped R) (prior G o) → (∀ U, - z ≤ R.exponent U - R.scalar) → p≤ ∫ U, stripped R U ∂prior G o:=by
    let μ:=prior G o; let P':= calm G o Q.threshold
    refine ⟨μ.real P' * Real.exp (-z),mul_pos ?_ (Real.exp_pos _),fun R h hQ hl hs=>?_⟩
    · exact lt_of_lt_of_le (pow_pos (pow_pos (div_pos Q.threshold_pos (by positivity)) _) _) (RG.space G o Q.threshold Q.threshold_pos Q.threshold_le)
    rw [show μ.real P' * Real.exp (-z) = ∫ U,P'.indicator (fun _=> Real.exp (-z)) U ∂μ by rw [integral_indicator (calm_meas _),setIntegral_const]; rfl]; refine integral_mono ((integrable_const _).indicator (calm_meas _)) hl ?_; intro x
    by_cases h':x∈P'
    · rw [Set.indicator_of_mem h',stripped,Rep.eval, Activities.gas_one _ _ (voids h' (le_of_eq ?_)),mul_one,←Real.exp_add,Real.exp_le_exp]; linarith only [hs x]; exact congr_arg BudgetPoint.threshold h.symm
    rw [Set.indicator_of_notMem h', stripped]; exact mul_nonneg (Real.exp_pos _).le (hQ x)
include ha hp
set_option quotPrecheck false
lemma roomR :∃ v z:ℝ,0 < v ∧ 0 < z ∧ ∀ N,m ≤N →
     (∀ U:Config G (n₀), Sail T (fun d:Y=> (stripped (V0 N d) U:ℂ)) v ∧ ∀ i:Wing, Sail T (fun d:Y=>faded (V0 N d) i U) v) ∧ ∀ d:Y,z ≤ (∫ U,stripped (V0 N d) U∂prior G n₀):=by
    obtain ⟨u,hu,h⟩:= pureGrowth S n m ha hp; obtain ⟨z,hz,hQ⟩:= floorR (G:=G) (o:=n₀) u P
    let p:= Real.exp ((Fintype.card (Site (A.B.a.S.side m n)):ℝ)*W); let v:=Real.exp u * p; refine ⟨v,z,mul_pos (Real.exp_pos _) (Real.exp_pos _),hz,fun N' hm=>?_⟩; let V (d:Y):= V0 N' d -- notation V conflict
    constructor
    · intro U; have hE: Sail T (fun d:Y=> (Real.exp ((V d).exponent U - (V d).scalar):ℂ)) (Real.exp u):= by simpa only [Complex.ofReal_exp] using (h N' hm U).exp
      obtain ⟨hp₁,hg⟩:= flashes S N' n m ha hp hm U; have he : Sail T (fun d:Y=> (stripped (V d) U:ℂ)) v:=by
         have hC:(fun d:Y=>(stripped (V d) U:ℂ))=(fun d=>(Real.exp ((V d).exponent U-(V d).scalar):ℂ)*((V d).activities.gas P U:ℂ)):=by
            funext d; unfold stripped Rep.eval; rw [←mul_assoc,←Real.exp_add,Complex.ofReal_mul,add_comm,← sub_eq_add_neg]; rfl
         rw [hC]; exact hE.mult hp₁ (Real.exp_pos _).le
      refine ⟨he,fun i=>?_⟩
      cases i with
      | logKey i=> simpa only [stripped,Complex.ofReal_mul] using! he
      | gasKey i=>
        have hG:= hE.mult (hg i) (Real.exp_pos _).le; have he:(fun d=>faded (V d) (.gasKey i) U)= (fun d=> (Real.exp ((V d).exponent U-(V d).scalar):ℂ)* dressed (V d) i U):=by
            funext d; unfold faded; change _*( (Real.exp _:ℂ)*_)=_; rw [←mul_assoc,←Complex.ofReal_mul,← Real.exp_add, add_comm, ← sub_eq_add_neg]
        change Sail _ _ _; exact he.symm ▸ hG
    intro d; let Q':= V d; let D':=prior G (n₀); have hs := liveR S N' n m (roseK S ha hp d) hm
    have hv : ∀ U,0≤Q'.eval U:= Vintage.YM.RG.History.nonnegative (Orchard.Path S (fun _ _=> roseK S ha hp d)) (selected S _) _ _ _ hm
    refine hQ Q' rfl hv (stripped_int _ hs) (fun U=>?_); have ht : ‖((Q'.exponent U - Q'.scalar:ℝ):ℂ)‖≤u:= (h N' hm U).within d; rw [Complex.norm_real] at ht; exact (abs_le.mp ht).1
end YM.UVExtension.Pier
