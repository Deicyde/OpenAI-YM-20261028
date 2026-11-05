import YM.UVExtension.Hearth.Trail
import YM.UVExtension.Forest.Coda
import YM.UVExtension.Orchard.Tarts

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
local notation "K'"=> A.B.a.budget m
open Steady Planned.GuardedAtom Guard Roads.Unum SectorNext.Vacuum
variable {ι:Type}{w:Filter ι} [w.NeBot](t:ι→ ℕ)(ht:Tendsto t w atTop)
open GridApprox.Joint
open Rep
lemma travelling (H':History G)(h:Vintage.YM.RG.History.Selected H') (m k N n:ℕ) (hm:m≤k) (hN:k≤N): pushTo H' N n hm (fun U=> ((H'.rep N n k).eval U:ℂ)) = fun U=> ((H'.rep N n m).eval U:ℂ) :=by
   induction k,hm using Nat.le_induction with
   | base=> simp only [pushTo_self]
   | succ k hk ih=>
     let t:= (H'.levels.clock.op k n); let b:= (H'|>.β N n (k+1)); let R0:=H'.rep N n k; let R1:= H'.rep N n (k+1); have ht: t.push b (fun U=>(R1.eval U:ℂ)) = fun U=>(R0.eval U:ℂ):=by
        rw [show R0.eval=t.push b R1.eval from ((Vintage.YM.RG.History.Selected.steps h) N n k hN).1]; funext U; unfold StepData.push; simp_rw [Complex.real_smul,smul_eq_mul,← Complex.ofReal_mul, integral_complex_ofReal]
     rw [pushTo_next H' N n hk,ht]; exact ih (Nat.le_trans (Nat.le_succ _) hN)

def tasting {c:Side}(R: Rep G c)(F: Config G c→ℂ):= ((( (∫ U,stripped R U ∂prior G c):ℝ):ℂ))⁻¹ * ∫ U, (stripped R U:ℂ)*F U ∂prior G c

lemma scaledK (H':History G)(h:Vintage.YM.RG.History.Selected H') (m N n:ℕ) (hm:m ≤ N){F: Config G (H'.S.side m n)→ℂ} (hf:Envelope F): moment (H'.β N n N) (backTo H' N n hm F) = tasting (H'.rep N n m) F:=by
   let b:=H'.β N n N; let c:=H'.S.side m n; let q:=H'.S.side N n; let g(U:Config G q):=(bare b U:ℂ); let R:= H'.rep N n m; let r:ℝ:=∫ U,R.eval U∂prior G c
   have hg: Envelope g:= Envelope.compactC (Complex.continuous_ofReal.comp (bare_cont _)); have ht:= pushTo_dual H' N n hm hf _ (hg.integrableC (prior G q)); have hx:= travelling H' h m N N n hm le_rfl; rw [(Vintage.YM.RG.History.Selected.starts h N n).2] at hx
   rw [show pushTo H' N n hm g = _ from hx] at ht
   have hΓ : ∫ U,stripped R U∂prior G c= Real.exp (-R.scalar)*r:=by unfold stripped r; rw [integral_const_mul]
   have hR : r= partition G q b:= Vintage.YM.RG.History.partition_eq _ h N n m hm
   let k:=(Real.exp (-R.scalar):ℂ); let F':=backTo H' N n hm F
   rw [moment_formula _ _ (by exact (backTo_env H' N n hm hf).integrableC _)] -- β arg
   change ((partition G q b:ℂ))⁻¹ * _ = _
   change ( (partition G q b:ℂ) )⁻¹ * (∫ U,g U * _ ∂prior G q) = tasting R F; rw [tasting]; rw [hΓ,hR]; unfold stripped; rw [← ht]; simp only [Complex.ofReal_mul,mul_inv_rev]; simp_rw [mul_assoc (Real.exp (-R.scalar):ℂ),integral_const_mul]
   have hu:k≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'; change _ = _*k⁻¹*(k*_); rw [mul_assoc _,inv_mul_cancel_left₀ hu]

lemma tunedT {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]{c:Side}{g: ι → Config G c → X}(h:Tune w g)(hp:∀ᶠ n in w, Integrable (g n) (prior G c)): ∃ t,Tendsto (fun i=> ∫ U,g i U ∂prior G c) w (𝓝 t):=by
   apply cauchy_map_iff_exists_tendsto.mp; rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds]; intro ε he; filter_upwards [tendsto_fst.eventually hp,tendsto_snd.eventually hp,h.uv (ε/2) (half_pos he)] with n hn hn' ht
   simp only [dist_zero_right,dist_eq_norm (∫ U,_ ∂_) (∫ U,_ ∂_), ←integral_sub hn hn']; apply lt_of_le_of_lt _ (half_lt_self he); simpa using (norm_integral_le_of_norm_le_const (μ:=prior G c) (Eventually.of_forall ht))

lemma seating {c:Side}{Z:ι→ Rep G c}{F:ι→ Config G c→ℂ}(hp:Tune w F)(h:Tune w (fun n=> stripped (Z n)))(hf:∀ᶠ i in w,Envelope (F i)∧ Integrable (stripped (Z i)) (prior G c))(hc:∃ b:ℝ,0<b∧ ∀ᶠ i in w,b ≤ ∫ U,stripped (Z i) U∂prior G c):∃ x,Tendsto (fun i=> tasting (Z i) (F i)) w (𝓝 x):=by
   obtain ⟨b,hb⟩:= tunedT h (hf.mono fun i hi=> hi.2); obtain ⟨c,hc,hE⟩:= hc
   let V i U:=(stripped (Z i) U:ℂ); have hg: Tune w V:= h.cont Complex.continuous_ofReal
   obtain ⟨y,hy⟩:= tunedT (mulT hg hp) (hf.mono fun n ⟨h,p⟩=> by obtain ⟨r,hr⟩:=h.cost; exact Integrable.mul_bdd (f:=fun U=>(stripped (Z n) U:ℂ)) (Complex.ofRealCLM.integrable_comp p) h.meas.aestronglyMeasurable (Eventually.of_forall hr))
   exact ⟨_, (((Complex.continuous_ofReal.tendsto _).comp hb).inv₀ (Complex.ofReal_ne_zero.mpr (hc.trans_le (ge_of_tendsto hb hE)|>.ne'))).mul hy⟩

include a hv
lemma arrival (F:ℕ→ Config G (A.B.a.S.side m n) → ℂ)(hp:Tune atTop F)(hf:∀ᶠ i in atTop, Envelope (F i)): UVExtension.Arrives (fun i=> tasting (H|>.rep i n m) (F i)):=by
   obtain ⟨k,hk⟩:= tier a.fields m; let l:=m+k; let t j:=j+l; have ht:Tendsto t atTop atTop:= tendsto_add_atTop_nat l; have hM j:m≤t j:=by unfold t l; omega
   have he : Tune atTop (fun j=> F (t j)):=by
      obtain ⟨r,hr⟩:= hp.price; refine ⟨⟨r, ht.eventually hr⟩,fun ε h=>?_⟩; exact ((ht.comp tendsto_fst).prodMk (ht.comp tendsto_snd)).eventually (hp.uv _ h)
   let Y i:=H|>.rep (t i) n m; obtain ⟨Z,hZ⟩:= hk ℕ _ t ht hM (fun i=>by unfold t l; omega); change Revenues atTop _ (fun i=> (Y i).path) Z at hZ
   have hr(i:ℕ): (Y i).clip=(A.B.a.params m).clip:=rfl; have hz: Span.StableR atTop Y:= Mast.signs S v m n a x hv t ht hM; have hδ i:= (Vintage.YM.RG.History.Selected.represents (Orchard.selected S v) (t i) n m (hM i)).good
   obtain ⟨r,hR⟩:=seating (Z:=Y) he (strippedOn hZ hz hr) ((ht.eventually hf).mono fun n hn=>⟨hn,stripped_int _ (hδ n)⟩) (zPositive hZ hz hr (Eventually.of_forall fun i=>⟨⟨_,_,_,_,_,hδ i⟩, Vintage.YM.RG.History.nonnegative H (Orchard.selected S v) (t i) n m (hM i)⟩))
   exact ⟨r,by rw [← tendsto_add_atTop_iff_nat l]; exact hR⟩
end YM.UVExtension.Hearth
