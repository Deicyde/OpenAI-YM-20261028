import YM.UVExtension.Gale.Scud
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{n m:Side}{P Q:BudgetPoint}
local notation "L'"=> RoutesF F n m P Q A
local notation "E₁"=> Cow G m P d A
local notation "E₀"=> Cow G n Q d A
local notation "N!"=> Bucket F Q A n
variable {S:Set ℂ}{L:ℂ→RoutesF F n m P Q A}
set_option synthInstance.maxHeartbeats 90000
variable {v s w c u r:ℝ} {T:Heading F}{l:Side}
local notation "Z"=>ball (0:ℂ) r
variable (hr:0<r)(h:Rains (ball 0 r) L)(hc:∀ z∈Metric.ball 0 r, Tips (L z) l T u v) (P':ℂ→ F.Coeff→ₗ[ℂ] Cow G m P d A)(hn:2≤ n.val)
variable (hp: Tollgate F u v c w s)(hz:∀ x,F.coeffSize (T.map x) ≤ c*F.coeffSize x∧ F.coeffSize (T.map.symm x)≤ c*F.coeffSize x)(hm:∀ i∈Metric.ball 0 r, Length F (P' i) s)(hh:∀ x,DifferentiableOn ℂ (fun z=>P' z x) (Metric.ball 0 r))
open Complex
lemma glows (i:Motion) (z:ℂ):‖gazeH i z‖=‖z‖:=by unfold gazeH; split<;> simp
lemma genes (i:Motion)(z:ℝ) : gazeH i (z:ℂ)=z:=by unfold gazeH; split<;> simp
lemma rises (i:Motion)(z:ℂ)(hz:z∈Z): gazeH i z∈Z:= mem_ball_zero_iff.mpr ((glows ..).trans_lt (mem_ball_zero_iff.mp hz))
local notation "U"=> fun (z:ℂ)(i:Motion)=> L (gazeH i z)
local notation "P₁"=> fun (z:ℂ)(i:Motion)=> P' (gazeH i z)
variable {P'}
-- analytic basis evaluated continuously (finite width index P₁.Xp no hidden Real)
include hr h hc hh hn
private lemma tents (i:Tally F) : DifferentiableOn ℂ (fun z=> sell (U z) (P₁ z) hn i) (Metric.ball 0 r):=by
   let f(z:ℂ):=(L z).rain (P' z (Size.axis F i.2)) (some i.2); have hf:DifferentiableOn ℂ f Z:= raft hr h (fun z hz=> (hc z hz).counts) _ (hh (Size.axis F i.2)) _
   have hg:DifferentiableOn ℂ (fun z=> Eyelet.cap n F A Q i.1 hn (f (gazeH i.1 z))) Z:=fun z hz=> (sway _ (hf.differentiableAt (Metric.isOpen_ball.mem_nhds (rises i.1 z hz)))).differentiableWithinAt
   exact (rooms n F A Q (aisleN (code _) i)).differentiable.comp_differentiableOn hg
omit hr h hc hh hn
-- pointwise on chart basis. P vector finite dim. hol CLM via axes.
variable {U':Type}[NormedAddCommGroup U'][NormedSpace ℂ U']
lemma curtains (V:ℂ→ F.Coeff→L[ℂ] U')(hv:∀ x,DifferentiableOn ℂ (fun z=> V z x) S): DifferentiableOn ℂ V S:=by
   let b(i:F.Index): F.Coeff→L[ℂ]ℂ:= ContinuousLinearMap.proj i; let f(i:F.Index)(v:U'):= (b i).smulRight v
   have hx(i:F.Index)(v w:U'): f i (v+w)= f i v+f i w:= ContinuousLinearMap.ext fun y=> smul_add ..
   have hX(i:F.Index) (c:ℂ)(v:U'): f i (c • v)= c • f i v:= ContinuousLinearMap.ext fun y=> smul_comm ..
   let L (i:F.Index): U'→L[ℂ] F.Coeff→L[ℂ] U':= ({toFun:=f i,map_add':=hx i,map_smul':=hX i} : U'→ₗ[ℂ] F.Coeff→L[ℂ] U').mkContinuous ‖b i‖ (fun v=>by
       apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)); intro x; change ‖(b i x) • v‖≤ ‖b i‖* ‖v‖*‖x‖; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right ((b i).le_opNorm _) (norm_nonneg _)).trans_eq (mul_right_comm ..))
   let Y i:= Size.axis F i
   have hF(z) : V z=∑ i:F.Index,L i (V z (Y i)):=by
       ext1 x; rw [ContinuousLinearMap.sum_apply]; change V z x=∑ i:F.Index,x i • V z (Y i); conv_lhs => rw [← Size.sum_axes F x]; rw [map_sum]; simp
   have hp : V= fun z=>∑ i:F.Index,L i (V z (Y i)):=funext hF
   exact (show DifferentiableOn ℂ (fun z=> ∑ i:F.Index,L i (V z (Y i))) S from DifferentiableOn.fun_sum fun i _=> (L i).differentiable.comp_differentiableOn (hv (Y i))).congr (fun z _=> hF z)
include hr h hc hh hn
lemma primp :
   DifferentiableOn ℂ (fun z=> major (U z) (P₁ z) hn) (ball 0 r) ∧ ∀ x:ℂ→F.Coeff,DifferentiableOn ℂ x (ball 0 r) → DifferentiableOn ℂ (fun z=> minor (U z) (P₁ z) hn (x z)) (ball 0 r):=by
   let M z:= major (U z) (P₁ z) hn; let N z:= minor (U z) (P₁ z) hn; have hp(i):=tents hr h hc (P':=P') hn hh i; constructor
   · change DifferentiableOn ℂ M Z; apply curtains; intro x; have hz z:M z x=_:=(Lacing.pieces ..).1; apply DifferentiableOn.congr (f:=fun z=>∑ i:Tally F,chips F x i • (sell (U z) (P₁ z) hn i).1) (DifferentiableOn.fun_sum fun i _=> DifferentiableOn.const_smul ((hp i).fst) (chips F x i)) (fun z h=> hz z)
   have hz:DifferentiableOn ℂ N Z:=by
      apply curtains; intro x; have hz z:N z x=_:=(Lacing.pieces ..).2; apply DifferentiableOn.congr (f:=fun z=>∑ i:Tally F,chips F x i • (sell (U z) (P₁ z) hn i).2) (DifferentiableOn.fun_sum (fun i _=> ((hp i).snd.const_smul (chips F x i)))) (fun z h=> hz z)
   intro x; exact fun h=> hz.clm_apply h
include hp hz hm
set_option maxHeartbeats 600000 in
set_option maxRecDepth 8192 in
lemma clippers (x:ℂ→ F.Coeff)(hf:DifferentiableOn ℂ x (ball 0 r)): let V(z):=steer (U z) (P₁ z) hn
   DifferentiableOn ℂ (fun z=> V z (x z)) (ball 0 r)∧ DifferentiableOn ℂ (fun z=> (V z).symm (x z)) (ball 0 r) ∧ DifferentiableOn ℂ (fun z=> Lacing.crown (U z) (P₁ z) hn (x z)) (ball 0 r):=by
   intro V; obtain ⟨h₁,h₂⟩:= primp hr h hc hn hh; have he(z)(h:z∈Z) (i:Motion) := rises i z h
   have hg (z)(he':z∈Z): Bijective (major (U z) (P₁ z) hn):= carat hp (fun i=>hc _ (he z he' i)) hz (fun i=>hm _ (he z he' i)) hn
   have ht:= keel _ Metric.isOpen_ball h₁ hg x hf
   refine ⟨(h₁.clm_apply hf).congr (fun z h=>steers_eq _ (hg z h) _),ht,h₂ _ ht⟩
end YM.UVExtension.Gale
