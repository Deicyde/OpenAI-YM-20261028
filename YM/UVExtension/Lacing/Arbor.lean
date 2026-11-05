import YM.UVExtension.Lacing.Ram
/-!
 # Graph-step architecture. at every complex coordinate its inputs under Motion may be OTHER values of the parameter.
 Hence require *family* per motion. cone delivered, eq genuine. Strong stability even without complex orientation equations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}
local notation "R"=> RoutesF F n n' p P H
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
set_option quotPrecheck false
variable (L:Motion→RoutesF F n n' p P H)(Y Y':Motion→(F.Coeff→ₗ[ℂ] Cow G n' p d H))(hn:2≤ n.val)
local notation "a'"=> major L Y hn
local notation "b'"=> minor L Y hn
local notation "F1"=> F.Coeff
section
variable {u v c w :ℝ} {r:Side}{T:Heading F}(h:∀ i, Tips (L i) r T u v)
lemma beaded {ι μ Ω:Type} [Fintype ι][NormedAddCommGroup μ] [NormedSpace ℂ μ][NormedAddCommGroup Ω][NormedSpace ℂ Ω][FiniteDimensional ℂ Ω]
   (g:Ω→ₗ[ℂ] (ι→ℂ))(f p:ι→μ)(C:ι→ℝ)(he:∀ i,‖f i-p i‖≤C i)(x:Ω): ‖beadZ g f x-beadZ g p x‖≤∑ i,‖g x i‖*C i:=by
    rw [beadV,beadV,← Finset.sum_sub_distrib]
    apply (norm_sum_le ..).trans; simp_rw [← smul_sub,norm_smul]; exact Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)
include h
set_option synthInstance.maxHeartbeats 140000
set_option maxRecDepth 4500 in
set_option maxHeartbeats 700000 in
lemma beams (hc:0 ≤ c)(hp:∀ i x,‖Y i x-Y' i x‖ ≤ c * F.coeffSize (F.core x))(x:F1) : F.coeffSize (major L Y hn x - major L Y' hn x) ≤ 2*u*c*orbitCost F *F.coeffSize (F.core x) ∧ ‖minor L Y hn x-minor L Y' hn x‖≤2*u*c*orbitCost F*F.coeffSize (F.core x):=by
    let J:= Size.axis F; let s (v:F.Coeff):=F.coeffSize (F.core v); let t:=2*u*c; have huv:= (h (1,false)).counts.calm; have ht :0≤t:=by unfold t; positivity
    let A i:= sell L Y hn i; let D i:= sell L Y' hn i
    have hx(i): F.coeffSize ((A i).1-(D i).1) ≤ t*s (J i.2) ∧ ‖(A i).2-(D i).2‖ ≤ t*s (J i.2):=by
       let x:= J i.2; let M:= L i.1; let z:= Y i.1 x; let z':= Y' i.1 x; have hC := (h i.1).shifts i.1 hn (some i.2) z z'
       have hs :2*u*‖z-z'‖ ≤ t*s x:= (mul_le_mul_of_nonneg_left (hp i.1 x) (by positivity)).trans_eq (mul_assoc ..).symm
       let j:= Eyelet.cap n F H P i.1 hn (M.rain z (some i.2))- Eyelet.cap n F H P i.1 hn (M.rain z' (some i.2)); have hh : A i-D i= rooms n F H P (aisleN (code _) i) j :=Eq.symm (map_sub ..)
       refine ⟨hC.1.trans hs,?_⟩; rw [← Prod.snd_sub,hh]; exact (Tips.deal ..).trans (hC.2.trans hs)
    have hv:(∑ i:Tally F,‖chips F x i‖*(t*s (J i.2))) ≤ (t*orbitCost F)*s x:=by
       simp_rw [mul_left_comm _ t,← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (core_tab F x) ht).trans_eq (mul_assoc ..).symm
    constructor
    · rw [(pieces L Y hn x).1,(pieces L Y' hn x).1]; simp_rw [← Finset.sum_sub_distrib,← smul_sub]
      refine (Size.finite ..).trans ((Finset.sum_le_sum (g:=fun i=> ‖chips F x i‖*(t*s (J i.2))) fun i _=> ?_).trans hv); rw [Size.smul]; exact mul_le_mul_of_nonneg_left (hx i).1 (norm_nonneg _)
    have hU:=beaded (μ:=Cow G n P d H) (chips F) (fun i=> (A i).2) (fun i=>(D i).2) (fun i=>t*s (J i.2)) (fun i=>(hx i).2) x
    have hv := hU.trans hv; rw [beadV,beadV] at hv; rw [(pieces L Y hn x).2,(pieces L Y' hn x).2]; unfold A D t s at hv; convert! hv
end
end YM.UVExtension.Lacing
