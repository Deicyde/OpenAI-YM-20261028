import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Coat
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Impasto
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites

/-!
# Phasing movements on arbitrary rotated screens

Around flat or scaled increments. Use with Sweep as visible row envelope.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows 
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : E→ Config G c} {x : E} {d u v : ℝ} {k : ℕ}
open Brush

structure Mode (U : E → Config G c) (x : E) (k : ℕ) (d : ℝ) : Prop where
  pos : 0≤d
  atLink : ∀ i, Brush k (royalty G) d (fun j=> G.mat (U j i)) x

lemma a_oneB (P : Gauge) (B : P.El) (hd : 0≤d) : Brush k (royalty P) d (fun _ : E => P.mat B) x :=
    (certified hd _).climb (Gauge.unitary_frob (P.mat_mul_star B)).le le_rfl

lemma offsetB {u : E → G.El} (p : Brush k v d (fun i=>G.mat (u i)) x) (a b : G.El) :
    Brush k v d (fun i=>G.mat (a*u i*b)) x := by
  let L : G.Mat →ₗ[ℝ] G.Mat := { toFun v:= G.mat a*v*G.mat b, map_add' i j:=by simp [mul_add,add_mul], map_smul' i j := by dsimp; simp }
  have he : Brush k (1*v) d _ x := p.report L.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound _
    zero_le_one (fun i=> by change ‖G.mat a*i * G.mat b‖ ≤ _; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star b), Gauge.mul_frob_eq _ _ (G.mat_star_mul _),one_mul]))
  rw [one_mul] at he; exact he
lemma turn (h : Mode U x k d) (s : Signed) : Mode (fun i=> pull s 0 (U i)) x k d := by
  constructor
  · exact h.pos
  intro i
  simp_rw [Channel.charge]; split_ifs
  · exact reverse (f:=fun k=> U k (Channel.edge s i)) (h.atLink _)
  exact h.atLink _
lemma soak (h : Mode U x k d) (s : Site c → G.El) : Mode (fun i=> gauge s (U i)) x k d :=
  ⟨h.pos,fun _=> offsetB (h.atLink _) _ _⟩
lemma thicken {f : E → G.El} (h : Brush k v d (G.mat ∘ f) x) : Brush k (royalty G) ((1+v)*d) (G.mat ∘ f) x := by
  have hu : 1 ≤ 1+v := le_add_of_nonneg_right h.nonneg
  refine ⟨h.smooth,mul_nonneg (zero_le_one.trans hu) h.pos,?_⟩; rintro (_|i) hi
  · unfold normJ; rw [pow_zero,mul_one,norm_iteratedFDeriv_zero]; exact (Gauge.unitary_frob (G.mat_mul_star (f x))).le
  apply (h.order _ hi).trans
  rw [mul_pow,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg h.pos _)
  refine (le_trans (show v ≤ 1+v from le_add_of_nonneg_left zero_le_one) (le_self_pow₀ (n:=i+1) hu (by omega))).trans ?_
  apply le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hu) _) (royalty_ge G)

lemma colorEvaluated {o : ℕ} (n : Fin o) {f : E→ EuclideanSpace ℝ (Fin o)} (p : Brush k u d f x) :
    Brush k u d (fun i=> f i n) x := by
  let L := innerSL ℝ ((EuclideanSpace.basisFun (Fin o) ℝ) n)
  have hh := p.report L (v:=1) (by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=>?_); rw [one_mul];
    exact (abs_real_inner_le_norm _ i).trans_eq (by rw [OrthonormalBasis.norm_eq_one, one_mul]))
  have hx : L ∘ f=(fun i=> f i n) := funext (fun i=>EuclideanSpace.basisFun_inner (Fin o) ℝ (f i) n)
  rwa [hx,one_mul] at hh

lemma fromLogL (B : E → Directions G c) (h : Brush k u d B x) (r : ℝ) (hr : 0<r) {w} (hh : ∀ z:G.Color, ‖z‖≤r →
    Brush k w 1 (fun i=> G.mat (G.lieExp i)) z) (hp : ∀ j, ‖B x j‖≤r) (U : Config G c) :
    Mode (fun i=> increment U (B i)) x k ((1+(k.factorial:ℝ)*w)*((1+u)*d)) := by
  have hs j : Brush k u d (fun i => B i j) x := by
    let L : (Directions G c) →L[ℝ] G.Color := ContinuousLinearMap.proj j
    have he := h.report L (show ‖L‖≤1 from ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro i; rw [one_mul]; exact norm_le_pi_norm i j)); rw [one_mul] at he; exact he
  constructor
  · have he := (hh 0 (by simpa using hr.le)).nonneg
    have hp := h.nonneg; have hd:=h.pos; positivity
  intro i;
  have hf := thicken (f:=fun z=> G.lieExp (B z i)) ((hs i).pine (hh _ (hp i)))
  simpa only [one_mul] using! offsetB hf 1 (U i)

lemma expCost (G : Gauge) (k : ℕ) (r : ℝ) : ∃ v : ℝ,0 < v ∧ ∀ z:G.Color, ‖z‖ ≤ r →
    Brush k v 1 (fun i=> G.mat (G.lieExp i)) z := by
  obtain ⟨v,h,hv⟩ := Brush.compact (s:=Metric.closedBall (0:G.Color) r) (isCompact_closedBall _ _)
    (fun i _=> ((G.exp_jet).contDiffAt).of_le (show (↑k:WithTop ℕ∞) ≤ ⊤ from le_top))
  exact ⟨v,h,fun i hi=> hv i (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hi))⟩
end YM.ConnectedActivityE6.Blaze
