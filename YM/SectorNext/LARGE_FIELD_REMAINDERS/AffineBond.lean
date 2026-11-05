import YM.Next.FLUCTUATIONS.Prediction
import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineFaces
import YM.SectorNext.LARGE_FIELD_REMAINDERS.BondPeriod


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Affine comparison on actual rooted predicted data

Even where not using tags actively on neighboring bonds the *same* choice is retained.
This math doesn't differentiate ineligibility or ask selected-row determiners; use in
any given proper branch neighborhoods meeting the displayed real tests. Include
an exact normalization check against multiplying by the matrix group inverse in
the definition of the tangent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

variable {G : Gauge} {n c f : Side} {S : StepData c f}

def actuate (S : StepData c f) (W : Config G f) (i : Bond c) (k : S.Choices) (a : Directions G f) (t : ℝ) :=
  S.prediction (increment W (t • a)) k i

def qVar (S : StepData c f) (W : Config G f) (i : Bond c) (k : S.Choices) (a : Directions G f) :=
  deriv (fun t => G.curvature (actuate S W i k a t * (actuate S W i k a 0)⁻¹)) 0

private lemma neutral (S : StepData c f) (W : Config G f) (i : Bond c) (k : S.Choices) (a : Directions G f) :
    actuate S W i k a 0=S.prediction W k i := by
  unfold actuate; congr!
  funext e; unfold increment; simp

private lemma q_turn (h : S.patch.Branches S.kernel G) (z : Site c → G.El) (U : Config G f) (k : S.Choices) :
    S.prediction (gauge (z ∘ S.ratio.parent) U) k = gauge z (S.prediction U k) := by
  funext e
  rw [StepData.prediction,S.updateGauged h,(S.patch.bond_gauge (h:=h) ..).2]
  simp only [Function.comp_apply,Ratio.embed_parent]; rfl

private lemma swept (S : StepData c f) (h : S.patch.Branches S.kernel G) (W : Config G f) (a : Directions G f)
    (i : Bond c) (k : S.Choices) (z : Site c → G.El) (t : ℝ) :
    let Z := z∘S.ratio.parent
    actuate S (gauge Z W) i k (flow Z a) t = z i.1 * actuate S W i k a t * (z (i.1+step i.2))⁻¹ := by
  dsimp only; unfold actuate; rw [show t • flow (z ∘ S.ratio.parent) a =
    fun j : Bond f => G.adjoint ((z∘S.ratio.parent) j.1) ((t • a) j) by ext j; simp [flow,map_smul]]
  rw [← increment_gauge W (t • a) (z∘S.ratio.parent), q_turn h]; rfl

private lemma norm_check (f : ℝ → G.El) (h : DifferentiableAt ℝ (G.mat ∘ f) 0) :
    G.colorMat (deriv (fun t => G.curvature (f t*(f 0)⁻¹)) 0)=(deriv (G.mat∘f) 0) * G.mat ((f 0)⁻¹) := by
  let F (t : ℝ) := f t*(f 0)⁻¹
  have H : HasDerivAt (G.mat∘F) ((deriv (G.mat∘f) 0) * G.mat ((f 0)⁻¹)) 0 := by
    have he := h.hasDerivAt.mul_const (G.mat ((f 0)⁻¹))
    simpa only [Function.comp_def,F,G.mat_mul] using! he
  let D := (deriv (G.mat∘f) 0) * G.mat ((f 0)⁻¹)
  have h0 : (G.mat∘F) 0=1 := by simp only [Function.comp_apply,F,mul_inv_cancel,G.mat_one]
  have hv : D∈G.lie := G.tangent_generates H h0 (fun i => ⟨_,rfl⟩)
  rw [show (deriv (fun t => G.curvature (f t*(f 0)⁻¹)) 0)=G.projectColor D from (Work.F03.curvature_of_hasDerivAt
    (V:=F) ((G.colorMat_project_self hv).symm ▸ H)).deriv, G.colorMat_project_self hv]

set_option maxHeartbeats 650000 in
/-- Caller only needs determine (and protect) the local reads through the given radius
≥ `predReach S.patch` about the coarse bond anchor, and V at this bond. -/
lemma bond_local (P : Patch) (K : KernelChoices) (G : Gauge) (h : P.Branches K G) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ (c f : Side) (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (U W : Config G f) (V : Config G c) (a b : Directions G f) (B : G.Color)
      (k : S.Choices) (i : Bond c) (z : Site c → G.El) (v : ℝ), 0 ≤ v → v ≤ r →
    let g := S.ratio.parent
    let R := predReach S.patch
    (∀ j : Bond f, separation i.1 (g j.1) ≤ R → ‖a j‖ ≤ v ∧ ‖b j‖ ≤ v) → ‖B‖ ≤ v →
    AgreeNear g i.1 R U (increment W a) →
    AgreeNear g i.1 R (gauge (z ∘ g) W) (absolutize b) → gauge z V i = G.lieExp B →
    let f := actuate S W i k a; let u := qVar S W i k a
    DifferentiableAt ℝ (fun t => G.curvature (f t*(f 0)⁻¹)) 0 ∧ DifferentiableAt ℝ (G.mat∘f) 0 ∧
    G.colorMat u = (deriv (G.mat ∘ f) 0)*G.mat ((S.prediction W k i)⁻¹) ∧
    ‖Z S (S.prediction U k) V i - (Z S (S.prediction W k) V i-Real.sqrt K.penalty • u)‖ ≤ C*v^2 ∧
    ‖Z S (S.prediction W k) V i‖ ≤ C*v ∧ ‖Real.sqrt K.penalty • u‖ ≤ C*v := by
  obtain ⟨C,r,hC,hr,hq⟩ := postage P K G h
  let c0 := Real.sqrt K.penalty
  have h0 : 0<c0 := Real.sqrt_pos.2 K.penalty_pos
  refine ⟨c0*C,r,mul_pos h0 hC,hr,?_⟩
  intro c f S hp hk U W V a b B k i z v hv hy g R ht hB hU hW hV F u
  have hf : S.patch.Branches S.kernel G := by rw [hp,hk]; exact h
  let travel (a : Directions G f) : Directions G f := fun j => if separation i.1 (g j.1) ≤ R then a j else 0
  let a0 := travel a; let b0 := travel b
  let Z0 := z∘g
  let e := flow Z0 a0
  let E : BondTest G f := (e,b0,B)
  have hh (a : Directions G f) (b : Directions G f) (t : ℝ) (ht : AgreeNear g i.1 R (gauge Z0 W) (absolutize b)) :
      AgreeNear g i.1 R (gauge Z0 (increment W (t•a))) (increment (absolutize (travel b)) (t • flow Z0 (travel a))) := by
    rw [increment_gauge]; intro j hj
    unfold increment flow; rw [ht j hj]; simp only [absolutize,Pi.smul_apply,travel,if_pos hj,map_smul]
  have he (t : ℝ) : qForecast S i k (t • e,E.2)=z i.1*F t*(z (i.1+step i.2))⁻¹ := by
    unfold qForecast; rw [← swept S hf W a i k z t]
    have h' := hh a b t hW; rw [increment_gauge] at h'
    have ht' : (fun j : Bond f => G.adjoint (Z0 j.1) ((t • a) j))=t • flow Z0 a := by ext j; simp [flow,map_smul]
    rw [ht'] at h'
    exact (prediction_near_eq hf _ _ k i h').symm
  have hi := prediction_near_eq hf U (increment W a) k i hU
  let M := (G.adjoint (z i.1)).toContinuousLinearMap
  let w t := G.curvature (F t*(F 0)⁻¹)
  let q (t : ℝ) := qTangent S i k (t • E.1,E.2)
  have hz : q=M ∘ w := by
    funext t; unfold q qTangent
    have hh := he 0; rw [zero_smul] at hh
    change G.curvature (qForecast S i k (t • e,E.2)*(qForecast S i k ((0 : Directions G f),E.2))⁻¹)=G.adjoint (z i.1) _
    rw [hh,he, show z i.1 * _ * _ * (z i.1 * _ * _)⁻¹ = z i.1*(F t*(F 0)⁻¹)*(z i.1)⁻¹ by group,G.curvature_conjugate]
  have hh : ‖E‖ ≤ v := by
    refine max_le ?_ (max_le ?_ hB) <;> refine (pi_norm_le_iff_of_nonneg hv).mpr fun j => ?_
    · change ‖flow Z0 a0 j‖ ≤ _; unfold flow; rw [G.norm_adjoint]; unfold a0 travel; split; exact (ht j ‹_›).1; rwa [norm_zero]
    change ‖b0 j‖ ≤ _; unfold b0 travel; split; exact (ht j ‹_›).2; rwa [norm_zero]
  obtain ⟨h1,h2,h3,-,h4,h5⟩ := hq c f S hp hk k i E v hh hy
  have hl := differentiation_back M (G.adjoint (z i.1)⁻¹).toContinuousLinearMap (ad_inv _) w q hz h1
  have Hmat (t : ℝ) : G.mat (F t) = star (G.mat (z i.1))*G.mat (qForecast S i k (t • E.1,E.2))*G.mat (z (i.1+step i.2)) := by
    change G.mat (F t) = star _ * G.mat (qForecast S i k (t • e,E.2)) * _
    rw [he,← G.mat_inv,← G.mat_mul, ← G.mat_mul, show (z i.1)⁻¹ * (z i.1*(F t)* (z (i.1+step i.2))⁻¹) * z (i.1+step i.2)=F t by group]
  have hC2 : DifferentiableAt ℝ (G.mat∘F) 0 := by
    change DifferentiableAt ℝ (fun t : ℝ => G.mat (F t)) 0
    simp_rw [Hmat]
    exact ((differentiableAt_const _).mul h2).mul (differentiableAt_const _)
  have hz1 : M u=response (qTangent S i k) E.1 E.2 := hl.2
  refine ⟨hl.1,hC2,?_,?_⟩
  · rw [← neutral S W i k a]; exact norm_check F hC2
  have HQ (t : ℝ) : chordColor S i k (t • E.1,E.2)=M (G.curvature (V i*(F t)⁻¹)) := by
    change G.curvature (G.lieExp B* (qForecast _ _ _ (t • e,E.2))⁻¹) = _
    rw [he,← hV]; unfold Lattice.gauge
    rw [show z i.1 * V i * _ * (z i.1 * _ * _)⁻¹ = z i.1 * (V i*(F t)⁻¹)*(z i.1)⁻¹ by group,G.curvature_conjugate]; rfl
  have hH v : M (Z S v V i) = c0 • M (G.curvature (V i*(v i)⁻¹)) := by rw [Z,hk,map_smul]
  have hh a : ‖a‖ = ‖M a‖ := (G.norm_adjoint _ _).symm
  have hs0 : M (Z S (S.prediction W k) V i) = c0 • chordColor S i k (0,E.2) := by rw [hH,← neutral S W i k a]; simpa only [zero_smul] using! congr_arg (c0 • ·) (HQ 0).symm
  have hs1 : M (Z S (S.prediction U k) V i) = c0 • chordColor S i k E := by rw [hH,hi]; simpa only [one_smul,F,actuate,Prod.mk.eta] using! congr_arg (c0 • ·) (HQ 1).symm
  refine ⟨?_,?_,?_⟩
  · rw [hh,map_sub,hs1,map_sub,hs0,map_smul,hz1, ← smul_sub, ← smul_sub,norm_smul,Real.norm_of_nonneg h0.le,mul_assoc]; exact mul_le_mul_of_nonneg_left h3 h0.le
  · rw [hh,hs0,norm_smul,Real.norm_of_nonneg h0.le,mul_assoc]; exact mul_le_mul_of_nonneg_left h4 h0.le
  rw [hh,map_smul,hz1,norm_smul,Real.norm_of_nonneg h0.le,mul_assoc]; exact mul_le_mul_of_nonneg_left h5 h0.le
end YM.SectorNext.Remainder.Affine
