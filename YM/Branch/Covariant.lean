import YM.Branch.Predict

/-! Covariance of the exact blocking density and cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice Wilson Function
open scoped Topology Matrix.Norms.Frobenius BigOperators
namespace StepData
variable {G : Gauge} {c f : Side} (S : StepData c f) (h : S.patch.Branches S.kernel G)
include h

lemma prediction_channel (s : Signed) (b : Site c) (U : Config G f) (t : S.Choices) :
    S.prediction (pull s (S.ratio.embed b) U) t=pull s b (S.prediction U (S.withinChoice s b t)) := by
  funext ⟨x,i⟩; unfold pull prediction; unfold Step.read
  change S.patch.predict S.kernel (S.connector (pull s (S.ratio.embed b) U) _ _) _ =
    (if _ then (S.patch.predict S.kernel (S.connector U (S.withinSites s b t.1) (sendEdge s b (x,i))) (S.withinBond s b t.2 (sendEdge s b (x,i))))⁻¹ else S.patch.predict S.kernel (S.connector U (S.withinSites s b t.1) (sendEdge s b (x,i))) (S.withinBond s b t.2 (sendEdge s b (x,i))))
  rw [S.port_bond]; cases he : s.flip i
  · rw [if_neg (by simp [he,posDir,Step.rotate]), S.positive h _ _ _ _ _ _ he]; exact (S.patch.bond_pull (h:=h) ..).2
  rw [if_pos (by simp [he,posDir,Step.rotate]), S.negative h _ _ _ _ _ _ he]; exact (S.patch.bond_inv (h:=h) ..).2

lemma mass_channel (s : Signed) (b : Site c) (U : Config G f) (t : S.Choices) :
    S.likelihood (pull s (S.ratio.embed b) U) t=S.likelihood U (S.withinChoice s b t) := by
  unfold likelihood; apply congr_arg₂
  · conv_rhs => rw [← Equiv.prod_comp (sendSites s b)]
    refine Finset.prod_congr rfl fun i _ => ?_
    change _=S.patch.frameMass S.kernel (expandAt (S.ratio.embed (affine s b i)) U) (S.withinSites s b t.1 (affine s b i))
    rw [S.port_site,expandAt_pull, S.port]; exact (S.patch.frames_channel h ..).1
  conv_rhs => rw [← Equiv.prod_comp (sendBonds s b)]
  refine Finset.prod_congr rfl ?_; rintro ⟨x,i⟩ _
  change _=S.patch.predictorMass S.kernel (S.connector U (S.withinSites s b t.1) (sendEdge s b (x,i))) (S.withinBond s b t.2 (sendEdge s b (x,i)))
  rw [S.port_bond]; cases he : s.flip i
  · rw [S.positive h _ _ _ _ _ _ he]; exact (S.patch.bond_pull (h:=h) ..).1
  rw [S.negative h _ _ _ _ _ _ he]; exact (S.patch.bond_inv (h:=h) ..).1

omit h in
lemma noise_channel (s : Signed) (b : Site c) (β) (V Y : Config G c) :
    S.noise β (pull s b V) (pull s b Y)=S.noise β V Y := by
  unfold noise; conv_rhs => rw [← Equiv.prod_comp (sendBonds s b)]
  refine Finset.prod_congr rfl ?_; rintro ⟨x,i⟩ _
  unfold pull Step.read
  split
  · change _ * S.penaltyWeight β ((Y _)⁻¹*((V _)⁻¹)⁻¹) = _* S.penaltyWeight β (Y (sendEdge s b (x,i))*(V (sendEdge s b (x,i)))⁻¹)
    have he (u v : G.El) : S.penaltyWeight β (u⁻¹*(v⁻¹)⁻¹)=S.penaltyWeight β (u*v⁻¹) := by
      unfold penaltyWeight
      rw [← G.price_inv (u*v⁻¹), show (u*v⁻¹)⁻¹ = u * (u⁻¹*(v⁻¹)⁻¹) * u⁻¹ by group, G.price_conj]
    rw [he]; rfl
  rfl

lemma channel (s : Signed) (b : Site c) (β : ℝ) (U : Config G f) (V : Config G c) :
    S.density β (pull s (S.ratio.embed b) U) (pull s b V)=S.density β U V := by
  unfold density
  conv_rhs => rw [← Equiv.sum_comp (S.withinChoice s b)]
  simp_rw [mass_channel S h,prediction_channel S h,S.noise_channel]

lemma covary (k : Site f → G.El) (β : ℝ) (U : Config G f) (V : Config G c) :
    S.density β (Lattice.gauge k U) (Lattice.gauge (k ∘ S.ratio.embed) V)=S.density β U V := by
  unfold density; refine Finset.sum_congr rfl fun i _ => ?_
  have he : S.likelihood (Lattice.gauge k U) i=S.likelihood U i := by
    unfold likelihood; apply congr_arg₂
    · refine Finset.prod_congr rfl fun j _ => ?_; rw [expandAt_gauge]; exact (S.patch.frame_gauged h ..).1
    refine Finset.prod_congr rfl fun j _ => ?_; rw [S.updateGauged h]; exact (S.patch.bond_gauge (h:=h) ..).1
  rw [he]; unfold noise; apply congr_arg
  refine Finset.prod_congr rfl fun j _ => ?_; unfold prediction; rw [S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2]
  have hh (u v x y : G.El) : S.penaltyWeight β (u*x*v⁻¹*(u*y*v⁻¹)⁻¹)=S.penaltyWeight β (x*y⁻¹) := by
    unfold penaltyWeight; rw [show u*x*v⁻¹*(u*y*v⁻¹)⁻¹=u*(x*y⁻¹)*u⁻¹ by group,G.price_conj]
  simp only [Lattice.gauge,Function.comp_apply,hh]
end StepData

lemma Calendar.blocks_go {G : Gauge} (A : Calendar G) (h : ∀ P : Patch, P.Branches A.kernel G) (m p) :
    A.BlockControl m p :=
  ⟨h _,fun β U V s b ↦ (A.op m p).channel (h _) s b β U V, fun β U V t ↦ (A.op m p).covary (h _) t β U V⟩
end YM.RG
