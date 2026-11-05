import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Tensor
import YM.Next.SCHEDULE.Stadium
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.UVNext.PRICED_KERNELS.Crews

set_option warningAsError false

/-!
# Coarse gauge action through the sector windows, and through the cut mean

Same tree, records, path/layout Tube and shared prediction tag. Extend the
coarse gauge constant on blocks; Haar-shell variables transformed as actual
bonds of this action (not by shifting Lie coordinates). Keep cuts even here.
No equivariance of an arbitrary external Free/Horizon reroll assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Gauges
open Filter Function Set Lattice RG Precision Exterior Wilson Tree Matrix Bloch Laurent
open Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Oriented Next.SectorChange Rows Orthogonal Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {α β : Type} {G : Gauge} {c f n : Side} {S : StepData c f}

def turn (z : G.El) : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint z with norm_map' := G.norm_adjoint z }
def E (z : G.El) : G.Color ≃L[ℝ] G.Color := ((turn z).toLinearIsometryEquiv rfl).toContinuousLinearEquiv
lemma turn_sum (u : G.El) (v : α → G.Color) : (∑' i, G.adjoint u (v i)) = G.adjoint u (∑' i, v i) := ((E u).map_tsum).symm

def rotating (w : Site n → G.El) : ColorOrtho G (Bond n) := fun i => turn (w i.1)
lemma rotates (w : Site n → G.El) (a : Directions G n) : lifting (rotating w) (Equiv.refl _) a = Motion.swing w a := rfl

lemma barrel_turn (P : PathData G) (z : Site n → G.El) (U : Config G n) (r : ℕ) (b : Cell n → G.Color) (p : Cell n) :
    barrel P r (Lattice.gauge z U) (fun i => G.adjoint (z i.1) (b i)) p = G.adjoint (z p.1) (barrel P r U b p) := by
  rw [barrel,barrel,← turn_sum]; apply tsum_congr; intro i; dsimp only; split
  next hi =>
    let s := (P.row p.2 i).2
    have he : stop p.1 s.walk=(Work.F03.slotFace s p.1).1 := by
      unfold Work.F03.slotFace RG.Slot.offset
      rw [wrap_stop_cover,map_zero,add_comm,← Work.E03.stop_add_left]; simp
    rw [travel_gauge,he,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul ((z _)⁻¹) (z (Work.F03.slotFace s p.1).1),inv_mul_cancel,G.adjoint_one,map_smul]
  rw [map_zero]

lemma shorten_turn (P : PathData G) (z : Site n → G.El) (U : Config G n) (r d : ℕ) (p : Cell n) :
    shorten P r d (Lattice.gauge z U) p= G.adjoint (z p.1) (shorten P r d U p) := by
  rw [shorten,shorten,← turn_sum]; apply tsum_congr; intro i
  unfold shortenTerm; split
  next hi =>
    let s := (P.row p.2 i).2
    have he : stop p.1 s.walk=(Work.F03.slotFace s p.1).1 := by
      unfold Work.F03.slotFace RG.Slot.offset
      rw [wrap_stop_cover,map_zero,add_comm,← Work.E03.stop_add_left]; simp
    unfold PathData.ellTerms; rw [Work.F03.atSite_path,Work.F03.atSite_path,face_gauge,G.curvature_conjugate,travel_gauge,he]
    rw [G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul ((z _)⁻¹) (z _), inv_mul_cancel,G.adjoint_one,map_smul]
  rw [map_zero]

lemma shoot_turn (P : Clip) (z : Site n → G.El) (U : Config G n) (p : Cell n) :
    shoot P (Lattice.gauge z U) p = G.adjoint (z p.1) (shoot P U p) := by unfold shoot; rw [face_gauge,G.curvature_conjugate,map_smul]
lemma plotted_turn (P : PathData G) (p : Clip) (r d : ℕ) (U : Config G n) (z : Site n → G.El) (i : Twin n) : plotted P p r d (Lattice.gauge z U) i = G.adjoint (z i.1.1) (plotted P p r d U i) := by unfold plotted; split <;> first | exact shorten_turn .. | exact shoot_turn ..
lemma thin_turn (P : PathData G) (p : Clip) (t : ℝ) (d r : ℕ) (U : Config G n) (z : Site n → G.El) (i : Twin n) : thinned P p t d r (Lattice.gauge z U) i = G.adjoint (z i.1.1) (thinned P p t d r U i) := by
  have he : PathData.kept p t i.1.1 (Lattice.gauge z U) ↔ PathData.kept p t i.1.1 U := by simp [PathData.kept]
  unfold thinned; rw [if_congr he rfl rfl]
  split
  · split <;> first | exact shorten_turn .. | rw [map_zero]
  rw [toll_gauge,shoot_turn,map_smul]
lemma Z_turn (U V : Config G c) (z : Site c → G.El) (i : Bond c) : Pressure.Tube.Z S (Lattice.gauge z U) (Lattice.gauge z V) i = G.adjoint (z i.1) (Pressure.Tube.Z S U V i) := by
  unfold Pressure.Tube.Z Lattice.gauge; rw [show z i.1*V i*_ * (z i.1 * U i * _)⁻¹=z i.1 * (V i*(U i)⁻¹)*(z i.1)⁻¹ by group,G.curvature_conjugate,map_smul]

lemma turned_sum (u v : G.El) {f g : α → Pay G} (h : ∀ i z, g i (G.adjoint v z)=G.adjoint u (f i z)) (z : G.Color) :
    (∑' i,g i) (G.adjoint v z) = G.adjoint u ((∑' i,f i) z) := by
  let L := (E v).arrowCongr (E u)
  have hh (H : Pay G) (a : G.Color) : L H (G.adjoint v a) = G.adjoint u (H a) := by
    change E u (H ((E v).symm (E v a))) = _; rw [ContinuousLinearEquiv.symm_apply_apply]; rfl
  rw [show g = fun i => L (f i) from ?_,← L.map_tsum]; exact hh ..
  funext i; apply ContinuousLinearMap.ext; intro a
  obtain ⟨b,rfl⟩ := (E v).surjective a; exact (h i b).trans (hh (f i) b).symm

lemma rated_turn (U : Config G n) (z : Site n → G.El) (p : Site n) (w : Walk) (b : ℝ) (v : G.Color) :
    rated (Lattice.gauge z U) p w b (G.adjoint (z (stop p w)) v) = G.adjoint (z p) (rated U p w b v) := by
  change b • (G.adjoint (travel _ _ _)) _ = G.adjoint _ (b • G.adjoint _ v)
  rw [travel_gauge,map_smul,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul ((z _)⁻¹) (z _),inv_mul_cancel,G.adjoint_one]

lemma lane_turn {α β : Type*} (A : Row α β) (d R : ℕ) (U : Config G c) (z : Site c → G.El) (i : Co c α) (j : Co c β) (v : G.Color) :
    lane R d (Lattice.gauge z U) A i j (G.adjoint (z j.1) v) = G.adjoint (z i.1) (lane R d U A i j v) := by
  apply turned_sum; intro y v; unfold priced; split
  next h =>
    have he := rated_turn U z i.1 (route 0 y 1) (A i.2 j.2 y) v
    rw [← show stop i.1 (route 0 y 1)=j.1 from (by rw [h.2]; simpa only [map_zero,add_zero] using Work.E03.stop_route i.1 0 y)]; exact he
  next h => change 0 = G.adjoint _ 0; rw [map_zero]
lemma leap_turn (M : Towers S.patch.L) (R : ℕ) (U : Config G c) (z : Site c → G.El) (i : Twin f) (j : Twin c) (v : G.Color) :
    leap S M R (Lattice.gauge z U) i j (G.adjoint (z j.1.1) v) = G.adjoint (z (S.ratio.parent i.1.1)) (leap S M R U i j v) := by
  apply turned_sum; intro y v; unfold casted; dsimp only; split
  next h =>
    rw [← copied S.ratio S.patch.odd_side U z]
    let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • y) 1
    have hh : S.ratio.parent (stop (mesh i).1 w)=(mesh j).1 := by
      rw [h.2,show stop _ w = _ from Work.E03.casted_endpoint S (mesh i).1 y,S.ratio.embed_parent]
    exact hh ▸ rated_turn (replica S.ratio U) (constantGauge z S.ratio) (mesh i).1 w _ v
  next h => change 0 = G.adjoint _ 0; rw [map_zero]

lemma Mv_turn (T : Tube G S) (R : ℕ) (t : ℝ) (V : Config G c) (z : Site c → G.El) (i : Twin f) :
    T.Mv R t (Lattice.gauge z V) i = G.adjoint (z (S.ratio.parent i.1.1)) (T.Mv R t V i) := by
  unfold Tube.Mv zip; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [Tube.vision,thin_turn]; exact leap_turn ..
lemma Mw_turn (T : Tube G S) (R : ℕ) (t : ℝ) (V : Config G c) (z : Site c → G.El) (i : Bond c) :
    T.Mw R t (Lattice.gauge z V) i = G.adjoint (z i.1) (T.Mw R t V i) := by
  unfold Tube.Mw zip; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [Tube.vision,thin_turn]; exact lane_turn ..

section rotation
variable (T : Tube G S) (z : Site c → G.El) (V : Config G c) (s : Signed) (k : S.Choices) (x : ℝ)
def turned (i : Site c) := z (affine s 0 i)

lemma comm (i : Site f) : z (S.ratio.parent (affine s 0 i))=constantGauge (turned z s) S.ratio i := by
  simp [turned,constantGauge,affine,S.ratio.parent_signed S.patch.odd_side]

lemma facade_turn (a : Directions G f) :
    facade S s (Lattice.gauge z V) (lifting (rotating (constantGauge z S.ratio)) (Equiv.refl _) a) = Lattice.gauge (constantGauge (turned z s) S.ratio) (facade S s V a) := by
  unfold facade; rw [← copied S.ratio S.patch.odd_side V z,rotates,Motion.swing_increment, Work.F05.pull_gauge_zero]; congr! 1; exact funext (comm z s)
lemma facade_null : facade S s (Lattice.gauge z V) 0 = Lattice.gauge (constantGauge (turned z s) S.ratio) (facade S s V 0) := by
  simpa using! facade_turn (S:=S) z V s 0
lemma plaquette_turn (p : Cell f) (a : Directions G f) : plaquetteJet S (Lattice.gauge z V) s p (lifting (rotating (constantGauge z S.ratio)) (Equiv.refl _) a)=
    G.adjoint (constantGauge (turned z s) S.ratio p.1) (plaquetteJet S V s p a) := by
  unfold plaquetteJet; refine derives _ (E _) (fun a => ?_) a
  rw [facade_turn,face_gauge,G.curvature_conjugate]; rfl

lemma predicts (p : Bond c) (a : Directions G f) (h : S.patch.Branches S.kernel G) : predictGroup (Lattice.gauge z V) k s p (lifting (rotating (constantGauge z S.ratio)) (Equiv.refl _) a)=
    turned z s p.1 * predictGroup V k s p a * (turned z s (p.1+step p.2))⁻¹ := by
  unfold predictGroup; rw [facade_turn,(choice_gauge h _ (choice s k) _).2]; simp only [Lattice.gauge,Function.comp_apply,constantGauge,Ratio.embed_parent]
lemma pred_null (h : S.patch.Branches S.kernel G) : S.prediction (facade S s (Lattice.gauge z V) 0) (choice s k) = Lattice.gauge (turned z s) (S.prediction (facade S s V 0) (choice s k)) := by
  funext i; simpa only [map_zero] using! predicts z V s k i 0 h
lemma block_turn (p : Bond c) (a : Directions G f) (h : S.patch.Branches S.kernel G) : blockJet (Lattice.gauge z V) k s p (lifting (rotating (constantGauge z S.ratio)) (Equiv.refl _) a)=
    G.adjoint (turned z s p.1) (blockJet V k s p a) := by
  unfold blockJet; refine derives _ (E _) (fun a => ?_) a
  unfold predictorTurn; rw [predicts z V s k p a h]
  have hp := predicts z V s k p 0 h; rw [map_zero] at hp; rw [hp]; change _ = G.adjoint _ _; rw [← G.curvature_conjugate]; congr 1; group

def outGauge (i : Slots S) : Site c := i.2.elim (fun j => affine i.1 0 (S.ratio.parent j.1.1)) (fun j => affine i.1 0 j.1)
def outRotation : ColorOrtho G (Slots S) := fun i => turn (z (outGauge i))
lemma gauge_bump (h : S.patch.Branches S.kernel G) (a : Directions G f) (i : Slots S) : bump T x (Lattice.gauge z V) k (lifting (rotating (constantGauge z S.ratio)) (Equiv.refl _) a) i=outRotation z i (bump T x V k a i) := by
  obtain ⟨s,j|j⟩ := i
  · unfold bump; simp only [Sum.elim_inl]; unfold faceKick; split
    next hh => simp_rw [facade_null,plaquette_turn]; exact barrel_turn ..
    next hh => rw [plaquette_turn]; exact (map_smul (G.adjoint _) _ _).symm
  unfold bump; simp only [Sum.elim_inr,noiseKick,block_turn z V s k j a h]
  exact ((map_neg (G.adjoint _) _).trans (congr_arg Neg.neg (map_smul (G.adjoint _) _ _))).symm
lemma gauge_base (h : S.patch.Branches S.kernel G) (i : Slots S) : base T x (Lattice.gauge z V) k i=outRotation z i (base T x V k i) := by
  obtain ⟨s,j|j⟩ := i
  · unfold base faceFixed; dsimp only [Sum.elim_inl]; rw [facade_null,Work.F05.pull_gauge_zero,Mv_turn, Tube.Xf,plotted_turn]; exact (map_sub (G.adjoint _) _ _).symm
  unfold base noiseFixed; rw [Work.F05.pull_gauge_zero,pred_null z V s k h]; change Pressure.Tube.Z _ _ (Lattice.gauge (turned z s) _) _ - T.Mw _ _ (Lattice.gauge (turned z s) _) j = _; rw [Mw_turn,Z_turn]; exact (map_sub (G.adjoint _) _ _).symm

variable (A : Stores S) (F : Forest S.ratio)
lemma gauge_cov (h : S.patch.Branches S.kernel G) {σ C Λ : ℝ} (hT : T.up.Bounds T.high σ C Λ) :
    Equivalent (x:=x) (A:=A) (F:=F) T V (Lattice.gauge z V) k k (Equiv.refl _) (onBond (rotating (constantGauge z S.ratio))) :=
  gram_motion (Equiv.refl _) _ (Equiv.refl _) (Equiv.refl _) (outRotation z) h hT (fun _ => rfl) (gauge_bump T z V k x h) ⟨fun _ => rfl,fun _ => rfl⟩

def gaugeY (Y : LinkArray G (Frozen A x F)) : LinkArray G (Frozen A x F) := fun i =>
    z (S.ratio.parent i.val.val.1)*Y i*(z (S.ratio.parent (i.val.val.1+step i.val.val.2)))⁻¹
lemma shell_turn (Y : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ) (i) : autoShell q d (Lattice.gauge z V) (gaugeY z x A F Y) i = G.adjoint (z (S.ratio.parent i.val.val.1)) (autoShell q d V Y i) := by
  unfold autoShell; rw [← copied S.ratio S.patch.odd_side, ← patched_covary]; unfold Lattice.gauge gaugeY constantGauge; simp only [Function.comp_apply]; congr 1; group


end rotation
end YM.AnalyticBridge.GaussianFieldAlignment.Gauges
