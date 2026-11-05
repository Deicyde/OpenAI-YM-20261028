import YM.AnalyticBridge.RESET_INCOME_PORT.Fiber
import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Forecast
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Primal
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Coach
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Museum
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest
import YM.Progress.STATIONARY_SCENES.Probe


/-!
# Coarse curl and leading linear fine curl under held patch gauge

Preserving cochain ordering. No unidentified one-step prediction lemma here;
use only the flat crossing equation of this actual Tube and the stencil
comparison of V (including flags on Y). `Seam` purchases at fixed tower
prices chosen before L for the actual linear-leading reduction. The locally
cut-off coarse-field extension is NOT generally Healthy past this buffer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Matrix Next Next.Free Next.SectorChange Next.Fluctuations
    Exterior Bloch Bid MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {V : Config G c} {Y : Support c}
    {o : Site c} {g : Site c → G.El} {b : Directions G c} {r C M δ α x y t w : ℝ}

lemma labels_area (v : Directions G c) : ‖Flat.labels v‖ ≤ ‖v‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun _ => norm_le_pi_norm v _)
lemma labels_eq (v : Directions G c) : represent (Flat.labels v)=increment 1 v := by
  unfold represent; congr 1; funext i; exact congr_arg v (Prod.ext rfl (axisEquiv.symm_apply_apply i.2))

structure Web (G : Gauge) where
  radius : ℝ
  scale : ℝ
  pos : 0 < radius
  cost : 1 ≤ scale
  linear {n : Side} (a : LogField G n) (p : Cell n) : ‖Work.F03.faceCurl p a‖ ≤ scale*‖a‖
  defect {n : Side} (a : LogField G n) (p : Cell n) : ‖a‖ ≤ radius → ‖G.curvature (faceValue (represent a) p)- Work.F03.faceCurl p a‖ ≤ scale*‖a‖^2
  travel {n : Side} (a : LogField G n) (p : Cell n) : ‖a‖ ≤ radius → G.chord (faceValue (represent a) p) ≤ 2 * ‖G.curvature (faceValue (represent a) p)‖

set_option maxHeartbeats 520000 in
lemma webExists (G : Gauge) : Nonempty (Web G) := by
  obtain ⟨Q,r,hQ,hr,h⟩ := face_chart_cost G
  obtain ⟨C,s,hC,hs,H⟩ := chord_chart_cost G
  obtain ⟨_,z,_,hz,hz'⟩ := Work.E05.curvature_lower G
  refine ⟨min (min r s) (z/(4*C)),max 1 Q, lt_min (lt_min hr hs) (by positivity),le_max_left ..,fun a p => ((h a p).1).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)),fun a p ha => ((h a p).2 (ha.trans ((min_le_left ..).trans (min_le_left ..)))).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)),fun a p ha => ?_⟩
  let U:=represent a
  have he : G.chord (faceValue U p) ≤ z := by
    refine (travel_chord (h:=C*‖a‖) U (square p.2.val.1 p.2.val.2) p.1 (fun i => ?_)).trans ?_
    · change G.chord (G.lieExp _ * 1) ≤ _; rw [mul_one]; exact (H _ ((norm_le_pi_norm a _).trans (ha.trans ((min_le_left ..).trans (min_le_right ..))))).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm a _) hC.le)
    have h := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (ha.trans (min_le_right ..)); simpa [square,mul_comm,mul_left_comm,mul_assoc] using h
  change G.chord (faceValue U p) ≤ _ * ‖G.curvature (faceValue U p)‖
  nlinarith only [(hz' _ he).2,norm_nonneg (G.curvature (faceValue U p))]

namespace Web
variable (W : Web G) (hv : Healthy (temp x) Y V) (hs : Museum.Station Y x o) (he : AgreeNear id o (reach x) (gauge g V) (increment 1 b))
    (ht : temp x ≤ 2*t) (ha : ‖b‖ ≤ w) (hr : w ≤ W.radius) (hC : W.scale*w^2 ≤ t)
include W hv hs he ht ha hr hC
lemma inner_toll (p : Cell c) (hp : separation p.1 o ≤ radiusB x) : ‖Work.F03.faceCurl p (Flat.labels b)‖ ≤ 3*t := by
  have h' : p.1 ∈ Y := hs (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,by rw [separation_comm]; unfold reach; omega⟩)
  have h : G.chord (faceValue V p) ≤ temp x := not_lt.mp (fun h => Finset.disjoint_left.mp hv h' ((flags_spec ..).mpr ⟨p,Work.E01.base_touched _,h⟩))
  have hh : faceValue (gauge g V) p=faceValue (increment 1 b) p := by
    refine travel_local _ _ _ _ (fun e h _ => he e ?_)
    have h := separation_triangle o p.1 e.1; have hh := Work.E01.sep_touched p e.1 (List.mem_toFinset.mpr ‹_›); rw [separation_comm] at hp; change separation o e.1 ≤ _; unfold reach; omega
  have hf : ‖G.curvature (faceValue (represent (Flat.labels b)) p)‖ ≤ 2*t := by
    apply (G.curvature_norm _).trans; rw [labels_eq,← hh,face_gauge,G.chord_conj]; exact h.trans ht
  have heq := (W.defect _ p ((labels_area b).trans (ha.trans hr))).trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) ((labels_area b).trans ha) _) (zero_le_one.trans W.cost)).trans hC)
  set A := G.curvature _
  refine le_trans (b:= ‖A‖ + ‖A-Work.F03.faceCurl p (Flat.labels b)‖) (by simpa using norm_sub_le A (A-Work.F03.faceCurl p (Flat.labels b))) ?_; linarith only [hf,heq]

lemma shelters (hd : 0 ≤ δ) (hW : W.scale*w ≤ 3*t*Real.exp (δ*radiusB x)) : Forecast.sheltered (Newt.load (Exterior.d 1 c) (Flat.labels b)) o (3*t) δ := by
  intro i; let p : Cell c := (i.1,plaqEquiv.symm i.2)
  have h : i = (p.1,plaquette p.2) := Prod.ext rfl (plaqEquiv.apply_symm_apply i.2).symm
  have ht' : 0≤t := le_trans (mul_nonneg (zero_le_one.trans W.cost) (sq_nonneg _)) hC
  rw [← Forecast.comatrix, h]; change ‖Work.F03.faceCurl p _‖ ≤ _
  by_cases hi : separation p.1 o ≤ radiusB x
  · exact (W.inner_toll hv hs he ht ha hr hC _ hi).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
  apply ((W.linear (Flat.labels b) p).trans ((mul_le_mul_of_nonneg_left ((labels_area b).trans ha) (zero_le_one.trans W.cost)).trans hW)).trans; dsimp only; gcongr; omega
end Web

structure Seam (T : Tube G S) (δ A : ℝ) : Prop where
  tCross : T.R.T.strip δ (A/(S.patch.L.val:ℝ)^2)
  fits : ∃ H H', Towers.Diagonal S H H' T.R ∧ H.dual_diag.acts f * H.diagonal.acts f=1 ∧ H.dual_diag.strip δ A ∧ H'.diagonal.strip δ A

def yarn (δ A : ℝ) := let i : ℝ := Fintype.card (TypeFace 2); 1+i*A*(Real.exp δ*i*A*(i*A*3))
theorem Seam.shield (s : Seam T δ M) (hd : 0<δ) (hm : 0≤M) (W : Web G)
    (hv : Healthy (temp x) Y V) (hs : Museum.Station Y x o) (he : AgreeNear id o (reach x) (gauge g V) (increment 1 b))
    (ht : temp x ≤ 2*t) (ha : ‖b‖ ≤ w) (hr : w ≤ W.radius) (hC : W.scale*w^2 ≤ t)
    (hW : W.scale*w ≤ 3*t*Real.exp (δ*radiusB x)) (y : Cell f) (hy : o=S.ratio.parent y.1) :
    ‖Work.F03.faceCurl y (Flat.labels (route T b))‖ ≤ yarn δ M*t/(S.patch.L.val:ℝ)^2 := by
  obtain ⟨L,N,h,h',hl,hn⟩ := s.fits
  subst o
  have ht' : 0≤3*t := mul_nonneg (by norm_num) ((mul_nonneg (zero_le_one.trans W.cost) (sq_nonneg _)).trans hC)
  have hx := Forecast.foresail h h' hl hn s.tCross hd.le hd hd le_rfl le_rfl hm hm _ y.1 ht' (W.shelters hv hs he ht ha hr hC hd.le hW) y.2
  have hh : Flat.labels (route T b)=Newt.load (installed S.ratio T.R.A0) (Flat.labels b) := by
    funext i; change route T b (i.1, axisEquiv.symm i.2) = _; rw [route,roll_as]; exact congr_arg _ (Prod.ext rfl (axisEquiv.apply_symm_apply i.2))
  rw [hh]; apply hx.trans; gcongr ?_/_; unfold yarn; nlinarith only [ht']
end YM.PhysicalNext.JointLoad.Heir
