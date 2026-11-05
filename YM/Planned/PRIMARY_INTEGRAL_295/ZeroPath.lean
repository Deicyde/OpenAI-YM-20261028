import YM.Planned.PRIMARY_INTEGRAL_295.Columns
import YM.Planned.PRIMARY_INTEGRAL_295.Unload


/-!
# Centered log path used for the stationary read, before plugging in the row.

The actual positive link holonomy. Use cover (initial vertex), **finite**
jet behavior only. `lane` does not promise a logarithm for the far-out
values, but all our assertions about its local derivatives are valid even at
those initial vertices. The response to be fed into the powered stationary
rows is evaluated as a Taylor jet only (not claiming analyticity on general
vectors of links). Costs here charged once per probe independent of the
number of addresses touched.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops MeasureTheory Precision Bloch Next.Free Place Carrier
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {d n : ℕ} {S : Finset Cover}

/-- Profile for a node pair at the origin-gauge (no gauge transformation
of the radial jet) and a single initial-positive edge. -/
def sampleIn (x : E4) (i : Axis) : Snap G d →L[ℝ] EdgeRead G d :=
    (0 : Snap G d→L[ℝ] G.Color).prod ((0 : Snap G d→L[ℝ] G.Color).prod (road x i))

def lane (x : E4) (i : Axis) (X : Snap G d) : G.Color := logo (sampleIn x i X)
lemma lane_smooth (x : E4) (i : Axis) : ContDiffAt ℝ ω (lane (G:=G) (d:=d) x i) 0 := by
  let F : Snap G d →L[ℝ] EdgeRead G d := sampleIn x i
  have hh := logo_smooth G d
  exact (show ContDiffAt ℝ ω logo (F 0) from by rw [map_zero]; exact hh).comp _ F.contDiff.contDiffAt
lemma lane_root (x : E4) (i : Axis) : lane x i (0 : Snap G d)=0 := by simp [lane]
lemma lane_truth (H : Hol G) (x : Edge Cover) (X : Snap G d) :
    lane (seat x.1) x.2 X=G.plog (G.mat (pureQuest H X x)) := by
  have he := flight_test H x X; simp [lane, logo, peak,sampleIn,he]; rfl

-- Gauge-related `opened` from the cancellation theorem, but here
-- evaluating no gauge endpoints, put Hard coords on coarse probe.
def localLane (X : Snap G d) : Dev S G := fun i => lane (seat (first i).val) (beam i) X
lemma local_smooth (S : Finset Cover) : ContDiffAt ℝ ω (localLane (S:=S) (G:=G) (d:=d)) 0 :=
    contDiffAt_pi.mpr fun _ => lane_smooth ..
lemma local_zero (S : Finset Cover) : localLane (S:=S) (0:Snap G d) = 0 := funext fun i => lane_root _ (beam i)
lemma local_reply (X : Snap G d) : localLane X=opened S (expandCode S 0 X) := by
  funext i; unfold localLane opened; change logo _ = logo _
  apply congr_arg logo; change ((0:G.Color),0,road _ _ X) = ((0:G.Color),0-0,_); simp [expandCode]

lemma section_comp {F : Labels.Frame G d} (H : Hol G) (T : SectionData F) (v : F.Coeff) (hT : T.Sound H) : -- {F}
    slant T v ∘ localLane (d:=d) =ᶠ[𝓝 0] T.evaluate v ∘ pureQuest H := by
  let u := ContinuousLinearMap.inr ℝ (T.stencil→G.Color) (Snap G d)
  have he : Tendsto u (𝓝 0) (𝓝 0) := by rw [← map_zero u]; exact u.continuous.tendsto _
  have ht := lit (T.stencil) (T.cylinder_local v) (hT.gaugeInvariant v) H d
  filter_upwards [he.eventually ht] with X hx; unfold slant; simp only [Function.comp_apply]; rw [local_reply]; exact hx

lemma lane_mail (G : Gauge) (d : ℕ) (n : ℕ) (v : Fin n → Snap G d) :
    ∀ (x : E4) (i : Axis), iteratedFDeriv ℝ n (lane (G:=G) (d:=d) x i) 0 v =
      iteratedFDeriv ℝ n (logo (G:=G) (d:=d)) (0 : EdgeRead G d) (fun k => sampleIn x i (v k)) := by
  intro x i
  exact DFunLike.congr_fun (Next.Foundations.jets_linear (sampleIn (G:=G) (d:=d) x i) ((Place.logo_smooth G d).of_le (show (n:WithTop ℕ∞) ≤ ω from le_top))) v

lemma lane_polynomial (a : Fin n → ℕ) (w : Fin n → Snap G d) (h : ∀ i, throughSlot (w i) (a i)) (hp : ∀ i, 0 < a i) :
    (fun x : E4 => fun i : Axis => iteratedFDeriv ℝ n (lane (G:=G) (d:=d) x i) 0 w)∈ rangeLt (Axis→G.Color) (∑ i,a i) := by
  apply vector_band; intro v
  simp_rw [lane_mail]; change (fun x => iteratedFDeriv ℝ n (logo (G:=G) (d:=d)) (0:EdgeRead G d) (fun k => sampleIn x v (w k))) ∈ _
  have he := logo_cost d (fun _ => 0) w a v hp (fun i=>Submodule.zero_mem _) h
  simp only [jump_zero] at he; exact he

lemma launch_testable (v : Fin n → Snap G d) (p : Spot S) :
    iteratedFDeriv ℝ n (localLane (G:=G) (S:=S) (d:=d)) 0 v p=iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat (first p).val) (beam p)) 0 v := by
  let F : Dev S G→L[ℝ]G.Color:=ContinuousLinearMap.proj p
  have he := F.iteratedFDeriv_comp_left (local_smooth (G:=G) (d:=d) S) (show (n : WithTop ℕ∞) ≤ ω from le_top)
  exact (DFunLike.congr_fun he v).symm

lemma road_cap (b : Cover) (e : Axis) : ‖road (seat b) e (G:=G) (d:=d)‖ ≤ liftCost d b := by
  refine ContinuousLinearMap.opNorm_le_bound _ (liftCost_pos d b) fun A => ?_
  have hr := liftCost_pos d b
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro m
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro s
  exact (shade_slice ((A m).val e) s (seat b) (basis e)).trans (by
    rw [show ‖basis e‖=1 by simp,one_pow,mul_one,mul_comm]
    have hs := covers s
    have h1 : ‖seat b‖^(home s)≤liftCost d b := (pow_le_pow_left₀ (norm_nonneg _) ((shade_seat b).trans
         (le_add_of_nonneg_left zero_le_one)) _).trans (pow_le_pow_right₀ (by simp) (by have hh := m.isLt; omega))
    have he : ‖(A m).val e‖ ≤ ‖A m‖ := norm_le_pi_norm ..
    exact mul_le_mul h1 (he.trans (norm_le_pi_norm A m)) (norm_nonneg _) hr)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
lemma mail_cap (G : Gauge) (d n : ℕ) : ∃ C : ℝ,0 ≤ C ∧ ∀ x : Cover,∀ i : Axis,
    ‖iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) i) 0‖ ≤ C * liftCost (d*n) x := by
  let F := iteratedFDeriv ℝ n (logo (G:=G) (d:=d)) (0:EdgeRead G d)
  refine ⟨‖F‖,norm_nonneg _,fun x i => ?_⟩
  let w : Snap G d→L[ℝ]EdgeRead G d:=sampleIn (seat x) i
  let u : Snap G d →L[ℝ] Route G d := road (seat x) i
  have hu : ‖w‖≤liftCost d x := by
    apply ContinuousLinearMap.opNorm_le_bound _ (liftCost_pos ..); intro A
    change ‖((0:G.Color),0,u A)‖≤ _
    have H : ‖u A‖≤liftCost d x*‖A‖ := (u.le_opNorm A).trans
      (mul_le_mul_of_nonneg_right (road_cap ..) (norm_nonneg A))
    simpa using! H
  rw [show iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) i) 0=F.compContinuousLinearMap fun _=> w from
    ContinuousMultilinearMap.ext fun v => lane_mail G d n v (seat x) i]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, liftCost, pow_mul]; gcongr
  exact hu
end YM.Planned.PrimaryIntegral295.Film
