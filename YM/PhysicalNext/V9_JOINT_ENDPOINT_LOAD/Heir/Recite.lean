import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Chorus

/-! # The local relative chart and its quantitative first-order predictor

For the large (possibly winding) E call on separate local gauges. Later
use a HETEROGENEOUS assembly of these charts on the very same argument
fields (especially same Gaussian and same tags) after returning via
fixed gauge. Not assuming a small-field neighborhood around the entire
support or that all its masked reads survive from the trimmed data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson Pressure Precision RG Tree Next Next.Fluctuations Next.SectorChange
    Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {x : ℝ} {k : S.Choices} {n : ℕ}
    {t Q r : ℝ}

abbrev Echo (G : Gauge) (c f : Side) := Deck G c f × Deck G c f
abbrev πL (G : Gauge) (c f : Side) := ContinuousLinearMap.fst ℝ (Deck G c f) (Deck G c f)
abbrev πR (G : Gauge) (c f : Side) := ContinuousLinearMap.snd ℝ (Deck G c f) (Deck G c f)
variable (T) (F) (x) (k)
def grounds (p : Echo G c f) (i : Bond f) : Chord G := ((0,display T F x k false p.2 i), (display T F x k false p.1 i,0))
def echo (p : Echo G c f) : Directions G f := fun i => decode (grounds T F x k p i)
def realStroke := (mainStroke T F false).comp (πL G c f - πR G c f)

structure Act (n : ℕ) (t Q : ℝ) : Prop extends Tour T F x k n t Q where
  calibrated : Portrait (echo T F x k) (realStroke T F) n (temp x) t Q
  visits : ∀ p : Echo G c f, ‖p‖ ≤ t → increment (sounds T F x k false p.2) (echo T F x k p) = sounds T F x k false p.1
variable {T F x k}

private lemma echo_deriv (i : Bond f) (h : Tour T F x k n t Q) (ht : 0<t) (hn : 1 ≤ n) (p : Echo G c f) :
    fderiv ℝ (fun p => echo T F x k p i) 0 p = fderiv ℝ (display T F x k false) 0 (p.1-p.2) i := by
  let J := display T F x k false; have hz : J 0=0 := (h.costs false).home
  have he := ((h.costs false).uniform 0 (show ‖(0:Deck G c f)‖ ≤ t by simpa using ht.le)).smooth.differentiableAt (by exact_mod_cast (show n ≠ 0 by omega))
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  have he₁ := (L.hasFDerivAt.comp _ he.hasFDerivAt).comp (f:=πL G c f) (0:Echo G c f) (πL G c f).hasFDerivAt
  have he₂ := (L.hasFDerivAt.comp _ he.hasFDerivAt).comp (f:=πR G c f) (0:Echo G c f) (πR G c f).hasFDerivAt
  have hh : grounds T F x k 0 i=0 := by unfold grounds; simp only [Prod.fst_zero,Prod.snd_zero,(show display T F x k false 0=0 from hz),Pi.zero_apply]; rfl
  have hs := (((hasFDerivAt_const (0:G.Color) (0:Echo G c f)).prodMk he₂).prodMk (he₁.prodMk (hasFDerivAt_const (0:G.Color) (0:Echo G c f))))
  change fderiv ℝ (decode ∘ fun p => grounds T F x k p i) 0 _ = _
  rw [fderiv_comp 0 (f:=fun p => grounds T F x k p i) (show DifferentiableAt ℝ decode (grounds T F x k 0 i) by rw [hh]; exact (decode_analytic G).1.differentiableAt (by simp)) hs.differentiableAt,
    hh, show fderiv ℝ (fun p => grounds T F x k p i) 0 = _ from hs.fderiv,ContinuousLinearMap.comp_apply,decode_first,map_sub,Pi.sub_apply]
  change (0:G.Color) + fderiv ℝ J 0 p.1 i + (0:G.Color) - fderiv ℝ J 0 p.2 i = _; rw [zero_add,add_zero]

lemma Tour.weaker (h : Tour T F x k n t Q) {r C} (hr : r ≤ t) (hC : Q ≤ C) : Tour T F x k n r C :=
    ⟨fun sw p hp => h.represents sw p (hp.trans hr),fun sw => (h.costs sw).relax hr hC (Work.E04.temp_nonneg x)⟩

set_option maxHeartbeats 1000000 in
private lemma recitals {K : ℝ} (h : Tour T F x k n t Q) (ht : 0<t) (hq : 1≤Q) (hn : 1 ≤ n) (hr : 0<r)
    (hD : ∀ p : Chord G, ‖p‖ ≤ r → Through n (decode (G:=G)) p K ∧ G.lieExp (decode p) = touch p) :
    Act T F x k n (min t (r/Q)) (|Push.Uniform.composeCost n K Q|+2*Q) := by
  let J := display T F x k false
  have hQ := zero_lt_one.trans_le hq; let M := |Push.Uniform.composeCost n K Q|+2*Q; have hm : 2*Q≤M := le_add_of_nonneg_left (abs_nonneg _)
  have hz : J 0=0 := (h.costs _).home
  have hu p (he : ‖p‖ ≤ t) := (h.costs false).uniform p he
  let s := min t (r/Q); have hs : 0<s := lt_min ht (div_pos hr hQ)
  have he (p : Echo G c f) (hp : ‖p‖ ≤ s) (i : Bond f) : G.lieExp (echo T F x k p i)*(sounds T F x k false p.2) i=(sounds T F x k false p.1) i ∧
      Through n (fun y => echo T F x k y i) p M := by
    let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
    have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by rw [one_mul]; exact norm_le_pi_norm w _)
    let K (p : Echo G c f) := grounds T F x k p i
    have ha (p : Echo G c f) (hp : ‖p‖ ≤ s) : Through n K p Q := by
      have hy (A : Echo G c f →L[ℝ] Deck G c f) (hA : ‖A‖ ≤ 1) : Through n (L ∘ (J ∘ A)) p Q := by
        have ht := ((A.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans hp)).trans (min_le_left ..)
        simpa only [one_mul] using (linear_through _ (pre_through A hA p (hu _ ht)) hL)
      have he : Through n (fun _ : Echo G c f => (0:G.Color)) p Q := Through.control (Push.Uniform.allows_const _ (by simpa using hQ.le))
      exact pair_through (pair_through he (hy (πR G c f) (ContinuousLinearMap.norm_snd_le ..))) (pair_through (hy (πL G c f) (ContinuousLinearMap.norm_fst_le ..)) he)
    have hh : K 0=0 := by change ((0,(J 0) i),(J 0 i,0))=(0:Chord G); simp [hz]
    obtain ⟨hb,hR⟩ := hD (K p) ((locate ha hn hh hp).trans ((mul_le_mul_of_nonneg_left (hp.trans (min_le_right ..)) hQ.le).trans_eq (mul_div_cancel₀ _ hQ.ne')))
    refine ⟨?_,(Through.comp (g:=decode) (f:=K) hb (ha p hp)).mono ((le_abs_self _).trans (le_add_of_nonneg_right (by linarith)))⟩
    have hp j hj : G.lieExp (J j i)=sounds T F x k false j i := (mul_one _).symm.trans (congr_fun (h.represents false j hj) i)
    change G.lieExp (decode (K p))*_= _
    rw [hR,touch]; change G.lieExp 0 * (G.lieExp (J p.1 i) * G.lieExp 0) * (G.lieExp (J p.2 i))⁻¹ * _ = _
    rw [G.mat_lieExp_zero,mul_one, one_mul,hp _ (((norm_fst_le ..).trans ‹‖p‖≤s›).trans (min_le_left ..)),hp p.2 (((norm_snd_le ..).trans ‹‖p‖≤s›).trans (min_le_left ..))]
    group
  have hC p hp := pi_through (f:=echo T F x k) (show 0≤M from (by positivity : (0:ℝ)≤2*Q).trans hm) (fun i => (he p hp i).2)
  refine { (h.weaker (min_le_left ..) (by linarith)) with visits := fun p hp => funext fun i => (he p hp i).1, calibrated := ⟨hC,?_,?_⟩ }
  · funext i; unfold echo grounds; dsimp only [Prod.fst_zero,Prod.snd_zero]; simp only [(show display T F x k false 0=0 from hz),Pi.zero_apply]; exact decode_zero
  have hx : DifferentiableAt ℝ (echo T F x k) 0 := (hC 0 (by simpa using hs.le)).smooth.differentiableAt (by exact_mod_cast (show n ≠ 0 by omega))
  have h : fderiv ℝ (echo T F x k) 0=(fderiv ℝ J 0).comp (πL G c f-πR G c f) := by
    refine ContinuousLinearMap.ext fun u => funext fun i => ?_
    let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
    have he := DFunLike.congr_fun ((L.hasFDerivAt.comp 0 hx.hasFDerivAt).fderiv) u
    exact he.symm.trans (echo_deriv i h ht hn u)
  rw [h,realStroke,← ContinuousLinearMap.sub_comp]
  have hx := (‹Tour ..›.costs false).miss
  calc
    _ ≤ (Q*temp x)*2 := (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul hx ((norm_sub_le ..).trans
      ((add_le_add (ContinuousLinearMap.norm_fst_le ..) (ContinuousLinearMap.norm_snd_le ..)).trans_eq (by norm_num))) (norm_nonneg _) ((norm_nonneg _).trans hx))
    _ ≤ _ := by rw [mul_comm (Q*_), ← mul_assoc]; exact mul_le_mul_of_nonneg_right hm (Work.E04.temp_nonneg _)

theorem recital (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r Q : ℝ, 0<r ∧ 1≤Q ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), Act T F x k n r Q := by
  obtain ⟨t,Q,ht,hQ,h⟩ := orchestra G P Pt hp n hn
  obtain ⟨K,r,hK,hr,he⟩ := decode_cert G n
  refine ⟨min t (r/Q),|Push.Uniform.composeCost n K Q|+2*Q,lt_min ht (by positivity),by linarith [abs_nonneg (Push.Uniform.composeCost n K Q)],?_⟩
  filter_upwards [h] with x h c f S T hP hT hp F k
  exact recitals (h S T hP hT hp F k) ht hQ (by omega) hr he
end YM.PhysicalNext.JointLoad.Heir
