import YM.Pert.Align.GroundLines
import YM.Pert.Align.Span
/-! Bilinear continuum tests on chart slots. Each turn may be different. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.Pert.Align
open Maxwell Lattice Full Function Filter Topology MeasureTheory Set Atom
open scoped BigOperators Classical RealInnerProductSpace
variable {G : Gauge} {j k : ℕ} {s t : Signed} {n : Side} {h q : ℝ} {v z : E4}
def ordinary (j k : ℕ) (s t : Signed) (h : ℝ) (x y : Site n) : Biform (Pad G j) (Pad G k) := under (jointB G n) (pickDual (chartOrb _ s h x)) (pickDual (chartOrb _ t h y))
open Push.FiniteDetection.Free.Hyper

-- the only restriction we use is on-shell, point displacement kept fixed

def sampleSol (s : Signed) : Shell G j →ₗ[ℝ] YM.Pert.Bare.Response G j where
  toFun Q f r γ := (turn s Q).val f r (basis∘γ)
  map_add' v w := by rw [map_add]; rfl
  map_smul' v w := by rw [map_smul]; rfl

def plain (s : Signed) := pickDual (sampleSol (G:=G) (j:=j) s)

lemma pi_eq (u : Spot G j) (s : Signed) : plain s u.meter = (u.atom s).factor • (constrain (G:=G) (Maxwell.fromF G (basis ∘ s.perm ∘ u.γ) u.color (s.perm u.slash) (s.perm u.via))) := by
  apply LinearMap.ext; intro y
  rw [plain,pickDual_apply,LinearMap.comp_apply]
  let i:=u.slash; let l:=u.via
  change inner ℝ (unitColor G u.color) (sampleSol s y i l u.γ) = _
  erw [real_inner_comm]; rw [to_color]
  have hv m : (Rₛ s) (basis (u.γ m))=Push.FiniteDetection.Free.Hyper.flip s (u.γ m) • basis (s.perm (u.γ m)) := moves_basis ..
  change (turns s y.val i l _) _ = ((Push.FiniteDetection.Free.Hyper.flip s l*Push.FiniteDetection.Free.Hyper.flip s i*((∏ k,Push.FiniteDetection.Free.Hyper.flip s (u.γ k)))) * _)
  simp only [apply_turns,Function.comp_def,hv, y.val _ _ |>.map_smul_univ _ _, PiLp.smul_apply,smul_eq_mul,sign₂];dsimp only [constrain,LinearMap.comp_apply,Maxwell.fromF,LinearMap.coe_mk,AddHom.coe_mk, LinearMap.smul_apply]
  -- recover value on RHS as coordinate
  unfold i l; rw [Submodule.subtype_apply]
  ring

def synthesis (z : E4) (hz : z≠0) (s t : Signed) : Biform (Pad G j) (Pad G k) := under (pairing (G:=G) hz) (plain s) (plain t)
lemma synthesis_spot (s t : Signed) (v : Spot G j) (u : Spot G k) (hz : z≠0) : synthesis z hz s t v.meter u.meter = fluxTarget (v.atom s) (u.atom t) v.color u.color z := by
  let L:=pairing (G:=G) (j:=j) (l:=k) hz
  rw [synthesis,under_at,pi_eq,pi_eq]; change L _ _ = _
  simp only [map_smul, LinearMap.smul_apply,smul_eq_mul]
  
  unfold fluxTarget; dsimp only [Spot.atom,rotated];rw [mul_left_comm,←mul_assoc];rfl
lemma b_meet (A : Pad G j) (B : Pad G k) (s t : Signed) (x y : Site n) (h : ℝ) : ordinary j k s t h x y A B = jointB G n (A ∘ₗ chartOrb j s h x) (B ∘ₗ chartOrb k t h y) := rfl
lemma o_spot (s t : Signed) (v : Spot G j) (u : Spot G k) (x y : Site n) (h : ℝ) : ordinary j k s t h x y v.meter u.meter = jointB G n (flux (v.atom s) h x (unitColor G v.color)) (flux (u.atom t) h y (unitColor G u.color)) := by
  rw [b_meet, Spot.meter_atom v s, Spot.meter_atom u t]
  exact (congrArg₂ (fun U V => (jointB G n) U V) (show _ = flux (v.atom s) h x _ from pro_out (G:=G) (v.atom s) h x (unitColor G v.color)) (show _=flux (u.atom t) h y _ from pro_out (u.atom t) h y (unitColor G u.color)))

lemma cont_cost (s t : Signed) (j k : ℕ) (h : ℝ) (A : Pad G j) (B : Pad G k) : IntegrableOn (fun q=> coverPair j k s t h q A B) cube := by
  have HA (c) := (A.continuous_of_finiteDimensional).comp (proc_cont (j:=j) (u:=h) s c (G:=G) (X:=fun _=>0))
  have HB (c) := (B.continuous_of_finiteDimensional).comp (proc_cont (j:=k) (u:=h) t c (G:=G) (X:=fun _=>0))
  have H := continuous_finsetSum Finset.univ fun c _=> (HA c).mul (HB c)
  obtain ⟨C,hC⟩ := cube_compact.exists_bound_of_continuousOn H.continuousOn; exact delta_integrable.mul_bdd H.aestronglyMeasurable ((ae_restrict_mem cube_compact.measurableSet).mono hC)

def baseDensity (s t : Signed) (q : E4) (j k : ℕ) (h : ℝ) : Biform (Pad G j) (Pad G k) := (delta q)⁻¹ • ∑ c : Channel G,
  under (LinearMap.mul ℝ ℝ) (LinearMap.applyₗ (chart j s h 0 (material c q))) (LinearMap.applyₗ (chart k t h 0 (material c q)))
lemma density_eq (s t j k h q) (A: Pad G j) (B : Pad G k) : baseDensity s t q j k h A B = coverPair j k s t h q A B := by simp [baseDensity,coverPair,under_at]
lemma density_good (s t j k h) (A : Pad G j) (B : Pad G k) : IntegrableOn (fun q=>baseDensity s t q j k h A B) cube := by simp only [density_eq];apply cont_cost

def integralForm (j k : ℕ) (s t : Signed) (h : ℝ) : Biform (Pad G j) (Pad G k) where
  toFun A := { toFun := fun B => ∫ q in cube, baseDensity s t q j k h A B
               map_add' x y := by simp only [map_add, integral_add (density_good _ _ _ _ _ _ x) (density_good _ _ _ _ _ _ y)]
               map_smul' a x := by simp only [map_smul, integral_smul, RingHom.id_apply] }
  map_add' x y := by apply LinearMap.ext; intro b; change (∫ q in cube, baseDensity s t q j k h (x+y) b) = _ + (_ : ℝ); simp only [map_add,LinearMap.add_apply, integral_add (density_good _ _ _ _ _ x b) (density_good _ _ _ _ _ y b)]; rfl
  map_smul' a x := by apply LinearMap.ext; intro b; change (∫ q in cube, baseDensity s t q j k h (a • x) b) = a • (_:ℝ); simp only [map_smul,LinearMap.smul_apply, integral_smul, RingHom.id_apply]; rfl
def sphereForm (j k : ℕ) (s t : Signed) (h:ℝ) : Biform (Pad G j) (Pad G k) := volumeFactor • integralForm j k s t h
lemma sph_eq j k s t h (A : Pad G j) (B : Pad G k) : sphereForm j k s t h A B = volumeFactor * ∫ q in cube, coverPair j k s t h q A B := by
  change (volumeFactor * (integralForm _ _ _ _ _ A B)) = _; simp_rw [←density_eq];rfl
lemma sph_spot (s t : Signed) (v : Spot G j) (u : Spot G k) (h : ℝ) : sphereForm j k s t h v.meter u.meter = fluxPrice (v.atom s) (u.atom t) h (unitColor G v.color) (unitColor G u.color) := by
  rw [sph_eq,Spot.meter_atom v s, Spot.meter_atom u t]
  exact fx_bill _ _ _ _ _

section
variable (T : Itinerary) (x y : StepPath T) (s t : Signed)

lemma chart_limit (z : E4) (hz : z≠0) (hx : Scene T x y z) (hi : Finale T x y z) (P : Pad G j) (Q : Pad G k):
    Tendsto (fun m=> ordinary j k s t (T.gap m) (x m) (y m) P Q) atTop (𝓝 (synthesis z hz s t P Q)) := by
  let cur (m:ℕ) : Biform (Pad G j) (Pad G k) := ordinary j k s t (T.gap m) (x m) (y m)
  let dest : Biform (Pad G j) (Pad G k):=synthesis z hz s t
  have he (v : Spot G j) (u : Spot G k) : Tendsto (fun m => cur m v.meter u.meter) atTop (𝓝 (dest v.meter u.meter)) := by
    dsimp only [cur,dest]; simp_rw [synthesis_spot,o_spot]; exact flux_limit (v.atom s) (u.atom t) _ _ _ _ _ hz hx hi
  have hh (v : Spot G j) (u : Spot G k) := (he v u).sub (tendsto_const_nhds (x:=dest v.meter u.meter))
  have H := (surge (G:=G) cur (fun _=>dest) (show _ from by simpa only [sub_self] using! hh) P Q).add (tendsto_const_nhds (x:=dest P Q))
  simp only [zero_add,sub_add_cancel] at H; exact H

lemma chart_return (z : E4) (hi : Finale T x x z) (P : Pad G j) (Q : Pad G k):
    Tendsto (fun m=> ordinary j k s t (T.gap m) (x m) (x m) P Q - sphereForm j k s t (T.gap m) P Q) atTop (𝓝 0) := by
  let cur (m:ℕ) : Biform (Pad G j) (Pad G k):= ordinary j k s t (T.gap m) (x m) (x m)
  let dest (m:ℕ) : Biform (Pad G j) (Pad G k) := sphereForm j k s t (T.gap m)
  apply surge (G:=G) cur dest;intro v u; dsimp only [cur,dest]; simp only [o_spot,sph_spot]; exact flux_return (z:=z) (v.atom s) (u.atom t) _ _ _ _ hi
end
end YM.Pert.Align
