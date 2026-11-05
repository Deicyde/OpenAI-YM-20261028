import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Carillon
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix

/-! Density normalization score & joint C^k for the centered unforced E
expectation. No held-coordinate displacement. Uses Jacobi slope and exact
normalized kernel exchange (no exponent derivative assumed through this
step). Keep two parts of the Band: value exactly one on THIS reference law,
speed has a period-independent part and all dimension/reanchoring terms
come with t before further moment payments. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
open AnalyticBridge.LocalGaussianLaws
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c : Side} {V : Config G c} {P : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {o : Site c}
    {K Z t : ℝ} {n R : ℕ} {J : Config G c → Matrix ι ι ℝ}
namespace Carillon
variable (J) (V)
def vary (z : Gaussian.Vec ι) (W : Config G c) := Density.replace (J W) (J V) 0 z
def value (z : Gaussian.Vec ι) (W : Config G c) := (Real.log (J V).det - Real.log (J W).det)/2 +
    (Gaussian.force (J V) z - Gaussian.force (J W) z)/2
variable {J V}
lemma vary_exp {W} (hw : (J W).PosDef) (hv : (J V).PosDef) (z : Gaussian.Vec ι) : vary V J z W = Real.exp (value V J z W) := by
  rw [vary,Density.replace,Density.chip_income _ _ hw hv,← Real.exp_add,Real.log_div hv.det_pos.ne' hw.det_pos.ne']; unfold value AnalyticBridge.LocalGaussianLaws.Density.spice; rw [add_zero]; congr 1; ring

variable (h : Carillon J V n P o K Z t R) (ht : 0 ≤ t) (ht' : t ≤ 1) (hZ : 1 ≤ Z) (z : Gaussian.Vec ι)
include h
lemma pos : (J V).PosDef := h.near.self_of_nhds
lemma home : vary V J z V=1 := by simp [vary_exp h.pos h.pos,value]
lemma joint : ContDiffAt ℝ n (fun z : Directions G c × Gaussian.Vec ι => vary V J z.2 (increment V z.1)) (0,z) := by
  let A := J V
  have hh := ((show Continuous (fun p : Directions G c × Gaussian.Vec ι => increment V p.1) by unfold increment; fun_prop).tendsto (0,z))
  rw [Work.G07.at_zero_increment] at hh
  have hf : ContDiffAt ℝ n (fun p : Directions G c × Gaussian.Vec ι => value V J p.2 (increment V p.1)) (0,z) := by
    have hdet := Normalizer.det_smooth (A:=J) (k:=n) (fun i j => (h.cov i j).read)
    have hforce {A : Config G c → Matrix ι ι ℝ} (h : ∀ i j, ContDiffAt ℝ n (fun y : Directions G c => (A (increment V y))⁻¹ i j) 0) :
        ContDiffAt ℝ n (fun p : Directions G c × Gaussian.Vec ι => Gaussian.force (A (increment V p.1)) p.2) (0,z) := by
      unfold Gaussian.force mulVec dotProduct; exact ContDiffAt.sum (fun i _ => ContDiffAt.mul (by fun_prop) (ContDiffAt.sum fun j _ => ((h i j).comp (f:=Prod.fst (β:=Gaussian.Vec ι)) (0,z) contDiffAt_fst).mul (by fun_prop)))
    refine ((contDiffAt_const.sub (((show ContDiffAt ℝ (↑n) ((fun W => Real.log (J W).det) ∘ increment V) 0 from hdet.germ.log (by simpa [Work.G07.at_zero_increment] using h.pos.det_pos.ne')).comp (0,z) contDiffAt_fst))).div_const 2).add
      (((hforce (A:=fun _ => A) (fun _ _ => contDiffAt_const)).sub (hforce (A:=J) (fun i j => (crest_cast.mp (h.inv i j).read).germ))).div_const 2)
  refine hf.exp.congr_of_eventuallyEq ((hh.eventually h.near).mono fun y hy => vary_exp hy h.pos y.2)
omit h [DecidableEq ι] in
private lemma norm_entry (i j : ι) (z : Gaussian.Vec ι) : ‖((z i*z j:ℝ):ℂ)‖ ≤ ‖z‖^2 := by
  rw [Complex.norm_real, norm_mul,sq]; exact mul_le_mul (norm_le_pi_norm ..) (norm_le_pi_norm ..) (norm_nonneg _) (norm_nonneg _)
include ht hZ
lemma force_slope : Slope n (P.dirBound o) V 2 ((Fintype.card ι:ℝ)^2* ‖z‖^2 * (t * canopy Z R P.power n)) (fun W => (Gaussian.force (J W) z:ℂ)) := by
  let A := t*canopy Z R P.power n; have ha : 0≤A := mul_nonneg ht (zero_le_one.trans (canopy_one hZ R ..))
  let M : ℝ := ‖z‖^2 * A
  let f i j := ((z i*z j:ℝ):ℂ) • Normalizer.entry (fun W => (J W)⁻¹) i j
  have hv i j : Slope n (P.dirBound o) V 2 M (f i j) := ((h.inv i j).scale ((z i*z j:ℝ):ℂ)).rise one_le_two (mul_le_mul_of_nonneg_right (norm_entry ..) ha)
  convert! (Slope.scheduled _ zero_le_two (s:=Finset.univ) (fun i _ => Slope.scheduled _ zero_le_two (s:=Finset.univ) (fun j _ => hv i j))) using 1
  · simp [M,A]; ring
  funext W; simp [Gaussian.force,mulVec,dotProduct,f,Normalizer.entry,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

def pitch (n : ℕ) (ι : Type) [Fintype ι] (Z : ℝ) (R b : ℕ) (z : Gaussian.Vec ι) := (Fintype.card ι:ℝ)^2 * (canopy Z R b n + ‖z‖^2) * canopy Z R b n
include ht'
lemma log_slope : Slope n (P.dirBound o) V 2 (t*pitch n ι Z R P.power z) (fun W => (value V J z W:ℂ)) := by
  let A:=canopy Z R P.power n; have hA : 1≤A := canopy_one hZ ..
  have hi i j := (h.inv i j).band (h.val i j) (mul_le_of_le_one_left (zero_le_one.trans hA) ht')
  have hx := Normalizer.slope (r:=1) zero_le_one (zero_le_one.trans hA) (mul_nonneg ht (zero_le_one.trans hA)) h.cov hi (IsUnit.mk0 _ h.pos.det_pos.ne')
  rw [mul_one 2] at hx
  have hc (a : ℂ) := Slope.fixed (n:=c) (D:=P.dirBound o) (U:=V) n a (r:=2) zero_le_two
  let m := Fintype.card ι
  let f W := (Real.log (J W).det:ℂ) + (Gaussian.force (J W) z:ℂ)
  have hh := (((hc (f V)).minus (hx.plus (h.force_slope ht hZ z))).scale (1/2:ℂ))
  rw [norm_div,norm_one, Complex.norm_two] at hh
  have HE : (fun W => (value V J z W:ℂ)) = (1/2:ℂ) • ((fun (_ : Config G c) => f V)-((fun W => (Real.log (J W).det:ℂ)) + (fun W => (Gaussian.force (J W) z:ℂ)))) := by
    ext1; simp [value,f]; ring
  rw [HE]; apply hh.rise le_rfl
  unfold pitch; change (1/2:ℝ)*(0+((m:ℝ)^2*A*(t*A)+(m:ℝ)^2*‖z‖^2*(t*A))) ≤ _
  calc
    _ ≤ 0+((m:ℝ)^2*A*(t*A)+(m:ℝ)^2*‖z‖^2*(t*A)) := mul_le_of_le_one_left (by positivity) (by norm_num)
    _ = _ := by unfold A m; ring

def speed (n : ℕ) (Z t : ℝ) (b R : ℕ) (z : Gaussian.Vec ι) := n*(1+t*pitch n ι Z R b z)*2
lemma sing : Band n (P.dirBound o) V (speed n Z t P.power R z) 1 (fun W => (vary V J z W:ℂ)) := by
  have hh := (h.log_slope ht ht' hZ z).exp_band
  simp only [show value V J z V = 0 by simp [value], Complex.ofReal_zero,Complex.exp_zero,norm_one] at hh
  exact band_move hh (h.near.mono (fun W hW => by dsimp only; rw [vary_exp hW h.pos,Complex.ofReal_exp]))
end Carillon
end YM.PhysicalNext.JointLoad.Heir
