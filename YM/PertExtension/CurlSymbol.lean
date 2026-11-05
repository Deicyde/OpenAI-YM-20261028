import YM.PertExtension.HeatProjection
import YM.RG.PathActions

/-! The full-cover *top* Wilson covariance on horizontal plaquette functionals
in physical color metric. This $I/\Delta$ covariance defines the top Wick map.
The joint integral itself instead uses the inversion regulator's no-zero-mode
quadratic kernel, not two independent infinite-volume covariances. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.LatticePT
open Function Set Filter RG Wilson Lattice MeasureTheory Metric
open scoped Topology Classical BigOperators
open Next.Rank.Normal
variable {G : Gauge}

abbrev Momentum := Four ℝ

def increment (j : Axis)(p : Momentum):=Complex.exp (Complex.I*(p j:ℂ))-1
def mass (p : Momentum) := ∑ i:Axis, ‖increment i p‖^2
def phase (s:RG.Slot)(p:Momentum) := Complex.exp (Complex.ofReal (∑ i, (s.offset i:ℝ)*p i) * Complex.I)
def impulse (s : RG.Slot)(i)(p) := (if i=s.plaq.val.2 then increment s.plaq.val.1 p else 0) - if i=s.plaq.val.1 then increment s.plaq.val.2 p else 0
def bubble (s t : RG.Slot) (p : Momentum) : ℝ := (∑ i, ((phase s p * star (phase t p))*(impulse s i p * star (impulse t i p))).re)/mass p
def cube : Set Momentum:= Set.pi Set.univ fun _=> Icc (-Real.pi) Real.pi
def kernelEntry (s t : RG.Slot): ℝ := (∫ p in cube, bubble s t p)/(2*Real.pi)^4

lemma phase_norm s p : ‖phase s p‖=1:=by unfold phase;rw [Complex.norm_exp];simp
@[fun_prop] lemma phase_cont s :Continuous (phase s) := by unfold phase;fun_prop
@[fun_prop] lemma incr_cont j:Continuous (increment j):=by unfold increment;fun_prop
@[fun_prop] lemma impulse_cont s i : Continuous (impulse s i) := by unfold impulse;split <;> split <;> first | exact continuous_const | fun_prop
@[fun_prop] lemma mass_cont : Continuous mass:=by unfold mass;fun_prop
@[fun_prop] lemma bubble_meas s t : Measurable (bubble s t) := by unfold bubble; apply Measurable.div _ mass_cont.measurable; refine (continuous_finsetSum _ (fun i h=>?_)).measurable; exact Complex.continuous_re.comp ((phase_cont s |>.mul (phase_cont t).star) |>.mul ((impulse_cont s i).mul (impulse_cont t i).star))
lemma mass_nonneg p : 0≤mass p:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
private lemma impulse_bound s i p : ‖impulse s i p‖^2≤ 4*mass p := by
  let u:= fun j=>‖increment j p‖
  have he j : u j^2 ≤ mass p:= Finset.single_le_sum (fun _ _=>sq_nonneg _) (Finset.mem_univ j)
  have hs := norm_sub_le (if i=s.plaq.val.2 then increment s.plaq.val.1 p else 0) (if i=s.plaq.val.1 then increment s.plaq.val.2 p else 0)
  change ‖impulse s i p‖ ≤_ at hs
  split at hs
  · split at hs
    · have hx : ‖impulse s i p‖^2 ≤ (u s.plaq.val.1+u s.plaq.val.2)^2:=by gcongr
      nlinarith [sq_nonneg (u s.plaq.val.1-u s.plaq.val.2),he s.plaq.val.1,he s.plaq.val.2]
    · simp only [norm_zero,add_zero] at hs
      have hx : ‖impulse s i p‖^2 ≤ (u s.plaq.val.1)^2:=by gcongr
      nlinarith [he s.plaq.val.1]
  split at hs
  · rw [norm_zero,zero_add] at hs
    have hx : ‖impulse s i p‖^2 ≤ (u s.plaq.val.2)^2:=by gcongr
    nlinarith [he s.plaq.val.2]
  simp at hs; rw [hs,norm_zero,zero_pow (by decide : 2≠0)]; have := mass_nonneg p;linarith

lemma bubble_bound (s t : RG.Slot)(p) : ‖bubble s t p‖ ≤ 16:= by
  unfold bubble;rw [Real.norm_eq_abs,abs_div]
  by_cases h : mass p=0
  · simp [h]
  have hm:=lt_of_le_of_ne (mass_nonneg p) (Ne.symm h)
  rw [abs_of_pos hm];apply (div_le_iff₀ hm).mpr
  refine (Finset.abs_sum_le_sum_abs ..).trans <| (Finset.sum_le_sum (g:=fun _=>4*mass p) (fun i hi=>?_)).trans_eq (by simp;ring)
  apply (Complex.abs_re_le_norm _).trans
  simp only [norm_mul,norm_star,phase_norm,one_mul]
  nlinarith [sq_nonneg (‖impulse s i p‖-‖impulse t i p‖),impulse_bound s i p, impulse_bound t i p]
lemma bubble_finite s t : IntegrableOn (bubble s t) cube := by
  have h : IsCompact cube := isCompact_univ_pi fun _=>isCompact_Icc
  exact (integrableOn_const (μ:=volume) h.measure_lt_top.ne).mono' (bubble_meas s t |>.aestronglyMeasurable) (Eventually.of_forall (bubble_bound s t))

lemma bubble_symm s t p : bubble s t p=bubble t s p:= by
  unfold bubble
  refine congr_arg (fun x=>x/mass p) (Finset.sum_congr rfl fun i hi=> ?_)
  let a:= phase s p * impulse s i p; let b:=phase t p * impulse t i p
  have h (a b : ℂ) : (a*star b).re=(b*star a).re:= by simp [Complex.mul_re,Complex.star_def];ring
  convert h a b using 2
  · unfold a b;rw [star_mul];ring
  · unfold a b;rw [star_mul];ring

lemma kernel_symm s t : kernelEntry s t=kernelEntry t s:=by unfold kernelEntry;simp_rw [bubble_symm s t]

def covarianceSymbol (G : Gauge) : Next.Rank.Normal.Symmetric (RG.Slot × G.ColorIndex):=⟨fun i j=>if i.2=j.2 then (kernelEntry i.1 j.1:ℂ) else 0,fun i j=>by
  by_cases h:i.2=j.2
  · simp only [h,if_pos rfl];rw [kernel_symm]
  · simp only [if_neg h,if_neg (Ne.symm h)]⟩
end YM.PertExtension.LatticePT
