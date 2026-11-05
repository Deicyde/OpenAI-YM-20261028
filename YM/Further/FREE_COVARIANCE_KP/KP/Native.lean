import YM.Further.FREE_COVARIANCE_KP.KP.Field
import YM.Further.FREE_COVARIANCE_KP.KP.Tile


/-! # kper on all joined endpoint tests, uniform on a stage -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι : Type*} {α Ω η : ℝ} {I : Firm α Ω η}
variable (A B : List Axis)




lemma room_none (f : Firm α Ω η) (i j : X2) : rebus A B f 0 i j = 0 := by unfold rebus record garnet; simp [q_exact,wedge,song]



lemma paving_change (n : Side) (a : Site n) (v : St) : mcast (lit n (pav n (a,v)))=mon a+reciprocal (posi v) := by
  rw [← lit_mon]; ext1 i; unfold mcast pav; rw [cor_axis]; simp [reciprocal]
lemma periodic_record (n : Side) (f: Firm α Ω η) (a : Site n) (v : St) : record A B f (lit n (pav n (a,v)))=record A B f (lit n (lift a)) := by
  have he p i : song (rcast (step i)) p=exp (Complex.I*mcast p i) := by rw [← cast_mode, factor]
  have hb : tooth (lit n (pav n (a,v)))=tooth (lit n (lift a)) := by
    ext1 i; unfold tooth q; rw [paving_change,lit_mon,← factor,← factor,mode_phase,mode_periodic,mul_one]
  unfold record garnet fuel bill; rw [hb,paving_change,lit_mon,Row.periods]

/-- lag kernel. Cover lifts arbitrary. -/
def meter (n : Side) := ((n.val:ℂ)^4)⁻¹
def transmits (n : Side) (f : Firm α Ω η) (a b : X2) (x:Cover) := meter n * ∑ t : Site n,
    mode (mon t) x * (record A B f (lit n (lift t))) a b
lemma covering (n : Side) (f:Firm α Ω η) (a b:X2) (x:Cover) :
    transmits A B n f a b x=(tally:ℂ) * ((leap n)^4 • (∑ i:Site n × St,song (rcast x) (lit n (pav n i))*rebus A B f (lit n (pav n i)) a b)) := by
  let m (i : Site n) := mode (mon i) x*record A B f (lit n (lift i)) a b
  have he (i : Site n) (v : St) : song (rcast x) (lit n (pav n (i,v)))*rebus A B f (lit n (pav n (i,v))) a b=house (lit n (pav n (i,v)))*m i := by
    unfold m rebus; rw [← cast_mode,paving_change,mode_phase,mode_periodic,mul_one,periodic_record,Matrix.smul_apply,smul_eq_mul]; ring
  rw [Fintype.sum_prod_type]
  simp_rw [he,← Finset.sum_mul, fold_door,one_mul, real_smul]
  rw [← mul_assoc,show (↑tally:ℂ)* (↑((leap n)^4:ℝ):ℂ)= meter n from ?_]
  rfl
  unfold tally height meter leap; have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero; have he := side_ne n; push_cast; field_simp




def slot (d : Axis→(Cover→ℂ)→ Cover→ℂ) : List Axis → (Cover→ ℂ) → Cover→ℂ
  | [],f=> f
  | i::is,f=> slot d is (d i f)

def rock (n : Side) (f: Firm α Ω η) (a b:X2) := transmits [] [] n f a b






end YM.Further.FreeCovariance.KP
