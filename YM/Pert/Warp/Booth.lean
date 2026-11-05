import YM.Pert.Warp.Exchange
import Mathlib.MeasureTheory.Integral.Pi
/-! Independent private marks as genuine finite Gaussian jet carriers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Pert.Warp
open MeasureTheory ProbabilityTheory Function
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
 {n : ℕ}

def punch (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : E × (Fin n → E) →L[ℝ] (Fin (n+1) → E) := {
   toFun x := Fin.cons x.1 x.2
   map_add' x y := by funext i; cases i using Fin.cases <;> simp
   map_smul' r x := by funext i; cases i using Fin.cases <;> simp
   cont := by fun_prop -- check
}
lemma punch_eq (n : ℕ) : (fun x=>punch E n x) = ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>E) 0).symm) := by
  funext x j; unfold punch; simp only [ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]; cases j using Fin.cases <;> simp
lemma pi_gaussian (n : ℕ) (μ : Measure E) [hG : IsGaussian μ] : IsGaussian (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero => exact IsGaussian.of_subsingleton
  | succ n h =>
      let ν := Measure.pi (fun _ : Fin n => μ)
      have hi : MeasurePreserving (fun x => punch E n x) (μ.prod ν) (Measure.pi (fun _ : Fin (n+1)=>μ)) := (punch_eq (E:=E) n).symm ▸ MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>E) 0) (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1)=>μ) (0 : Fin (n+1))) -- signature
      letI : IsGaussian ν := h
      haveI : IsGaussian (μ.prod ν) := inferInstance
      exact hi.map_eq ▸ ((isGaussian_map_of_measurable (by fun_prop : Measurable (punch E n))):IsGaussian ((μ.prod ν).map (punch E n)))

variable (μ : Measure E) (ν : Measure F) [IsGaussian μ] [IsGaussian ν]
def mixed (n : ℕ) := μ.prod (Measure.pi (fun _ : Fin n=>ν))
lemma mix_gaussian (n) : IsGaussian (mixed μ ν n) := by haveI := pi_gaussian n ν; unfold mixed; infer_instance
lemma mix_pair {K : Type*} [RCLike K] (n : ℕ) (A : E→K) (p : Fin n → F→K) :
    (∫ z : E×(Fin n →F), A z.1 * (∏ i,p i (z.2 i)) ∂mixed μ ν n) = (∫x,A x ∂μ) * ∏ i,(∫ y,p i y ∂ν) := by unfold mixed; rw [integral_prod_mul A (fun z : Fin n→F => ∏ i,p i (z i)),integral_fintype_prod_eq_prod]

abbrev Hall (n:ℕ) (E F) := E × (Fin n→F)
variable (E) in
def lead (j : Fin n) (g : F→L[ℝ] ℝ) : Hall n E F →L[ℝ] ℝ := (g.comp (ContinuousLinearMap.proj j)).comp (ContinuousLinearMap.snd ..)
variable (n F) in
def chain (f : E →L[ℝ] ℝ) : Hall n E F →L[ℝ] ℝ := f.comp (ContinuousLinearMap.fst ..)
variable (E F) in
def floating (i : Fin n) (f:E→L[ℝ] ℝ) (g:F→L[ℝ] ℝ) : Hall n E F →L[ℝ] ℂ := Complex.ofRealCLM.comp (chain F n f) + Complex.I • Complex.ofRealCLM.comp (lead E i g)
variable (E F) in
def flight (i : Fin n) (f : E→L[ℝ] ℝ) (g : F→L[ℝ] ℝ) : (Hall n E F) → ℂ := fun x=> ↑(f x.1) + Complex.I * ↑(g (x.2 i))
lemma floating_eq (i : Fin n) (f : E→L[ℝ] ℝ) (g : F→L[ℝ] ℝ) (x : Hall n E F): floating E F i f g x = flight E F i f g x := rfl
lemma mix_leg (i : Fin n) (g : F→ℝ) (a : E→ℝ) : ∫ z : Hall n E F,a z.1 * g (z.2 i) ∂mixed μ ν n = (∫ x,a x ∂μ) * ∫ y,g y ∂ν := by
  have he : ∀ (x:Fin n) (p q : F→ℝ), (∫ y,(if x=i then p y else q y) ∂ν) = if x=i then ∫ y,p y ∂ν else ∫ y,q y ∂ν := by intros; split <;> simp only [*]
  simpa only [he,integral_const,probReal_univ,smul_eq_mul,one_mul,Finset.prod_ite_eq',Finset.mem_univ,↓reduceIte] using mix_pair μ ν n a (fun x y=> if x=i then g y else 1)
lemma float_int (i : Fin n) {f : E→L[ℝ] ℝ} {g : F→L[ℝ] ℝ} (hf : ∫ x,f x ∂μ=0) (hg : ∫ y,g y ∂ν=0) : (∫ z,floating E F i f g z ∂mixed μ ν n)=0 := by
  let M := mixed μ ν n; haveI hI : IsGaussian M := mix_gaussian _ _ _
  have hlead : (∫z : Hall n E F, g (z.2 i) ∂M) = ∫ x,g x ∂ν := by simpa only [one_mul,integral_const,probReal_univ,smul_eq_mul,M] using mix_leg μ ν i (fun x=>g x) (fun _=>1)
  have hchain : (∫ z : Hall n E F, f z.1 ∂M) = ∫ x,f x ∂μ := by simpa using mix_pair μ ν n (fun x=> f x) (fun _ _=> (1:ℝ))
  change (∫ z,Complex.ofRealCLM (chain F n f z) + Complex.I * (Complex.ofRealCLM.comp (lead E i g)) z ∂M)=0
  erw [integral_add (price_tame M (Orb.Tame.clm (Complex.ofRealCLM.comp (chain F n f)))) (((price_tame M (Orb.Tame.clm (Complex.ofRealCLM.comp (lead E i g))))).const_mul _), integral_const_mul, integral_complex_ofReal]; erw [integral_complex_ofReal] -- possible rewriting all
  erw [show (∫ z,chain F n f z ∂M)=0 from hchain.trans hf,show (∫ z,lead E i g z ∂M)=0 from hlead.trans hg]; simp
lemma float_prod (i j : Fin n) {f1 f2 : E→L[ℝ] ℝ} {g1 g2 : F→L[ℝ] ℝ} (hg1 : ∫ y,g1 y ∂ν=0) (hg2 : ∫ y,g2 y ∂ν=0) :
    (∫ z, floating E F i f1 g1 z * floating E F j f2 g2 z ∂mixed μ ν n) = (↑(∫ x,f1 x * f2 x ∂μ) : ℂ) - ↑(if i=j then ∫ y,g1 y * g2 y ∂ν else (0:ℝ)) := by
  let M := mixed μ ν n; haveI hI : IsGaussian M := mix_gaussian _ _ _
  have ht (f : Hall n E F→L[ℝ] ℝ) := Orb.Tame.clm f
  let X:=chain F n f1
  let Y:=chain F n f2
  let S:=lead E i g1
  let T:=lead E j g2
  have ep : (fun z=>floating E F i f1 g1 z * floating E F j f2 g2 z) = fun (z : Hall n E F)=> (↑(X z*Y z) + (↑(X z*T z)+ ↑(Y z*S z))*Complex.I) - ↑(S z*T z) := by
    simp_rw [floating_eq]; funext z;unfold flight; have e : Complex.I * Complex.I = -(1:ℂ) := Complex.I_mul_I;push_cast
    change (X z+Complex.I*S z)*((Y z:ℂ)+Complex.I*T z)=(↑(X z) * ↑(Y z) + ((X z*T z:ℂ)+(Y z*S z : ℂ))*Complex.I)-(S z:ℂ)*T z
    ring_nf; simp [mul_assoc,Complex.I_mul_I,Complex.I_sq];ring
  -- integrate real terms
  have hi (f g : Hall n E F→L[ℝ] ℝ) := price_tame M (((ht f).mul (ht g)).ofReal)
  -- here syntactic. test
  have hf : (∫ z,X z*Y z ∂M)=(∫ x,f1 x * f2 x ∂μ) := by simpa [chain,X,Y,M] using mix_pair μ ν n (fun x=>f1 x * f2 x) (fun _ _ => (1:ℝ))
  have cross (l : Fin n) (f : E→L[ℝ] ℝ) (g : F→L[ℝ] ℝ) (hg : ∫ x,g x ∂ν=0) : ∫ z : Hall n E F,f z.1 * g (z.2 l) ∂M=0 := by simpa only [hg,mul_zero,M] using mix_leg μ ν l g f
  have last : (∫ z : Hall n E F,S z*T z ∂M)= if i=j then ∫ y,g1 y * g2 y ∂ν else (0:ℝ) := by
    change (∫ z : Hall n E F,g1 (z.2 i)*g2 (z.2 j) ∂M) = _
    by_cases h:i=j
    · rw [if_pos h,h]; simpa using mix_leg μ ν j (fun x=>g1 x *g2 x) (fun _=>1)
    rw [if_neg h]
    have e := mix_pair μ ν n (fun _=> (1:ℝ)) (fun a x=>(if a=i then g1 x else 1) * if a=j then g2 x else 1)
    simp only [Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,↓reduceIte, integral_const,probReal_univ,smul_eq_mul,one_mul] at e
    rw [show M= mixed μ ν n from rfl,e]; apply Finset.prod_eq_zero (Finset.mem_univ i);simp [h,hg1]
  -- integrals
  change (∫ z, (fun w=> floating E F i f1 g1 w *floating E F j f2 g2 w) z ∂M) = _
  rw [ep]; erw [MeasureTheory.integral_sub ((hi X Y).add (((hi X T).add (hi Y S)).mul_const _)) (hi S T)] -- possible name collision
  erw [MeasureTheory.integral_add (hi X Y) (((hi X T).add (hi Y S)).mul_const _),integral_mul_const,MeasureTheory.integral_add (hi X T) (hi Y S)]
  erw [integral_complex_ofReal,integral_complex_ofReal,integral_complex_ofReal,integral_complex_ofReal, hf, last,show (∫ z,X z*T z ∂M)=_ from cross j f1 g2 hg2,show (∫ z,Y z*S z ∂M)=_ from cross i f2 g1 hg1]; push_cast; ring
end YM.Pert.Warp
