import YM.UVExtension.Pier.Pilot
import YM.Push.LOCAL_SPLITTING.Recovery
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push.Local
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
variable {ι:Type}(B: BudgetPoint) (M:ι→ Wing)
local notation "C"=> Config G n
variable (Q : Rep G n){σ v a r b:ℝ}(h:Q.Lawful σ v a r b)

def salaryP (P:ℕ→ C → ℂ) (U:Config G n):= (Real.exp (Q.exponent U):ℂ)*∑' i, gasMark Q.p Q.activities U i P
variable (f:ι→ Config G n→ℂ)(he:Dominated f)
include he h
lemma charter: Dominated (fun i=>port Q (M i)*f i):=by
    obtain ⟨t,ht,hT⟩:= he; obtain ⟨u,hu⟩:= pricing Q h; have hx : 0 ≤ u:= (norm_nonneg _).trans (hu (Wing.logKey 0) 1)
    exact ⟨_,ht.mul_left u,fun i U=> (norm_mul ..).trans_le (mul_le_mul (hu ..) (hT i U) (norm_nonneg _) hx)⟩
omit he
lemma carded (j:ℕ→ Config G n→ℂ)(he:Dominated j)(U:Config G n):∑' i, port Q (.gasKey i) U*j i U= salaryP Q j U:=by
    have hp i: gasMark Q.p Q.activities U i j= ∑' l, j l U*coat Q l i U:=by
        rw [tsum_eq_sum (s:=i)]
        · rw [gasMark_eq]; split
          next h=> exact Finset.sum_congr rfl fun l hl=> by simp [coat,h,hl]
          next h=> simp [coat,h]
        intro l hl; simp [coat,hl]
    unfold port salaryP; simp_rw [hp,mul_assoc]; rw [tsum_mul_left]
    congr 1; simp_rw [mul_comm (dressed Q _ U),dressed,←tsum_mul_left]
    symm; exact Summable.tsum_comm ((coat_all h he).summable U)

lemma transmute {m:Side}(S: StepData m n)(H:S.IsKernel Q.beta G)(R: Rep G m)(hp:R.eval=S.push Q.beta Q.eval)(F:Config G n→ℂ)(he: Integrable F (prior G n)) : total Q F= total R (S.push Q.beta F):=by
    have ht : (∫ U,R.eval U∂prior G m)= ∫ U,Q.eval U∂prior G n:= hp ▸ StepData.push_integral H Q.eval ((Q.envelope h).integrable _)
    unfold total; rw [S.push_integral H F he]; simp_rw [integral_complex_ofReal]; rw [ht]

omit h
lemma sums {f g:Config G n→ℂ}(hs: Integrable f (prior G n))(ht: Integrable g (prior G n)):total Q (f+g)=total Q f+total Q g:=by unfold total; simp_rw [Pi.add_apply]; rw [integral_add hs ht,mul_add]
lemma scale (f:Config G n→ℂ)(t:ℂ):total Q (t • f)= t * total Q f:=by unfold total; simp_rw [Pi.smul_apply,smul_eq_mul,integral_const_mul]; exact mul_left_comm ..
include h he
variable [Countable ι] (hk:∀ i, Measurable (f i))
include hk
lemma recorded : Envelope (fun U:Config G n=>∑' i,port Q (M i) U * f i U):=by
   have hp(i):= portEnv (M i) Q h; exact ⟨Measurable.tsum fun i=> (hp i).meas.mul (hk i), (charter M Q h f he).bound⟩
lemma stored : HasSum (fun i=> hit Q (M i) (f i)) (total Q (fun U:Config G n=>∑' i,port Q (M i) U * f i U)):=by
   let P i:= port Q (M i)*f i; obtain ⟨u,hu,hU⟩:=charter M Q h f he
   have hx i : Envelope (P i):= ⟨(portEnv (M i) Q h).meas.mul (hk i), u i, hU i⟩
   have h₁ i:= (hx i).integrableC (prior G n); have h₂: Summable (fun i=> ∫ x,‖P i x‖ ∂prior G n):= hu.of_nonneg_of_le (fun i=> integral_nonneg (fun x=> norm_nonneg _)) (fun i=> by simpa using integral_mono ((h₁ i).norm) (integrable_const (u i)) (hU i))
   exact (hasSum_integral_of_summable_integral_norm h₁ h₂).mul_left _

omit [Countable ι] f he hk -- f omitted?
variable (w: Wing) (x:PoleC (G:=G) (n:=n) B w)
lemma complexify (V W:Leaf Q)(he: V.turn=w)(hk:W.turn=w)(hP:∀ U, x.val U=((V.ingredient U:ℂ)+Complex.I * (W.ingredient U:ℂ))): hit Q w x.val= total Q (Complex.ofReal ∘ V.cicada)+ Complex.I * total Q (Complex.ofReal ∘ W.cicada):=by
   let A:= Complex.ofReal ∘ V.cicada; let Z:= Complex.ofReal ∘ W.cicada; have hv: Integrable A (prior G n):= ((V.sells h|>.1.integrable _)).ofReal; have hh: Integrable Z (prior G n):= ((W.sells h|>.1.integrable _)).ofReal; have hx: port Q w*x.val=A+Complex.I • Z:=by
      funext i; change port Q w i*x.val i=_ + Complex.I * _; rw [hP]; have hs: port Q w i*(V.ingredient i:ℂ)=A i:= he ▸ lit Q V i; have ht: port Q w i*(W.ingredient i:ℂ)=Z i:= hk ▸ lit Q W i; rw [mul_add,hs,mul_left_comm _ Complex.I,ht]
   rw [hit,hx,sums Q hv (hh.smul _), scale Q]
end YM.UVExtension.Pier
