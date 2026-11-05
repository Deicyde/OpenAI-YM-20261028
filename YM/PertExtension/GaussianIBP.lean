import YM.PertExtension.GaussianScore

/-! Centered Gaussian monomial and pairing recursion by differentiation of an
actual translate. Applies directly to singular leg covariance from a positive
tangent precision (no inverse needed on the leg index space). -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.PertExtension.GaussianScore
open Series Function Filter Set Metric MeasureTheory
open scoped Topology ContDiff Classical BigOperators
open LinearMap Radial

variable {E I : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
local notation "z" => Radial.zone (E:=E)
local notation "V" => Module.Dual ℝ E

namespace Law
variable (Γ : Law E)
variable {A L : E→ℝ}
variable [MeasurableSpace E][BorelSpace E]

-- Step common to all monomial lengths.
lemma translation_lemma (v : E)(hA : Zone.Invoice z A)(hAc : Continuous A)(hL : Zone.Invoice z L)(hLc : Continuous L)
    (hd : ∀ x t, HasDerivAt (fun r : ℝ => A (x+r•v)) (L (x+t•v)) t)
    (μ : Measure E)[μ.HasTemperateGrowth][μ.IsAddRightInvariant] :
    ∫ x, ((L-A*(Γ.P v))*Γ.kern) x ∂μ=0 := by
  let B:=L-A*(Γ.P v)
  have hB : Continuous B:= hLc.sub (hAc.mul (Γ.P v).continuous_of_finiteDimensional)
  let f (x : E)(t : ℝ):=x+t•v
  let F (a : ℝ)(x) := (A*Γ.kern) (f x a)
  let D (a : ℝ)(x) := (B*Γ.kern) (f x a)
  have hF (a) : Continuous (F a) := (hAc.mul Γ.continuous_kern).comp (continuous_id.add continuous_const)
  have hh (a) : Continuous (D a) := (hB.mul Γ.continuous_kern).comp (continuous_id.add continuous_const)
  have hbi := hL.add ((hA.mul (Law.linearInvoice (Γ.P v))).weaken (b:= -(A*fun x=>Γ.P v x)) (by simp))
  obtain ⟨c,hc,C,hC,k,H⟩:=Γ.translation_bound (A:=B) hbi v
  have h₂ (x : E): ∀ a ∈ ball (0:ℝ) 1, ‖D a x‖ ≤ C*bill k c x := fun a ha=> H x a (by simpa [Real.norm_eq_abs] using (mem_ball_zero_iff.mp ha).le)
  have hI : Integrable (F 0) μ:=by simpa [F,f] using! Γ.integrable_entry μ hA hAc
  have ht (x : E)(a)(ha : a∈ball (0:ℝ) 1) : HasDerivAt (fun t=> F t x) (D a x) a := by
     have hq (t : ℝ) : -(Γ.P (x+t•v)) (x+t•v)/2 = -(Γ.P x x)/2 - Γ.P v x * t - (Γ.P v v)/2 * (t*t) := by
          rw [map_add,map_add, map_smul,map_smul]; simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,map_add,map_smul,Γ.turns x v];ring
     have hi := ((hasDerivAt_id' a).mul (hasDerivAt_id' a))
     have hz: HasDerivAt (fun t : ℝ=> -(Γ.P x x)/2-Γ.P v x*t-(Γ.P v v)/2*(t*t)) _ a :=
          ((hasDerivAt_const a _).sub ((hasDerivAt_id' a).const_mul _)).sub (hi.const_mul _)
     have hw:= (hd x a).mul hz.exp
     dsimp only [F,D,Pi.mul_apply,Pi.sub_apply,B,f,kern]; convert! hw using 1
     · funext t;rw [hq]; rfl
     rw [hq]; simp only [id_eq, map_add,map_smul,smul_eq_mul];ring
  have hi:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=ball (0:ℝ) 1) (F':=D) (ball_mem_nhds _ zero_lt_one) (Eventually.of_forall (fun a=>(hF a).aestronglyMeasurable)) hI ((hh 0).aestronglyMeasurable) (Eventually.of_forall h₂) ((bill_integrable μ _ hc).const_mul C) (Eventually.of_forall ht)
  rw [show (L-A*Γ.P v)*Γ.kern = D 0 from by funext x; unfold D f;rw [zero_smul,add_zero]]
  apply hi.2.unique
  rw [show (fun r:ℝ=>∫ x, F r x ∂μ) = (fun _=>∫ x,(A*Γ.kern) x ∂μ) from funext (fun a=>integral_add_right_eq_self (A*Γ.kern) (a•v))]
  exact hasDerivAt_const ..

-- Product of source evaluations as function of integration variable.
def product (u : I→V)(s : Finset I)(x : E) := ∏ i∈s,u i x
def diffSum [DecidableEq I](u : I→V)(s : Finset I)(v:E)(x : E) := ∑ i∈s,product u (s.erase i) x * u i v

def average (μ : Measure E)(A : E→ℝ) := (∫ x,(A*Γ.kern) x ∂μ) / (∫ x,Γ.kern x ∂μ)

lemma product_bound (ℓ:I→V)(s : Finset I):Zone.Invoice z (product ℓ s) := by
  induction s using Finset.induction_on with
  | empty=>exact by simpa [product] using! (Zone.Invoice.const (1:ℝ))
  | insert a s ha ih=>
      have H : product ℓ (insert a s)= (ℓ a)*(product ℓ s):= by funext x; simp [product,ha]
      rw [H]; exact (Law.linearInvoice (ℓ a)).mul ih
variable [DecidableEq I]
lemma diffSum_bound (ℓ:I→V)(s : Finset I)(v : E):Zone.Invoice z (diffSum ℓ s v) := by
     convert! Zone.Invoice.fin_sum s (fun i=> product ℓ (s.erase i)* fun _=>ℓ i v) ?_ using 1
     · funext x; simp [diffSum,Finset.sum_apply]
     intro i hi;exact (product_bound ℓ _).mul (Zone.Invoice.const _)
lemma diffSum_on (ℓ : I→V)(s : Finset I)(v x : E)(a) : HasDerivAt (fun t : ℝ=> product ℓ s (x+t•v)) (diffSum ℓ s v (x+a•v)) a := by
    exact HasDerivAt.fun_finsetProd (fun i hi=> show HasDerivAt (fun t:ℝ=>ℓ i (x+t•v)) (ℓ i v) a from by
       simp only [map_add,map_smul,smul_eq_mul]; simpa only [one_mul] using! (((hasDerivAt_id' a).mul_const (ℓ i v)).const_add ..))
lemma product_cont (ℓ : I→V)(s : Finset I):Continuous (product ℓ s) := continuous_finsetProd _ (fun i _=>(ℓ i).continuous_of_finiteDimensional)
lemma diffSum_cont (ℓ:I→V)(s : Finset I)(v : E) : Continuous (diffSum ℓ s v):= continuous_finsetSum s (fun i _=>(product_cont ..).mul continuous_const)

theorem recursion (μ : Measure E)[μ.HasTemperateGrowth][μ.IsAddRightInvariant]
    (ℓ₀ : V)(ℓ : I→V)(s : Finset I) :
    Γ.average μ (fun x=> product ℓ s x *ℓ₀ x)= ∑ i∈s, (Γ.average μ (product ℓ (s.erase i)))*Γ.wick ℓ₀ (ℓ i) := by
  classical
  let v:=Γ.inverse ℓ₀
  have ht:= Γ.translation_lemma v (product_bound ℓ s) (product_cont ..) (diffSum_bound ℓ s v) (diffSum_cont ..) (diffSum_on ℓ s v) μ
  let Q:=product ℓ s * fun x=>Γ.P v x
  have hs : Integrable (Q*Γ.kern) μ := Γ.integrable_entry μ ((product_bound ℓ _).mul (linearInvoice _)) ((product_cont ..).mul ((Γ.P v).continuous_of_finiteDimensional))
  have he : Integrable ((diffSum ℓ s v)*Γ.kern) μ := Γ.integrable_entry μ (diffSum_bound ..) (diffSum_cont ..)
  have hb : ∫ x, diffSum ℓ s v x * Γ.kern x ∂μ = ∫ x,product ℓ s x* ℓ₀ x * Γ.kern x ∂μ := by
     have hq : ∫ x, diffSum ℓ s v x * Γ.kern x-Q x*Γ.kern x ∂μ=0:= by
        simp_rw [Pi.mul_apply,Pi.sub_apply,sub_mul] at ht;exact ht
     have hki:=integral_sub (μ:=μ) he hs; change ∫ a,diffSum ℓ s v a *Γ.kern a-Q a * Γ.kern a ∂μ = (∫ a,diffSum ℓ s v a *Γ.kern a ∂μ) - ∫ a,Q a*Γ.kern a ∂μ at hki
     have h:= sub_eq_zero.mp (hki.symm.trans hq)
     refine h.trans (by unfold Q;simp [v,Γ.applies])
  unfold average
  let G i : E→ℝ := fun x=> product ℓ (s.erase i) x * Γ.kern x *Γ.wick ℓ₀ (ℓ i)
  simp only [Pi.mul_apply];rw [←hb,show ∫ x,diffSum ℓ s v x*Γ.kern x ∂μ = ∑ i∈s,∫ x,G i x ∂μ from ?_, Finset.sum_div]
  · apply Finset.sum_congr rfl fun i _ => ?_;unfold G; rw [MeasureTheory.integral_mul_const];ring
  have hG i : Integrable (G i) μ:= (Γ.integrable_entry μ (product_bound ℓ _) (product_cont ..)).mul_const _
  calc
    _ = ∫ x, (∑ i∈s,G i x) ∂μ := by refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); unfold diffSum; dsimp only;rw [Finset.sum_mul];exact Finset.sum_congr rfl (fun i _=>by unfold G v wick;ring)
    _ = _ := integral_finsetSum _ (fun i _=>hG i)

lemma empty (μ : Measure E)[μ.HasTemperateGrowth][NeZero μ] : Γ.average μ 1=1 := by
  unfold average;rw [one_mul, div_self ?_]
  have hi := Γ.integrable_entry (A:=1) μ (Zone.Invoice.const (1:ℝ)) continuous_const
  rw [one_mul] at hi
  exact (integral_exp_pos hi).ne'

end Law
end YM.PertExtension.GaussianScore
