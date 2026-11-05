import YM.PertExtension.Tails

/-! Gaussian rescaling estimate, making no uniformity assertion between different saddles. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Radial
open Filter Set Metric MeasureTheory Asymptotics
open scoped BigOperators Topology Real ContDiff Classical
open Zone
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "Z" => Radial.zone (E:=E)

def disc (t r : ℝ) : Set E:= (fun u : E=>t • u) ⁻¹' Metric.ball 0 r
lemma disc_meas (t r:ℝ): MeasurableSet (disc (E:=E) t r):=by unfold disc;apply MeasurableSet.preimage isOpen_ball.measurableSet;fun_prop
lemma disc_mem {t}(ht : 0≤t)(r : ℝ)(u : E) : u∈disc t r ↔ t*‖u‖<r:=by simp [disc,norm_smul,abs_of_nonneg ht]

variable (μ : Measure E) [μ.HasTemperateGrowth]

private lemma scaledBound {s : Set E}{g : E→ℝ}{c A : ℝ}{k : ℕ}(hc : 0<c)(hA : 0≤A)
    (h : ∀ᵐ x ∂μ.restrict s, ‖g x‖≤A*bill k c x) :
    IntegrableOn (fun x=>A*bill k c x) s μ ∧ ‖∫ x in s,g x ∂μ‖≤(∫ x,bill k c x ∂μ)*A := by
  have hi : Integrable (fun x=>A*bill k c x) μ := (bill_integrable μ k hc).const_mul _
  refine ⟨hi.integrableOn,(norm_integral_le_of_norm_le hi.integrableOn h).trans ?_⟩
  exact (setIntegral_le_integral hi (Eventually.of_forall fun x=>mul_nonneg hA (bill_nonneg ..))).trans_eq <| by rw [integral_const_mul,mul_comm]

def projection (K f : E→ℝ)(t:ℝ)(u : E):=insertion f K t u * kernel f u
def partialSum (K f : E→ℝ)(r t : ℝ) := ∫ u in disc t r,projection K f t u ∂μ

lemma projection_eq (K f : E→ℝ)(t:ℝ)(u) : projection K f t u = K (t • u)*Real.exp (-f (t • u)/t^2) := by
  unfold projection insertion kernel higher;rw [mul_assoc,← Real.exp_add]; congr 2 <;> ring
lemma projection_meas {K f : E→ℝ}(hK : Measurable K)(hf : Measurable f)(t:ℝ) : Measurable (projection K f t) := by
  change Measurable fun u=>projection K f t u
  simp_rw [projection_eq];fun_prop (disch:=exact measurable_id)

namespace Stationary
variable {K f : E→ℝ}(F : Stationary f)(hf : ContDiffAt ℝ ∞ K 0)
include μ F hf

protected lemma integrable_poly (n)(H : ∃ c>0,∀ u : E,c*‖u‖^2≤jet f 2 u)(t : ℝ) : Integrable (poly K f n t) μ := by
  have he(u) : poly K f n t u=∑ i∈Finset.range (n+1),t^i*normTerm K f i u:= by unfold poly Zone.eval normTerm;rw [Finset.sum_mul];simp [mul_assoc]
  change Integrable (fun x=>poly K f n t x) μ
  simp_rw [he]; exact integrable_finsetSum _ fun i _=>(F.integrableTerm μ hf H).const_mul _

protected lemma outside (H : ∃ c>0,∀ u : E,c*‖u‖^2≤jet f 2 u)(n N : ℕ){r : ℝ} (hr : 0<r) :
    ∃ C, ∀ t∈Ioc (0:ℝ) 1,‖∫ u in (disc t r)ᶜ, poly K f n t u ∂μ‖ ≤ C*t^N := by
  obtain ⟨c,hc,h⟩:=H
  obtain ⟨C,k,hC,hd⟩:= F.coeffBound hf n
  let B := C*(r⁻¹)^N
  have hB : 0≤B:=by dsimp [B];positivity
  refine ⟨(∫ u:E,bill (k+N) c u ∂μ)*B,fun t ht=> ?_⟩
  refine ((scaledBound μ hc (mul_nonneg hB (pow_nonneg ht.1.le _)) (h:=?_) (k:=k+N)).2).trans_eq (mul_assoc ..).symm
  filter_upwards [ae_restrict_mem (disc_meas (E:=E) t r).compl] with u (hu : u∈(disc t r)ᶜ)
  have hm : r≤t*‖u‖ := not_lt.mp (hu ∘ (disc_mem ht.1.le r u).2)
  let w:= (Z).w u; have hh : 0<w:= lt_of_lt_of_le zero_lt_one ((Z).high ..);have hw : 1≤w:= (Z).high ..
  have hw' : t*w*(r⁻¹)≥1 := by apply (le_mul_inv_iff₀ hr).mpr;dsimp [w,Radial.zone];grind
  have ht0 : kernel f u≤Real.exp (-c*‖u‖^2) := by unfold kernel;gcongr;have := h u;linarith
  unfold poly;rw [norm_mul,Real.norm_eq_abs (kernel ..),abs_of_nonneg kernel_pos.le]
  have HH := Real.exp_pos (-c*‖u‖^2)
  calc
     _ ≤ C*w^k*Real.exp (-c*‖u‖^2) := mul_le_mul (hd _ _ ht.1.le ht.2) ht0 kernel_pos.le (by positivity)
     _ ≤ (C*w^k*Real.exp (-c*‖u‖^2))*(t*w*r⁻¹)^N := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hw')
     _ = _ := by change _= C*(r⁻¹)^N * t^N * (w^(k+N)*Real.exp _); simp [mul_pow,pow_add];ring

omit μ hf F in
private lemma point {c C : ℝ}{f : E→ℝ}{K : E→ℝ}(n k : ℕ)(h : ∀ u, (c+c)*‖u‖^2 ≤ jet f 2 u)(hC : 0≤ C)
    {t : ℝ}(ht : 0≤t){u : E}
    (h' : ‖insertion f K t u - eval (integrandSeries f K) n t u‖≤ C*(Z).w u^k*shade c u*t^(n+1)) :
    ‖(projection K f t - poly K f n t) u‖ ≤ (C*t^(n+1))*bill k c u := by
  have hb:=h u
  let w := (Z).w u
  have hht : 0≤w := lt_of_lt_of_le zero_lt_one ((Z).high ..) |>.le
  rw [Pi.sub_apply,projection,poly,← sub_mul,norm_mul]
  simp only [norm_mul,Real.norm_eq_abs (kernel ..),abs_of_nonneg kernel_pos.le]
  calc
     _ ≤ C*w^k*shade c u*t^(n+1)*kernel f u := mul_le_mul_of_nonneg_right h' kernel_pos.le
     _ = (C*t^(n+1))*(w^k)*(shade c u * kernel f u):=by ring
     _ ≤ (C*t^(n+1))*(w^k)* Real.exp (-c*‖u‖^2) := mul_le_mul_of_nonneg_left (kernel_bound hb) (by positivity)
     _ = _ := by unfold bill;ring

protected theorem rescale_estimate (hK : Measurable K)(hf' : Measurable f)
    (H : ∃ c>0,∀ u : E,c*‖u‖^2≤jet f 2 u)(n : ℕ) :
    ∃ δ>0, ∀ r∈Ioo 0 δ,∃ C,∀ᶠ t in 𝓝[>] (0:ℝ),
      ‖partialSum μ K f r t - ∑ i∈Finset.range (n+1),t^i*moment μ K f i‖ ≤ C*t^(n+1) := by
  obtain ⟨m,hm,h⟩:=H
  let c := m/2
  have hc:0<c:=half_pos hm
  have h (u) : (c+c)*‖u‖^2≤jet f 2 u:=by convert h u using 1; unfold c;ring
  obtain ⟨δ,C,e,hδ,hC,hb⟩:=((integrand hf F hc).fits n).cost
  refine ⟨δ/2,by positivity,fun r hr=>?_⟩
  obtain ⟨B,hB⟩:=F.outside μ hf ⟨m,hm,by simpa [c] using h⟩ n (n+1) hr.1
  refine ⟨(∫ u:E,bill e c u ∂μ)*C+B,?_⟩; rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds (show 0 < min 1 (δ/2) from lt_min zero_lt_one (half_pos hδ))] with t ht (ht' : t∈Ioi 0)
  have ht' := ht'
  change 0 < t at ht'
  let S : Set E:=disc t r
  let d : E→ℝ := projection K f t - poly K f n t
  have H : ∀ᵐ u ∂μ.restrict S, ‖d u‖≤ (C*t^(n+1))*bill e c u := by
    filter_upwards [ae_restrict_mem (disc_meas t r)] with u hu
    have hh : t*(Z).w u≤δ := by change t*(1+‖u‖)≤δ; have hu := (disc_mem ht'.le r u).mp hu; unfold S at *;nlinarith [hr.2,ht.trans_le (min_le_right ..)]
    exact point n e h hC ht'.le (hb _ _ ht' hh)
  obtain ⟨h₁,h₂⟩:=scaledBound μ hc (by positivity:0≤C*t^(n+1)) H
  have hp:=F.integrable_poly μ hf n (t:=t) ⟨(c+c),add_pos hc hc,h⟩
  have ha : IntegrableOn (projection K f t) S μ:= by
    have hm : AEStronglyMeasurable d (μ.restrict S) := (projection_meas hK hf' t).aestronglyMeasurable.sub hp.integrableOn.1
    have ho := ((h₁.mono' hm H).add hp.integrableOn); unfold d at ho; rw [sub_add_cancel] at ho; exact ho
  have h₂' := h₂
  change ‖∫ u in S, projection K f t u - poly K f n t u ∂μ‖≤_ at h₂
  rw [integral_sub ha hp.integrableOn] at h₂
  unfold partialSum; change ‖(∫ u in S,projection K f t u ∂μ) - (∑ i∈Finset.range (n+1),t^i*moment μ K f i)‖ ≤ _
  rw [← F.integral_eval μ hf ⟨c+c,add_pos hc hc,h⟩,←integral_add_compl (s:=S) (disc_meas ..) hp,sub_add_eq_sub_sub]
  exact (norm_sub_le ..).trans <| (add_le_add h₂ (hB t ⟨ht',ht.le.trans (min_le_left ..)⟩)).trans_eq (by ring)

end Stationary
end YM.PertExtension.Series.Radial
