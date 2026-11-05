import YM.RemainderComparison.Relative
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Blips
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
 # Vertical Taylor with passive probes. Pull coupling parameter into SAME chart
 as coarse real field before sending b to zero in the model. `lift` remembers
 complete transverse finite-derivative budgets through division by a finite power
 of b (fluctuation order criterion is applied separately on actual packets).
 For Tayloring only the purchased interior integrand, not per-configuration mask.
 See also multi-axis coefficient proxy estimates using this.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Trace
open Metric Set Function Filter MeasureTheory Finset
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat
open scoped Topology ContDiff BigOperators Classical Interval ENNReal
variable {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {x : E} {b t A C p : ℝ} {m j : ℕ}

lemma nearby {f : E → F} (hf : Brush j A 1 f x) {A' : ℝ} (hp : A < A') :
    ∀ᶠ y in 𝓝 x, Brush j A' 1 f y := by
  have hh (i : Fin (j+1)) : ∀ᶠ y in 𝓝 x, normJ i f y < A' :=
    (hf.smooth.continuousAt_iteratedFDeriv (by exact_mod_cast (show i.val ≤ j from Nat.lt_succ_iff.mp i.isLt))).norm.eventually (gt_mem_nhds (((Brush.offer.1 hf).2 _ (Nat.lt_succ_iff.mp i.isLt)).trans_lt hp))
  filter_upwards [eventually_all.mpr hh,hf.smooth.eventually (by simp)] with y hy h
  exact Brush.offer.2 ⟨h,fun i hi=> (hy ⟨i,Nat.lt_succ_iff.mpr hi⟩).le⟩

/-- Homogeneous vertical derivative; no factorial. -/
def plain (f : ℝ×E→F) (m : ℕ) (x : ℝ×E) : F:=
  iteratedFDeriv ℝ m f x (fun _=> (1,0))
def coefficient (f : ℝ×E→F) (k : ℕ) (x : E) : F := (k.factorial:ℝ)⁻¹ • plain f k (0,x)
def polyeval (m : ℕ) (a : ℕ→E→F) (x : ℝ × E) := ∑ i∈range (m+1), x.1^i • a i x.2
def trunc (m : ℕ) (f : ℝ×E→F) : ℝ×E→ F := polyeval m (coefficient f)

lemma normalized_fact (i : ℕ) : ‖(i.factorial:ℝ)⁻¹‖ ≤ 1 := by
  have hp : 1 ≤ (i.factorial:ℝ):= Nat.one_le_cast.mpr (Nat.factorial_pos i)
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ hp

private lemma brush_iso {f : E→F} (h : Brush j C 1 f x) (L : F ≃ₗᵢ[ℝ] Y) : Brush j C 1 (L ∘ f) x :=
    (h.report L.toLinearIsometry.toContinuousLinearMap L.toLinearIsometry.norm_toContinuousLinearMap_le).climb (by rw [one_mul]) le_rfl

lemma budgetJ {f : E→F} (h : Brush (j + m) C 1 f x) : Brush j C 1 (iteratedFDeriv ℝ m f) x := by
  induction m generalizing j with
  | zero =>
    let L := continuousMultilinearCurryFin0 ℝ E F
    rw [iteratedFDeriv_zero_eq_comp]
    exact brush_iso h L.symm
  | succ i ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    let L:= continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (i+1)=>E) F
    have hp : Brush j C 1 (fderiv ℝ (iteratedFDeriv ℝ i f)) x:= Lantern.norm_F (ih (by rw [show j+1+i=j+(i+1) by omega]; exact h))
    exact brush_iso hp L.symm

lemma plain_jet {x : ℝ×E} {f : ℝ×E→F} (h : Brush (j+m) C 1 f x) : Brush j C 1 (plain f m) x := by
  let L:= ContinuousMultilinearMap.apply ℝ (fun _:Fin m=>ℝ×E) F (fun _ : Fin m=> ((1:ℝ),(0:E)))
  have hp : ‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z=> by
    have h:= z.le_opNorm (fun _=> (1,0))
    change ‖z _‖ ≤ _; simpa using h
  exact (Brush.report (budgetJ h) L hp).climb (by rw [one_mul]) le_rfl

lemma trace_arc {t : ℝ} {f : ℝ×E→F} (h : Brush j C 1 f (t,x)) : Brush j C 1 (fun y=> f (t,y)) x := by
  have he v : (t,v)=(t,(0:E))+ Lantern.hook E v:= by simp
  rw [show (fun y=> f (t,y))=(fun y:E=> f ((t,(0:E))+Lantern.hook E y)) from funext fun i=> congr_arg f (he i)]
  exact Lantern.skim _ (by rw [← he]; exact h) Lantern.n_hook

lemma sample {f : ℝ×E→F} (h : Brush (j+m) C 1 f (0,x)) : Brush j C 1 (coefficient f m) x :=
  ((trace_arc (plain_jet h)).smul ((m.factorial:ℝ)⁻¹)).climb (mul_le_of_le_one_left h.nonneg (normalized_fact _)) le_rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma polyeval_zero (a : ℕ→E→F) (m : ℕ) (x : E) : polyeval m a (0,x) = a 0 x := by
  unfold polyeval; rw [sum_eq_single (0:ℕ)]
  · simp
  · intro b _ hb; rw [zero_pow hb, zero_smul]
  simp

variable (f : ℝ×E→F) (m : ℕ)
local notation "win" => Icc (0:ℝ) 1
local notation "Zₘ" => Measure.restrict (volume (α:=ℝ)) (Ioc (0:ℝ) 1)

def toll (i : ℕ) (v : ℝ×E) (t : ℝ) := (1-t)^i • plain f (i+1) (t*v.1,v.2)
/-- Integral remainder coefficient, including at b=0 (= first omitted coefficient). -/
def pending (m : ℕ) (v : ℝ×E) := (m.factorial:ℝ)⁻¹ • ∫ t in (0:ℝ)..1, toll f m v t

section receipt
variable [CompleteSpace F]
lemma quote (hp : ∀ t∈win, ContDiffAt ℝ (↑(m+1:ℕ)) f (t*b,x)) :
    f (b,x)= trunc m f (b,x) + b^(m+1) • pending f m (b,x) := by
  let z:=((0:ℝ),x); let p:ℝ×E:=(b,0)
  have hx t : z+t • p=(t*b,x):=by simp [z,p]
  have he (t) (h:t∈win) : ContDiffAt ℝ (↑m+1) f (z+t • p):= by rw [hx]; exact_mod_cast hp t h
  rw [show f (b,x)=f (z+p) from congr_arg f (by simp [z,p]), map_add_eq_sum_add_integral_iteratedFDeriv he]
  have hh i (v: ℝ×E): (iteratedFDeriv ℝ i f v) (fun _=> p)= b^i • plain f i v:= by
    rw [show p= b • (1,(0:E)) from (by simp [p] : p=b • ((1:ℝ),(0:E))),ContinuousMultilinearMap.map_smul_univ]
    unfold plain; rw [prod_const,card_univ,Fintype.card_fin]
  apply congr_arg₂ (fun a c : F=> a+c)
  · unfold trunc polyeval; refine sum_congr rfl (fun i _=>?_)
    unfold coefficient; rw [hh i]; exact smul_comm ..
  unfold pending; rw [smul_comm (b^(m+1))]; apply congr_arg; rw [← intervalIntegral.integral_smul]; refine intervalIntegral.integral_congr fun i _=>?_
  unfold toll; dsimp only; rw [hx,hh]; exact smul_comm ..
end receipt

def crossing (t : ℝ) : (ℝ×E)→L[ℝ] (ℝ×E):= (t • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)
lemma fare (t : ℝ) (ht:t∈win) : ‖crossing (E:=E) t‖ ≤ 1:=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by
    rw [one_mul]; change max ‖t • i.1‖ ‖i.2‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg ht.1]; exact max_le ((mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_fst_le _)) (norm_snd_le _)
lemma rotate {v : ℝ×E} (hp : t∈win) (he : Brush (j+(m+1)) A 1 f (crossing t v)) :
    Brush j A 1 (fun y=> toll f m y t) v := by
  have hu := plain_jet he
  have hh := Brush.reading (crossing (E:=E) t) hu (fare (E:=E) t hp); rw [one_mul] at hh
  apply (hh.smul ((1-t)^m)).climb _ le_rfl
  have h : 0≤1-t:= sub_nonneg.mpr hp.2
  rw [Real.norm_of_nonneg (pow_nonneg h _)]
  exact mul_le_of_le_one_left hu.nonneg (pow_le_one₀ h (sub_le_self _ hp.1))

section wallet
variable [FiniteDimensional ℝ E] [SecondCountableTopology F] -- only strong meas wrapper; possibly remove
variable [CompleteSpace F]
lemma work (u : ℝ×E) (h : ∀ᶠ y in 𝓝 u, ∀ t∈win, Brush (j+(m+1)) A 1 f (crossing t y)) :
    Brush j A 1 (pending f m) u := by
  let P:= win
  let H y := P.indicator (toll f m y)
  have hf :0≤A := (h.self_of_nhds _ (left_mem_Icc.mpr zero_le_one)).nonneg
  have hp : ∀ᶠ y in 𝓝 u,∀ i, Brush j A 1 (fun y=> H y i) y := by
    filter_upwards [h] with y hy i
    by_cases ht:i∈P
    · exact (rotate f m ht (hy i ht)).shimmy (Eventually.of_forall fun j=>indicator_of_mem ht _)
    exact ((Brush.certified zero_le_one (k:=j) (x:=y) (0:F)).climb (by simpa using hf) le_rfl).shimmy (Eventually.of_forall fun _=> indicator_of_notMem ht _)
  have ht : ∀ᶠ y in 𝓝 u, StronglyMeasurable (H y) := by
    filter_upwards [h] with y hy
    borelize F
    apply Measurable.stronglyMeasurable
    apply measurable_of_restrict_of_restrict_compl (s:=P) measurableSet_Icc
    · rw [show P.restrict (H y)=P.restrict (toll f m y) from funext fun i=> indicator_of_mem i.2 _]
      apply Continuous.measurable; apply continuousOn_iff_continuous_restrict.mp; intro t ht
      apply ContinuousAt.continuousWithinAt; apply (show ContinuousAt (fun i:ℝ=> (1-i)^m) t by fun_prop).smul
      exact (plain_jet (hy t ht)).smooth.continuousAt.comp (f:=fun i:ℝ=> (i*y.1,y.2)) (show ContinuousAt (fun i:ℝ=> (i*y.1,y.2)) t from by fun_prop)
    rw [show Pᶜ.restrict (H y)=(fun _=>0) from funext fun i=> indicator_of_notMem i.2 _]; exact measurable_const
  have hA : (Zₘ).real Set.univ=1:= by simp [Measure.real]
  letI : IsFiniteMeasure Zₘ:= inferInstance
  have hh := Relative.test_domination (μ:=Zₘ) (M:=fun _=>A) (integrable_const _) hp ht
  have he: ∀ i: ℝ×E, (∫ t in (0:ℝ)..1, toll f m i t)= ∫ y, H i y ∂(Zₘ) := by
    intro i; rw [intervalIntegral.integral_of_le zero_le_one]; apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc] with y hy using Eq.symm (indicator_of_mem (Ioc_subset_Icc_self hy) _)
  unfold pending; simp_rw [he]
  exact (((hh.buds (fun _=> A) (integrable_const _) zero_le_one (by rw [integral_const,hA,one_smul]) (ae_of_all _ hp.self_of_nhds)).smul _).climb (mul_le_of_le_one_left hf (normalized_fact _)) le_rfl)

lemma vertically {b : ℝ} {x : E} (h : ∀ᶠ y in 𝓝 (b,x), ∀ t∈win, Brush (j+(m+1)) A 1 f (crossing t y)) :
    Brush j (|b|^(m+1)*A) 1 (fun y=> f (b,y)-trunc m f (b,y)) x := by
  have he := (trace_arc (work f m _ h)).smul (b^(m+1)); rw [norm_pow,Real.norm_eq_abs] at he
  refine he.shimmy ?_
  have hp := Tendsto.eventually (show Tendsto (fun i:E=>(b,i)) (𝓝 x) (𝓝 (b,x)) from continuousAt_const.prodMk continuousAt_id) h
  filter_upwards [hp] with y hy
  have h := quote f m (x:=y) (b:=b) (fun i hi=> ((hy i hi).smaller (show m+1≤j+(m+1) from Nat.le_add_left ..)).smooth)
  rw [h, add_sub_cancel_left]
end wallet
end YM.RemainderComparison.Trace
