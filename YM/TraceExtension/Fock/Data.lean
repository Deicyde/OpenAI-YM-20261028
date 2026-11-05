import YM.TraceExtension.Fock.Jets

/-! Uniform Cauchy-data distribution in one leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff
variable {m n d : ℕ}

/-- Leave one leg open. -/
def slot (g : Fin n→Probe E4) (i : Fin n) (p : Mom n) := ∏ j∈Finset.univ.erase i, front (g j) (p j)
def sink (b : ℕ) (g : Fin n→Probe E4) (i : Fin n) (f : Probe Space3) (p : Mom n) :=
    (‖p i‖:ℂ) ^ (b+1) * f (p i)*slot g i p
@[fun_prop] lemma sink_cont (b : ℕ) (g : Fin n→Probe E4) (i : Fin n) (f : Probe Space3) : Continuous (sink b g i f) := by
    unfold sink slot front; fun_prop

def normCost (j : ℕ) : Seminorm ℂ (Probe Space3) :=
    NNReal.mk ((2:ℝ)^j) (by positivity) • (SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ j 0)
lemma normCost_le (j : ℕ) (f : Probe Space3) (p : Space3) :
    ‖f p‖ ≤ normCost j f * (env j p)⁻¹ := by
    have hx := pow_mul_le_of_le_of_pow_mul_le (k:=0) (x:=‖p‖) (l:=j) (C₁:=Probe.size 0 0 f)
       (C₂:=Probe.size j 0 f) (norm_nonneg _) (norm_nonneg (f p))
       (by simpa using SchwartzMap.le_seminorm ℂ 0 0 f p)
       (by simpa using SchwartzMap.le_seminorm ℂ j 0 f p)
    simpa [normCost,env, mul_add,Real.rpow_neg (by positivity : 0 ≤ 1+‖p‖),NNReal.smul_def] using hx
lemma normCost_cont (j:ℕ) : Continuous ⇑(normCost j) := Continuous.const_smul
    ((Probe.cont_size 0 0).add (Probe.cont_size j 0)) (NNReal.mk ((2:ℝ)^j) (by positivity))

lemma slot_cost (d b : ℕ) (g : Fin n → Probe E4) (i : Fin n) :
    ∃ A : ℝ, 0≤A ∧ ∀ f p, ‖sink b g i f p‖≤ (A*normCost (d+(b+1)) f)*(shield d p)⁻¹ := by
    choose C hC hv using fun j => front_bound (g j) d
    let A := ∏ j∈Finset.univ.erase i, C j
    have hA : 0≤A := Finset.prod_nonneg fun j _ => hC j
    refine ⟨A,hA,fun f p=>?_⟩
    let R := ∏ j∈ Finset.univ.erase i, env d (p j)
    have he : ‖slot g i p‖ ≤ A*R⁻¹ := by
        unfold slot; rw [norm_prod]; apply (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>hv j (p j))).trans_eq
        rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
    have hw : shield d p=env d (p i)*R := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
    let N := normCost (d+(b+1)) f
    have hN : 0≤N := apply_nonneg ..
    have ht : ‖p i‖^(b+1)*‖f (p i)‖≤N*(env d (p i))⁻¹ := by
        calc _ ≤ (1+‖p i‖)^(b+1) * (N * (env (d+(b+1)) (p i))⁻¹) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _) (normCost_le _ _ _) (norm_nonneg _) (by positivity)
             _ = _ := by unfold env; rw [pow_add]; field_simp; ring
    unfold sink; simp only [norm_mul,norm_pow,Complex.norm_real, norm_norm]
    refine (mul_le_mul ht he (norm_nonneg _) (mul_nonneg hN (inv_nonneg.mpr (env_positive .. |>.le)))).trans_eq ?_
    rw [hw,mul_inv_rev]; unfold N; ring
lemma sink_int (b) (q : Wave n) (hp : tempered q d) (g) (i : Fin n) (f : Probe Space3) :
    Integrable (fun k => q k*sink b g i f k) (photons n) ∧ Integrable (fun k => star (q k)*sink b g i f k) (photons n) := by
    obtain ⟨A,hA,he⟩ := slot_cost (d+2) b g i; let a := A*normCost ((d+2)+(b+1)) f
    have hs (k) : ‖q k‖ * ‖sink b g i f k‖≤(‖q k‖*(shield (d+2) k)⁻¹)*a := by
        refine (mul_le_mul_of_nonneg_left (he f k) (norm_nonneg _)).trans_eq ?_; unfold a; ring
    have ht := (austere q hp).mul_const a
    exact ⟨ht.mono' ((wave_meas q).aestronglyMeasurable.mul (sink_cont b g i f).aestronglyMeasurable)
        (ae_of_all _ fun k => (norm_mul ..).trans_le (hs k)),
      ht.mono' ((wave_meas q).aestronglyMeasurable.star.mul (sink_cont b g i f).aestronglyMeasurable)
        (ae_of_all _ fun k => (by change ‖star (q k)*sink b g i f k‖≤ _; rw [norm_mul,norm_star]; exact hs k))⟩

def dataM (b) (q : Wave n) (g : Fin n→Probe E4) (i : Fin n) (f : Probe Space3) :=
    ∫ p, q p*sink b (Probe.hat ∘ g) i (Probe.hat f) p ∂photons n
def dataP (b) (q : Wave n) (g : Fin n→Probe E4) (i : Fin n) (f : Probe Space3) :=
    ∫ p, star (q p)*sink b (testPlus ∘ g) i (testPlus f) p ∂photons n
def data (b) (q : Wave n) (g : Fin n→Probe E4) (i : Fin n) (f : Probe Space3) :=
    dataM b q g i f - (-1:ℂ)^b*dataP b q g i f

lemma sink_add (b g) (i : Fin n) (f h : Probe Space3) (p) : sink b g i (f+h) p=sink b g i f p+sink b g i h p := by simp only [sink,_root_.add_apply,mul_add,add_mul]
lemma sink_smul (b g) (i : Fin n) (f : Probe Space3) (c : ℂ) (p) : sink b g i (c • f) p = c*sink b g i f p := by unfold sink; rw [_root_.smul_apply,smul_eq_mul]; ring
lemma data_linear (b) (q : Wave n) (hp : tempered q d) (g) (i : Fin n) : IsLinearMap ℂ (data b q g i) := by
    constructor
    · intro x y; unfold data dataM dataP; simp_rw [map_add,sink_add,mul_add]
      rw [integral_add (sink_int _ _ hp ..|>.1) (sink_int _ _ hp ..|>.1),integral_add (sink_int _ _ hp ..|>.2) (sink_int _ _ hp ..|>.2),mul_add]; ring
    intro c v; unfold data dataM dataP; simp_rw [map_smul,sink_smul,mul_left_comm (q _),mul_left_comm (star (q _)) c]
    rw [integral_const_mul,integral_const_mul,smul_eq_mul]; ring

def dataCost (j) := (normCost j).comp ((Probe.hat:(Probe Space3)→L[ℂ](Probe Space3)).toLinearMap) +
    (normCost j).comp ((testPlus:(Probe Space3)→L[ℂ](Probe Space3)).toLinearMap)
lemma dataCost_cont (j) : Continuous ⇑(dataCost j) := Continuous.add ((normCost_cont j).comp Probe.hat.continuous) ((normCost_cont j).comp testPlus.continuous)

lemma band_cost (b) (q : Wave n) (hp : tempered q d) (g) (i : Fin n) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖data b q g i x‖ ≤ C*dataCost ((d+2)+(b+1)) x := by
    obtain ⟨A,hA,hM⟩ := slot_cost (d+2) b (Probe.hat ∘ g) i
    obtain ⟨B,hB,hP⟩ := slot_cost (d+2) b (testPlus ∘ g) i
    let W k := ‖q k‖*(shield (d+2) k)⁻¹
    let K := ∫ k,W k ∂photons n
    have hK : 0≤K := integral_nonneg (fun k => mul_nonneg (norm_nonneg _) (by have := shield_pos (d+2) k; positivity))
    let N := normCost ((d+2)+(b+1)); let c := K*(A+B)
    refine ⟨c,by unfold c; positivity,fun x=>?_⟩
    have he (p : Mom n) : ‖q p‖*‖sink b (Probe.hat ∘ g) i (Probe.hat x) p‖ ≤ (A*N (Probe.hat x))*W p := (mul_le_mul_of_nonneg_left (hM _ _) (norm_nonneg _)).trans_eq (by unfold W N; ring)
    have hs (p : Mom n) : ‖q p‖*‖sink b (testPlus ∘ g) i (testPlus x) p‖ ≤ (B*N (testPlus x))*W p := (mul_le_mul_of_nonneg_left (hP _ _) (norm_nonneg _)).trans_eq (by unfold W N; ring)
    have hv := norm_integral_le_of_norm_le (f:=fun k=> q k*sink b (Probe.hat ∘ g) i (Probe.hat x) k) ((austere _ hp).const_mul (A*N (Probe.hat x))) (ae_of_all _ fun k => by rw [norm_mul]; exact he _)
    rw [integral_const_mul] at hv
    have hw := norm_integral_le_of_norm_le (f:=fun k=> star (q k)*sink b (testPlus ∘ g) i (testPlus x) k) ((austere _ hp).const_mul (B*N (testPlus x))) (ae_of_all _ fun k => by rw [norm_mul,norm_star]; exact hs _)
    rw [integral_const_mul] at hw
    apply (norm_sub_le ..).trans; simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]; apply (add_le_add hv hw).trans
    change A*N (Probe.hat x)*K+B*N (testPlus x)*K ≤ c*(N (Probe.hat x)+N (testPlus x))
    have hm : 0≤A*N (testPlus x)*K := mul_nonneg (mul_nonneg hA (apply_nonneg ..)) hK
    have hy : 0≤B*N (Probe.hat x)*K := mul_nonneg (mul_nonneg hB (apply_nonneg ..)) hK
    unfold c; linarith

lemma data_order (n b d : ℕ) : ∃ ℓ : ℕ, ∀ (q : Wave n), tempered q d → ∀ (g : Fin n→ Probe E4) (i : Fin n), (∀ f : Probe Space3, HasCompactSupport ⇑f → 0∉tsupport f → data b q g i f=0) → ∀ f, finiteOrder f ℓ → data b q g i f=0 := by
    let p := dataCost ((d+2)+(b+1))
    obtain ⟨k,hk⟩ := jet_support p (dataCost_cont _)
    refine ⟨k,fun q h g i hp f hf =>?_⟩
    obtain ⟨C,hC,hA⟩ := band_cost b q h g i
    let A := IsLinearMap.mk' _ (data_linear b q h g i)
    have ht : Continuous A := by
        apply continuous_of_continuousAt_zero A
        apply Metric.tendsto_nhds.mpr; intro ε he
        have hv : Continuous (fun F => C*p F) := continuous_const.mul (dataCost_cont _)
        have hu : (0:ℝ) < ε := he
        filter_upwards [(hv.tendsto 0).eventually (gt_mem_nhds (by rw [map_zero,mul_zero]; exact he))] with y hy
        rw [map_zero,dist_zero_right]; exact lt_of_le_of_lt (hA y) hy
    exact hk (⟨A,ht⟩ : Distn Space3) _ hC hA hp f hf
end YM.TraceExtension.Photons
