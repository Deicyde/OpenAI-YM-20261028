import YM.TraceExtension.Fock.Zoom

/-! Homogeneous-sector dilation relation, part I. The Euler operator
used here is discrete dilation by 2. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff
variable {m n d : ℕ}

lemma dble_embed (i : Fin n) : MeasurableEmbedding (doubling i) := by
    let v (x : Mom n) := update x i ((2:ℝ)⁻¹ • x i)
    let V : Mom n ≃ᵐ Mom n := {
        toFun := doubling i
        invFun := v
        left_inv := fun x=> by unfold v doubling blow; simp [smul_smul]
        right_inv := fun x=> by unfold v doubling blow; simp [smul_smul]
        measurable_toFun := (stretch i).measurable
        measurable_invFun := (show Measurable v from by
            apply measurable_pi_lambda; intro j; change Measurable (fun x : Mom n=> update x i ((2:ℝ)⁻¹ • x i) j); by_cases h:j=i
            · rw [h]; simp_rw [update_self]; fun_prop
            simp_rw [update_of_ne h]; exact measurable_pi_apply _) }
    exact V.measurableEmbedding

lemma scale_value (i : Fin n) (f : Mom n→ℂ) :
    (∫ x,f (doubling i x) ∂photons n) = (2:ℂ)⁻¹^2 * ∫ x,f x ∂photons n := by
    rw [(stretch i).integral_comp (dble_embed i) f, integral_smul_measure, Complex.real_smul]; norm_num

lemma slot_same (g) (i : Fin n) (p) : slot g i (doubling i p)=slot g i p := by
    apply Finset.prod_congr rfl; intro j hj; simp only [doubling, update_of_ne (Finset.ne_of_mem_erase hj)]
lemma sink_same (w w' : Probe Space3) (hp : ∀ x,w' ((2:ℝ) • x)=w x) (g) (i : Fin n) (b : ℕ) (p) :
    sink b g i w' (doubling i p)= (2:ℂ) ^ (b+1) * sink b g i w p := by
    unfold sink; rw [slot_same]; unfold doubling blow; rw [update_self, hp,norm_smul]; norm_num; ring

def timeScale (b : ℕ) : ℝ := ((2:ℝ)^(3+b))⁻¹
lemma zoom_result (i : Fin n) (q : Wave n) (b : ℕ) (g : Fin n→ Probe E4) (f : Probe Space3) :
    data b (zoom i q) g i f=(↑(timeScale b):ℂ)*data b q g i (condense 2 f) := by
    have he : ∀ x : Space3, testPlus (condense 2 f) ((2:ℝ) • x)=testPlus f x := by
       intro x; rw [condense_plus 2 (by norm_num), smul_smul]; norm_num
    have hp : ∀ x : Space3, Probe.hat (condense 2 f) ((2:ℝ) • x)=Probe.hat f x := by
       intro x; rw [plus_minus,plus_minus (p:=x), ← smul_neg,he]
    have hw : (↑(timeScale b):ℂ) = ((2:ℂ)^(b+1))⁻¹ * (2:ℂ)⁻¹^2 := by
        unfold timeScale; push_cast; rw [pow_add]; field_simp; ring
    have hh : dataM b (zoom i q) g i f = (↑(timeScale b):ℂ) * dataM b q g i (condense 2 f) := by
        unfold dataM; rw [hw,mul_assoc,← scale_value i,← integral_const_mul]; apply integral_congr_ae; filter_upwards [zoom_ae i q] with p ht
        rw [ht, comp_apply,sink_same _ _ hp]; field_simp
    have hv : dataP b (zoom i q) g i f = (↑(timeScale b):ℂ) * dataP b q g i (condense 2 f) := by
        unfold dataP; rw [hw,mul_assoc,← scale_value i,← integral_const_mul]; apply integral_congr_ae; filter_upwards [zoom_ae i q] with p ht
        rw [ht, comp_apply,sink_same _ _ he]; field_simp
    unfold data; rw [hh,hv]; ring

lemma scale_jets (j) (f : Probe Space3) :
    iteratedFDeriv ℝ j ⇑(condense 2 f) 0 = ((2:ℝ)^(3+j)) • iteratedFDeriv ℝ j f 0 := by
    let L := (2:ℝ) • ContinuousLinearMap.id ℝ Space3
    have hp (i : ℕ) : ContDiff ℝ (↑i : WithTop ℕ∞) (f ∘ L) := ((f.smooth i).comp L.contDiff)
    rw [show ⇑(condense 2 f)= ((2:ℝ)^3) • (f ∘ L) by ext1 x; rw [condense_eval 2 (by norm_num),show Module.finrank ℝ Space3=3 from finrank_euclideanSpace_fin]; rfl]
    rw [iteratedFDeriv_const_smul_apply (hp j).contDiffAt, L.iteratedFDeriv_comp_right (f.smooth ⊤) 0 (by exact_mod_cast le_top),map_zero]
    apply ContinuousMultilinearMap.ext; intro x
    change (2:ℝ)^3 • ((iteratedFDeriv ℝ j f 0) fun i=> (2:ℝ) • x i) = (2:ℝ)^(3+j) • _
    rw [ContinuousMultilinearMap.map_smul_univ _ (fun _=> (2:ℝ)) x, smul_smul,pow_add]; simp

lemma data_sub (p q : Wave n) (hp : tempered p d) (hq : tempered q d) (b g i f) : data b (p-q) g i f=data b p g i f-data b q g i f := by
    have he : dataM b (p-q) g i f=dataM b p g i f-dataM b q g i f := by
        unfold dataM; rw [← integral_sub (sink_int _ _ hp ..|>.1) (sink_int _ _ hq ..|>.1)]; apply integral_congr_ae
        filter_upwards [AEEqFun.coeFn_sub p q] with i hi; simp [hi,sub_mul]
    have hu : dataP b (p-q) g i f=dataP b p g i f-dataP b q g i f := by
        unfold dataP; rw [← integral_sub (sink_int _ _ hp ..|>.2) (sink_int _ _ hq ..|>.2)]; apply integral_congr_ae
        filter_upwards [AEEqFun.coeFn_sub p q] with i hi; simp only [hi,Pi.sub_apply,star_sub,sub_mul]
    unfold data; rw [he,hu,mul_sub]; ring
lemma data_mul (p : Wave n) (c : ℝ) (b g i f) : data b (c • p) g i f=(↑c:ℂ)* data b p g i f := by
    have he : dataM b (c • p) g i f = (↑c:ℂ)* dataM b p g i f := by
        unfold dataM; rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards [AEEqFun.coeFn_smul c p] with i hi; simp [hi,Complex.real_smul,mul_assoc]
    have hu : dataP b (c • p) g i f = (↑c:ℂ)* dataP b p g i f := by
        unfold dataP; rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards [AEEqFun.coeFn_smul c p] with i hi; simp [hi,Complex.real_smul,mul_assoc]
    unfold data; rw [he,hu]; ring

def eigenFee (i : ℕ) : ℝ := 2^i/2
def signalPoly (i : Fin n) (q : Wave n) : (k : ℕ) → Wave n
 | 0 => q
 | k+1 => zoom i (signalPoly i q k) - eigenFee k • (signalPoly i q k)
lemma signal_tempered (i : Fin n) (q : Wave n) (hp : tempered q d) (k) : tempered (signalPoly i q k) d := by
    induction k with
    | zero=> exact hp
    | succ k ih=> exact tempered_sub _ _ (tempered_zoom _ ih _) (tempered_mul _ ih _)

private def condDiff (b k : ℕ) (f : Probe Space3) := (↑(timeScale b):ℂ) • condense 2 f - (↑(eigenFee k):ℂ) • f
private def testPoly (b : ℕ) (f : Probe Space3) (k : ℕ) : Probe Space3 := match k with
 | 0 => f
 | k+1 => testPoly b (condDiff b k f) k
lemma data_poly (q : Wave n) (hp : tempered q d) (i : Fin n) (b g f k) : data b (signalPoly i q k) g i f=data b q g i (testPoly b f k) := by
    induction k generalizing f with
    | zero=> rfl
    | succ k ih=>
        have he := signal_tempered i q hp k
        rw [signalPoly,data_sub _ _ (tempered_zoom _ he _) (tempered_mul _ he _),data_mul,zoom_result,testPoly,← ih, condDiff,(data_linear b _ he g i).map_sub]
        simp_rw [(data_linear b _ he g i).map_smul,smul_eq_mul]

private def jetFee (b j : ℕ) := timeScale b * (2:ℝ)^(3+j)
private lemma test_jets (f : Probe Space3) (b k j : ℕ) : iteratedFDeriv ℝ j ⇑(testPoly b f k) 0 =
    (∏ i∈Finset.range k,(jetFee b j - eigenFee i)) • iteratedFDeriv ℝ j f 0 := by
    induction k generalizing f with
    | zero=> simp [testPoly]
    | succ k ih=>
       rw [testPoly,ih, condDiff]
       let g := condense 2 f
       let t := timeScale b; let w := eigenFee k
       have he : ((↑t:ℂ) • g - (↑w:ℂ) • f : Probe Space3) = t • g+ (-w) • f := by
            ext; simp [Complex.real_smul,sub_eq_add_neg]
       rw [he]
       rw [show ⇑(t • g+(-w) • f)=(t • ⇑g + (-w) • ⇑f) from rfl,
         iteratedFDeriv_add_apply, iteratedFDeriv_const_smul_apply (g.smooth j).contDiffAt, iteratedFDeriv_const_smul_apply (f.smooth j).contDiffAt,
         show iteratedFDeriv ℝ j g 0=_ from scale_jets j f, smul_smul, ← add_smul,Finset.prod_range_succ, smul_smul]; rfl
       exacts [((g.smooth j).const_smul t).contDiffAt, ((f.smooth j).const_smul (-w)).contDiffAt]

lemma dyadic_order (q : Wave n) (hp : tempered q d) (h : ∀ g, (∀ i,Remote (g i)) → paired_at q g=adjoint_at q g) :
    ∃ k : ℕ, ∀ (i : Fin n) (g), (∀ j, Remote (g j)) → ∀ (f : Probe Space3),
       data 0 (signalPoly i q k) g i f=0 ∧ data 1 (signalPoly i q k) g i f=0 := by
    obtain ⟨a,ha⟩ := data_order n 0 d
    obtain ⟨c,hc⟩ := data_order n 1 d
    let k:= a+c+2
    refine ⟨k,fun i g hg f=>?_⟩
    rw [data_poly q hp,data_poly q hp]
    refine ⟨ha q hp g i (cauchy_point q hp h i g hg 0) _ (fun j hj=> ?_),hc q hp g i (cauchy_point q hp h i g hg 1) _ (fun j hj=> ?_)⟩
    · rw [test_jets,Finset.prod_eq_zero (Finset.mem_range.mpr (show j+1<k from by unfold k; omega)) (show jetFee 0 j-eigenFee (j+1)=0 from ?_),zero_smul]; unfold jetFee eigenFee timeScale; ring
    rw [test_jets,Finset.prod_eq_zero (Finset.mem_range.mpr (show j<k from by unfold k; omega)) (show jetFee 1 j-eigenFee j=0 from ?_),zero_smul]; unfold jetFee eigenFee timeScale; ring
end YM.TraceExtension.Photons
