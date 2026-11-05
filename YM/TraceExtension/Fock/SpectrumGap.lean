import YM.TraceExtension.Fock.Eigen

/-! Positivity power argument on dyadic bands. Growth upper limit is a
property of the full Fock wave, not of any hypothetical Wick series expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {n : ℕ}

lemma eigen_mass (q : Wave n) (i : Fin n) (k) (hk : zoom i q=eigenFee k • q) (d):
    sectorsMass q (parcel (update d i (2*d i))) = ENNReal.ofReal ((2^(2*k):ℝ)) * sectorsMass q (parcel d) := by
    have he := parcel_zoom q d i; rw [hk,sectors_smul,Measure.smul_apply,smul_eq_mul] at he
    suffices hp : (2⁻¹^2:ℝ≥0∞)* ENNReal.ofReal (2^(2*k):ℝ)=ENNReal.ofReal (eigenFee k^2) by
        apply (ENNReal.mul_right_inj (a:= (2⁻¹^2:ℝ≥0∞)) (by simp) (by finiteness)).1
        rw [← mul_assoc,hp,he]
    conv_lhs => lhs; rw [show (2⁻¹^2:ℝ≥0∞)= ENNReal.ofReal ((2:ℝ)⁻¹^2) by rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_inv_of_pos (by positivity)]; norm_num]
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; unfold eigenFee; ring

lemma zero_degree (q : Wave n) (h : Evaporates q) (i : Fin n) (hi : zoom i q=eigenFee 0 • q) : q=0 := by
    apply died; intro j
    let μ := sectorsMass q
    let d := fun _:Fin n=> (2:ℝ)^j
    let V k := parcel (update d i (d i * (2:ℝ)⁻¹^k))
    have hf : V 0=barrel n j := by unfold V barrel; rw [pow_zero,mul_one,update_eq_self]
    have hm k : μ (V (k+1))=μ (V k) := by
       have he := eigen_mass q i 0 hi (update d i (d i * (2:ℝ)⁻¹^(k+1)))
       suffices h : (2:ℝ)* (d i*2⁻¹^(k+1))= d i*2⁻¹^k by simpa only [V,update_self,h,update_idem, Nat.mul_zero,pow_zero,ENNReal.ofReal_one,one_mul] using he.symm
       rw [pow_succ]; ring
    have hp k : μ (V k)=μ (V 0) := by induction k with | zero=> rfl | succ k h=> exact (hm k).trans h
    have hv : Antitone V := antitone_nat_of_succ_le fun k=> parcel_mono (fun p=> by
        by_cases h:p=i
        · subst p; rw [update_self,update_self,pow_succ]; dsimp only [d]; gcongr; exact mul_le_of_le_one_right (by positivity) (by norm_num)
        rw [update_of_ne h,update_of_ne h])
    have hx := tendsto_measure_iInter_atTop (μ:=μ) (s:=V) (fun i=> (parcel_closed _).measurableSet.nullMeasurableSet) hv ⟨0,by rw [hf]; exact (h.cover j).ne⟩
    have hu : μ (V 0)=μ (⋂ i,V i) := tendsto_nhds_unique_of_eventuallyEq (g:=μ∘V) tendsto_const_nhds hx (Eventually.of_forall (fun i=> (hp i).symm))
    have ht : (photons n) (⋂ i,V i)=0 := by
        rw [← compl_mem_ae_iff]
        filter_upwards [photons_nonzero n] with p hh H
        have hd := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)).const_mul (d i)
        rw [mul_zero] at hd
        obtain ⟨k,hk⟩ := (hd.eventually (gt_mem_nhds (hh i))).exists
        have he : ‖p i‖≤_ := (show p∈V k from mem_iInter.mp H _) i; rw [update_self] at he; exact not_lt_of_ge he hk
    rw [← hf]; exact hu.trans (withDensity_absolutelyContinuous _ _ ht)

lemma uniform_eigen (q : Wave n) (v : Fin n→ℕ) (hv : ∀ i, zoom i q=eigenFee (v i) • q) (k : ℕ) :
    sectorsMass q (barrel n k) = ENNReal.ofReal (((2^k:ℝ)^(2 * ∑ i, v i))) * sectorsMass q (barrel n 0) := by
    have fold (s : Finset (Fin n)) (d) :
        let f i := if i∈s then 2*d i else d i
        sectorsMass q (parcel f) = ENNReal.ofReal (2 ^ (2 * ∑ i∈s, v i):ℝ)* sectorsMass q (parcel d) := by
        induction s using Finset.induction_on with
        | empty=> simp
        | @insert i s hi ih=>
            intro f; let g j := if j∈s then 2*d j else d j
            rw [show f= update g i (2*g i) by ext j; by_cases h:j=i <;> simp [f,g,h,hi], eigen_mass q i _ (hv i), ih, Finset.sum_insert hi, Nat.mul_add,pow_add,ENNReal.ofReal_mul (by positivity),mul_assoc]
    induction k with
    | zero => simp
    | succ k ih =>
        let d := fun _ : Fin n=> (2:ℝ)^k
        have he := fold Finset.univ d; dsimp only at he
        rw [show (fun i=> if i∈Finset.univ then 2*d i else d i)=(fun _=>2^(k+1)) by ext i; simp [d,pow_succ,mul_comm]] at he
        change sectorsMass q (barrel n (k+1))=_*sectorsMass q (barrel n k) at he
        rw [he,ih,← mul_assoc,← ENNReal.ofReal_mul (by positivity)]; congr 2; ring

/-- Retreat to engineering ≤3, or zero. Works also for the arity-zero wave. -/
lemma not_tall (q : Wave n) (v : Fin n → ℕ) (hv : ∀ i, zoom i q=eigenFee (v i) • q) (hk : Evaporates q) (hd : 4 ≤ ∑ i,v i) : q=0 := by
    apply died; intro i; rw [uniform_eigen q v hv]
    suffices h : sectorsMass q (barrel n 0)=0 by rw [h,mul_zero]
    apply le_zero_iff.mp; apply ge_of_tendsto hk.top; filter_upwards with i
    rw [uniform_eigen q v hv i,← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    conv_lhs => rw [← one_mul (sectorsMass q _)]
    apply mul_le_mul_left _ _
    rw [ENNReal.one_le_ofReal]
    rw [inv_pow,inv_mul_eq_div,le_div_iff₀ (by positivity),one_mul]; exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)

/-- Width bound useful even when combining different degrees. -/
def width (q : Wave n) := ∃ C : ℝ≥0, ∀ i : ℕ,
    sectorsMass q (barrel n i) ≤ (C:ℝ≥0∞)* ENNReal.ofReal ((2^i:ℝ)^6)

def short (n : ℕ) : Submodule ℝ (Wave n) where
    carrier := { q | (4 ≤ n → q=0) ∧ width q }
    zero_mem' := ⟨fun _=>rfl,⟨0,fun i=> by rw [sectors_zero]; simp⟩⟩
    add_mem' := by
        rintro x y ⟨hx,a,ha⟩ ⟨hy,b,hb⟩
        refine ⟨fun h => by rw [hx h,hy h]; simp, 2*(a+b),fun i=>?_⟩
        apply (sectors_add x y (barrel n i)).trans; rw [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
        apply le_trans (mul_le_mul_right (add_le_add (ha i) (hb i)) _); rw [ENNReal.coe_mul,ENNReal.coe_add,← add_mul,mul_assoc]; norm_num
    smul_mem' := by
        rintro c x ⟨hx,a,h⟩; let v : ℝ≥0:= ⟨c^2,sq_nonneg c⟩
        refine ⟨fun h=>by rw [hx h,smul_zero], v*a,fun i=>?_⟩
        rw [sectors_smul, Measure.smul_apply,smul_eq_mul]; refine (mul_le_mul_right (h i) _).trans_eq ?_
        rw [ENNReal.coe_mul,mul_assoc,← ENNReal.ofReal_coe_nnreal (p:=v)]; rfl

lemma restrict_eigen (k : ℕ) : mainSet (Margin n) Finset.univ k ⊆ (short n : Set (Wave n)) := by
    rintro q ⟨hv,hh⟩
    change Evaporates q at hv; choose g hg h using fun i=> hh i (Finset.mem_univ i)
    by_cases ht : q=0
    · rw [ht]; exact (short n).zero_mem
    have hp (i) : 1 ≤ g i := Nat.pos_of_ne_zero fun H=> ht (zero_degree q hv i (by rw [h,H]))
    have hk : n≤ ∑ i,g i := by simpa using (Finset.sum_le_sum (s:=Finset.univ) fun i _=> hp i)
    have he : ∑ i,g i < 4 := Nat.lt_of_not_ge fun H=> ht (not_tall q g h hv H)
    let C := (sectorsMass q (barrel n 0)).toNNReal
    refine ⟨fun h => by omega,C,fun i=>?_⟩
    rw [uniform_eigen q g h,mul_comm (ENNReal.ofReal _), show (C:ℝ≥0∞)=sectorsMass q (barrel n 0) from ENNReal.coe_toNNReal (hv.cover _).ne]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega))) _

lemma local_eigen (q : Wave n) (h : Evaporates q) {d : ℕ} (hp : tempered q d) (hv : ∀ g : Fin n→Probe E4,(∀ i, Remote (g i)) → paired_at q g=adjoint_at q g) :
    (4 ≤ n → q=0) ∧ width q := by
    obtain ⟨k,hk⟩ := binds q hp hv
    have he:= splitParts (Margin n) Finset.univ k q (show q∈Margin n from h) (fun i _ z hz=> zoom_margin z hz i) (fun i _=>hk i)
    exact (Submodule.span_le.mpr (restrict_eigen k)) he
end YM.TraceExtension.Photons
