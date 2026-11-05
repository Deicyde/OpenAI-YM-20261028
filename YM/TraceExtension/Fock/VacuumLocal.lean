import YM.TraceExtension.Fock.Weight
import YM.TraceExtension.Fock.Transverse
import YM.TraceExtension.LogScaling
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! The vacuum locality consequence in relative position variables. Use a
shrinking *single* trace region. No condition on relative separations of
two electric-field tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff
section
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

def bump : ContDiffBump (0:V) := ⟨1,2,by norm_num,by norm_num⟩
def petal : Probe V := (((bump V).hasCompactSupport_normed (μ:=volume)).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (ContDiffBump.contDiff_normed ..))
def atom (s : ℝ) := condense s (petal V)
lemma atom_real {s : ℝ} (hp : 0<s) : Probe.bar (atom V s)=atom V s := by
    ext x; unfold atom; rw [Probe.bar_at,condense_eval s hp]; change star ((s^Module.finrank ℝ V:ℝ) • ((↑((bump V).normed volume (s • x)):ℂ))) = _; simp [hp.ne']; rfl
lemma atom_small {r : ℝ} (hr : 0<r) : ∀ᶠ s : ℝ in atTop, tsupport (atom V s) ⊆ ball 0 r ∧ HasCompactSupport ⇑(atom V s) := by
    filter_upwards [eventually_gt_atTop 0,eventually_gt_atTop (2/r)] with s hs hx
    have he : tsupport (atom V s) ⊆ closedBall 0 (2/s) := by
        apply closure_minimal ?_ isClosed_closedBall; intro p hp; rw [mem_closedBall,dist_zero_right,le_div_iff₀ hs]; by_contra! h
        apply hp; unfold atom; rw [condense_eval s hs];
        suffices hh : s • p ∉ tsupport (petal V) by rw [image_eq_zero_of_notMem_tsupport hh,smul_zero]
        intro ht
        have hh := (tsupport_comp_subset Complex.ofReal_zero _ ht)
        change s • p ∈ tsupport ((bump V).normed volume) at hh
        rw [ContDiffBump.tsupport_normed_eq, mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le] at hh
        exact not_lt_of_ge hh (mul_comm ‖p‖ s ▸ h)
    exact ⟨he.trans (closedBall_subset_ball ((div_lt_iff₀ hs).2 (by linarith [(div_lt_iff₀ hr).mp hx]))), (isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _) he⟩
lemma atom_delta (p : V) : Tendsto (fun s : ℝ=> testPlus (atom V s) p) atTop (𝓝 1) := by
    have he : testPlus (petal V) 0=1 := by
        rw [testPlus_apply]; simp_rw [Probe.plane_zero,one_mul]
        change (∫ x,↑((bump V).normed volume x))=(1:ℂ); rw [integral_complex_ofReal,ContDiffBump.integral_normed]; rfl
    have hx := (testPlus (petal V)).continuous.tendsto 0
    rw [he] at hx
    have ht := tendsto_inv_atTop_zero (𝕜:=ℝ) |>.smul_const p
    rw [zero_smul] at ht; apply (hx.comp ht).congr'
    exact Eventually.mono (eventually_gt_atTop (0:ℝ)) fun s hs=> (condense_plus s hs ..).symm
lemma atom_bound (s : ℝ) (hp : 0<s) : ∀ q, ‖testPlus (atom V s) q‖≤1 := by
    intro q; unfold atom; rw [condense_plus s hp, testPlus_apply]; apply (norm_integral_le_of_norm_le ((bump V).integrable_normed
       ) ?_).trans (ContDiffBump.integral_normed _).le
    filter_upwards with x; rw [norm_mul, Probe.plane_norm,one_mul]; change ‖(↑((bump V).normed volume x):ℂ)‖≤_; rw [Complex.norm_real,Real.norm_of_nonneg ((bump V).nonneg_normed ..)]

end
variable {m n d : ℕ}

def front (f : Probe E4) (x : Space3) := (↑‖x‖:ℂ) * f (momentum x)
def frontList (f : Fin n→ Probe E4) (x : Mom n) := ∏ i, front (f i) (x i)
lemma front_bound (f : Probe E4) (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖front f x‖ ≤ C*(env d x)⁻¹ := by
    obtain ⟨C,hC,hf⟩ := schwartz_bound f (d+1); refine ⟨C,hC,fun x => ?_⟩
    unfold front env
    have he : ‖x‖≤ ‖momentum x‖ := by
       have he := Mink.squares (momentum x); rw [momentum_space,momentum_energy] at he; nlinarith [norm_nonneg x,norm_nonneg (momentum x)]
    calc ‖_ * _‖ = ‖x‖ * ‖f (momentum x)‖ := by simp
         _ ≤ _ := (mul_le_mul (le_add_of_nonneg_left (show (0:ℝ)≤1 from zero_le_one)) (hf _) (norm_nonneg _) (by positivity)).trans ?_
    calc
       _ ≤ (1+‖x‖)*(C*((1+‖x‖)^(d+1))⁻¹) := by gcongr
       _ = _ := by rw [pow_succ]; field_simp

lemma front_int (q : Wave n) (h : tempered q d) (f : Fin n→ Probe E4) : Integrable (fun k => q k*frontList f k) (photons n) := by
    choose C hC hv using fun i=> front_bound (f i) (d+2)
    have he (k : Mom n) : ‖frontList f k‖ ≤ (shield (d+2) k)⁻¹*∏ i,C i := by
        unfold frontList; rw [norm_prod]; apply (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>hv i (k i))).trans_eq
        rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,mul_comm]; rfl
    apply ((austere q h).mul_const (∏ i, C i)).mono' ((wave_meas q).aestronglyMeasurable.mul
      (show Continuous (frontList f) from by unfold frontList front; fun_prop).aestronglyMeasurable)
    filter_upwards with i; change ‖q i*frontList f i‖ ≤ _; rw [norm_mul,mul_assoc]; gcongr; exact he _

lemma neg_side {K : Set E4} (h : IsCompact K) (hs : K ⊆ spacelike) :
    ∃ r:ℝ, 0<r ∧ ∀ x∈ball (0:E4) r, ∀ y∈K, x-y∈spacelike := by
    let W := {p : E4 × E4 | p.1-p.2 ∈ spacelike}; have he : IsOpen W := open_spacelike.preimage (continuous_fst.sub continuous_snd)
    obtain ⟨u,v,hu,hv,ha,hb,hW⟩ := generalized_tube_lemma (isCompact_singleton (x:=(0:E4))) h he (by
      rintro ⟨x,y⟩ ⟨hx,hy⟩
      change x-y∈spacelike; rw [show x=0 from hx,zero_sub]; apply (Mink.lateral _).2; simpa using (Mink.lateral _).1 (hs hy))
    obtain ⟨r,hp,hr⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (ha (mem_singleton _)))
    exact ⟨r,hp,fun x hx y hy => hW (show (x,y) ∈ u ×ˢ v from ⟨hr hx,hb hy⟩)⟩

def Remote (f : Probe E4) := HasCompactSupport ⇑f ∧ tsupport f ⊆ spacelike
def paired_at (q : Wave n) (g : Fin n→ Probe E4) :=
    (∫ p,q p * frontList (Probe.hat ∘ g) p ∂photons n)
def adjoint_at (q : Wave n) (g : Fin n→ Probe E4) :=
    (∫ p,star (q p) * frontList (testPlus ∘ g) p ∂photons n)

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m}
    (X : Comparison F U) (hL : LocalTest F U) (hp : TraceSpectrum F μ) (Y : Form F U)

include X hL hp
lemma local_position (s : Tags m n) (g : Fin n→ Probe E4) (hc : ∀ i, Remote (g i)) :
    paired_at (Y.wave ⟨n,s⟩) g=adjoint_at (Y.wave ⟨n,s⟩) g := by
    obtain ⟨r,hR,hr⟩ := hL
    let i : Index m := ⟨n,s⟩; let q:=Y.wave i; obtain ⟨d,hD⟩ := Y.surface X hp i
    let f := atom E4
    have he (j : Fin n) : ∀ᶠ k in atTop, Fields.causal (f k) (g j) := by
        obtain ⟨t,ht,h⟩ := neg_side (hc j).1 (hc j).2; exact (atom_small E4 ht).mono fun k hp => fun x hx y hy => h x (hp.1 hx) y hy
    let L := frontList (Probe.hat ∘ g); let R := frontList (testPlus ∘ g)
    let w k p := testPlus (f k) (totalMomentum (n:=n) p)
    let Z (k : ℝ) (p) := w k p * q p
    have hz (k) : sectionFn (signal F U (f k)) i =ᵐ[photons n] Z k := by
        filter_upwards [(sum_ae (m:=m) _).1 (Y.means (f k)) i,Y.val_wave i] with j hk hp
        change signal F U _ _ = _ * Y.wave i j; change signal F U _ _ = _ at hk
        rw [hk,hp]; rfl
    have hw (p : Mom n) : Tendsto (fun k => Z k p) atTop (𝓝 (q p)) := by
       simpa only [one_mul] using (atom_delta E4 (totalMomentum p)).mul_const (q p)
    have hk (k : ℝ) : Measurable (Z k) := (((testPlus (f k)).continuous.comp total_cont).measurable).mul (wave_meas q)
    have hb (k : ℝ) (h:0<k) (p : Mom n) : ‖Z k p‖≤ ‖q p‖ := by
        unfold Z; rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (atom_bound E4 k h _)
    have hl := (front_int q hD (Probe.hat ∘ g)).norm
    have hu := (front_int q hD (testPlus ∘ g)).norm
    let A k p := Z k p * L p; let B k p := star (Z k p) * R p
    have hcL : Continuous L := by unfold L frontList front; fun_prop
    have hcR : Continuous R := by unfold R frontList front; fun_prop
    have hy : Tendsto (fun k => ∫ p,A k p ∂photons n) atTop (𝓝 (paired_at q g)) := by
        apply tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall (fun k => ((hk k).mul hcL.measurable).aestronglyMeasurable)) _ hl
          (ae_of_all _ fun p => (hw p).mul_const (L p))
        filter_upwards [eventually_gt_atTop 0] with k hp; filter_upwards with p
        change ‖Z k p * L p‖≤ ‖q p*L p‖; rw [norm_mul (Z k p), norm_mul (q p)]; exact mul_le_mul_of_nonneg_right (hb k hp p) (norm_nonneg (L p))
    have hy' : Tendsto (fun k => ∫ p,B k p ∂photons n) atTop (𝓝 (adjoint_at q g)) := by
        apply tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall (fun k => ((continuous_star.measurable.comp (hk k)).mul hcR.measurable).aestronglyMeasurable)) _ hu
          (ae_of_all _ fun p => (hw p).star.mul_const (R p))
        filter_upwards [eventually_gt_atTop 0] with k hp; filter_upwards with p
        change ‖star (Z k p)*R p‖≤ ‖q p * R p‖; rw [norm_mul (star (Z k p)),norm_mul (q p),norm_star]; exact mul_le_mul_of_nonneg_right (hb k hp p) (norm_nonneg (R p))
    apply tendsto_nhds_unique_of_eventuallyEq hy hy'
    filter_upwards [eventually_all.mpr he, atom_small E4 hR,eventually_gt_atTop 0] with k he hh hP
    let T := signal F U (f k); have hp : PhysicalWave T:= X.ambient _
    have hq : OnVac (f k) T T := by
       have hz := hr (f k) hh.2 hh.1
       rwa [show Probe.bar (f k)=f k from atom_real E4 hP] at hz
    have hx := positioned (f k) T T hp hp hq s g (fun i => (hc i).1) he
    calc
      _ = ∫ p,sectionFn T i p * L p ∂photons n := integral_congr_ae ((hz k).symm.mul EventuallyEq.rfl)
      _ = ∫ p, star (sectionFn T i p) * R p ∂photons n := hx
      _ = _ := integral_congr_ae ((hz k).star.mul EventuallyEq.rfl)
end YM.TraceExtension.Photons
