import Mathlib.Analysis.Matrix.Order
import YM.Branch.Covariant
import YM.Next.UV_STRESS.Product
import YM.Slice.Levels




/-!
# Use the same fine→coarse RG kernel as the history

Expose site tags from the density, integrate bond choices exactly. Pullback
shorthand for conditional averages against this kernel for observables. True
expectation for the bounded measurable functions we use below; conveyor at
fixed β and side. No conditional independence assertion with shared tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory  Lattice Wilson RG Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}

lemma borel_bounded {s : Set (Site c)} {F : Config G c → ℂ} (hp : Interior s F) : Envelope F := ⟨hp.borel,hp.cost⟩

lemma prior_int {F : Config G c→ℂ} (hp : Envelope F) : Integrable F (prior G c) :=
  Integrable.of_bound hp.meas.aestronglyMeasurable hp.cost.choose (Eventually.of_forall hp.cost.choose_spec)

variable (S : StepData c f)

def back (β : ℝ) (F : Config G c → ℂ) (U : Config G f) := ∫ x : Config G c, S.density β U x • F x ∂prior G c

section Budget
variable {B : Config G c→ℂ} (hB : Envelope B) (H : S.patch.Branches S.kernel G) (β : ℝ)

include hB H
lemma pull_int (U : Config G f) : Integrable (fun x : Config G c => S.density β U x • B x) (prior G c) := by
  have he := S.isKernel H β
  obtain ⟨M,hM⟩ := he.bound
  have hh : Measurable fun x => S.density β U x :=
    (show Measurable ((fun p : Config G f × Config G c => S.density β p.1 p.2) ∘ fun x : Config G c => (U,x)) from
      he.meas.comp (measurable_const.prodMk measurable_id))
  have hp x : ‖S.density β U x‖ ≤ M := (Real.norm_of_nonneg (he.positive U x)).trans_le (hM U x)
  apply (prior_int hB).bdd_smul M hh.aestronglyMeasurable
  exact Eventually.of_forall hp

omit hB in
lemma keeps_bound (M : ℝ) (hp : ∀ x, ‖B x‖ ≤ M) (U : Config G f) : ‖back S β B U‖ ≤ M := by
  calc
    _ ≤ ∫ x : Config G c, S.density β U x * M ∂prior G c :=
      norm_integral_le_of_norm_le (((S.isKernel H _).integrable U).mul_const M) (ae_of_all _ fun x => by
        rw [norm_smul, Real.norm_of_nonneg ((S.isKernel H β).positive U x)]
        exact mul_le_mul_of_nonneg_left (hp _) ((S.isKernel H _).positive U x))
    _ = M := by rw [integral_mul_const,(S.isKernel H _).total,one_mul]

lemma pulled : Envelope (back S β B) := by
  constructor
  · have ht : Measurable (fun u : Config G f × Config G c => S.density β u.1 u.2 • B u.2) :=
      (S.isKernel H β).meas.smul (hB.meas.comp measurable_snd)
    exact ht.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨M,hM⟩ := hB.cost
  exact ⟨M,keeps_bound S H β M hM⟩

lemma transfer_gauge (hp : GaugeInvariant B) : GaugeInvariant (back S β B) := by
  intro g x
  let t : Site c → G.El := g ∘ S.ratio.embed
  let F := fun y : Config G c => S.density β (Lattice.gauge g x) y • B y
  have h := prior_gauge t
  have hv := integral_map (f := F) h.aemeasurable (by rw [h.map_eq]; exact (pull_int S hB H ..).aestronglyMeasurable)
  rw [h.map_eq] at hv
  unfold back; rw [hv]
  apply integral_congr_ae
  filter_upwards with y
  rw [show F (Lattice.gauge t y)=S.density β _ (Lattice.gauge t y) • B (Lattice.gauge t y) from rfl,S.covary H,hp]

lemma transfer_shift (k : Signed) (s : Site c) : back S β (B ∘ pull k s)=back S β B ∘ pull k (S.ratio.embed s) := by
  funext U
  let F := fun y => S.density β (pull k (S.ratio.embed s) U) y • B y
  have hp := prior_pull (G:=G) k s
  have he := integral_map (f:=F) hp.aemeasurable (by rw [hp.map_eq]; exact (pull_int S hB H ..).aestronglyMeasurable)
  rw [hp.map_eq] at he
  change _=∫ y,F y ∂prior G c
  rw [he]
  unfold back; apply integral_congr_ae; filter_upwards with y
  unfold F; rw [S.channel H]; rfl

omit H hB in
lemma conjugate_back (B : Config G c → ℂ) : back S β (fun x => star (B x))=fun x => star (back S β B x) := by
  funext x; unfold back
  simp only [Complex.star_def, Complex.real_smul]
  rw [← integral_conj]; simp
end Budget

-- Factor before taking F-sums
section tags
variable (β : ℝ) (U : Config G f) (t : S.SitesChoice)

def fees (e : Edge (Site c)) (z : G.El) : ℂ :=
  ∑ k : S.patch.Points, (↑(S.patch.predictorMass S.kernel (S.connector U t e) k * ((S.penaltyZ β G)⁻¹ *
    S.penaltyWeight β (z*(S.patch.predict S.kernel (S.connector U t e) k)⁻¹))) : ℂ)

def channels (x : Site c) (t : S.patch.FrameTag) : ℂ := ↑(S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) t)

def sourced (V : Config G c) : ℂ := (∏ i : Site c, channels S U i (t i)) * ∏ i, fees S β U t i (V i)

lemma gathered (V : Config G c) : (S.density β U V:ℂ) = ∑ t, sourced S β U t V := by
  unfold StepData.density; rw [Fintype.sum_prod_type]; push_cast; apply Finset.sum_congr rfl; intro t _
  unfold sourced fees
  rw [Fintype.prod_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
  unfold StepData.likelihood StepData.noise StepData.prediction channels; push_cast
  rw [mul_assoc,← Finset.prod_mul_distrib]

lemma fees_cont (i : Edge (Site c)) : Continuous (fees S β U t i) := by
  unfold fees; apply continuous_finsetSum; intro j _
  exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.mul
    ((S.penaltyWeight_cont β).comp (continuous_id.mul continuous_const))))

lemma sourced_cont : Continuous (sourced S β U t) := by
  unfold sourced
  exact continuous_const.mul (continuous_finsetProd _ fun i _ => (fees_cont S ..).comp (continuous_apply i))

lemma channels_mass (h : S.patch.Branches S.kernel G) (i : Site c) : ∑ j, channels S U i j=1 := by
  unfold channels; rw [← Complex.ofReal_sum,S.patch.frameMass_sum h]; rfl

lemma fees_total (i : Edge (Site c)) : (∫ z, fees S β U t i z ∂G.probHaar)=1 := by
  let L := S.patch.predictorMass S.kernel (S.connector U t i)
  let J := S.patch.predict S.kernel (S.connector U t i)
  let F (p : S.patch.Points) z := L p * ((S.penaltyZ β G)⁻¹ * S.penaltyWeight β (z*(J p)⁻¹))
  have hc p : Continuous (F p) := continuous_const.mul (continuous_const.mul
    ((S.penaltyWeight_cont β).comp (continuous_id.mul continuous_const)))
  have ht p : (∫ z, F p z ∂G.probHaar) = L p := by
    have hh := (measurePreserving_mul_right G.probHaar (J p)⁻¹).integral_comp
      (Homeomorph.mulRight (J p)⁻¹).measurableEmbedding (S.penaltyWeight β)
    unfold F; rw [integral_const_mul,integral_const_mul,hh,← StepData.penaltyZ,inv_mul_cancel₀ (S.penaltyZ_pos _).ne',mul_one]
  have hh p : (∫ z, (↑(F p z):ℂ) ∂G.probHaar)=L p := by rw [integral_complex_ofReal,ht]
  change (∫ z, (∑ p, (↑(F p z):ℂ))∂G.probHaar)=1
  have hp p : Integrable (fun z => (↑(F p z):ℂ)) G.probHaar :=
    (Complex.continuous_ofReal.comp (hc p)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun p _ => hp p)]; simp_rw [hh]; rw [← Complex.ofReal_sum,show ∑ p,L p=1 from S.patch.predictorMass_sum ..]; rfl



lemma scanned_back (F : Config G c→ℂ) (hp : Envelope F) : back S β F U=scanning (channels S U)
    (fun t => scatter G.probHaar (fees S β U t) F) := by
  unfold back scanning; simp_rw [Complex.real_smul,gathered S β U,Finset.sum_mul]
  have h t : Integrable (fun V => sourced S β U t V * F V) (prior G c) := by
    obtain ⟨C,H⟩ := (sourced_cont S β U t).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    exact (prior_int hp).bdd_smul _ (sourced_cont _ _ _ _).aestronglyMeasurable (Eventually.of_forall H)
  rw [integral_finsetSum _ (fun i _ => h i)]; apply Finset.sum_congr rfl; intro i _
  simp_rw [sourced,mul_assoc,integral_const_mul]; rfl
end tags
end YM.Next.UVStress
