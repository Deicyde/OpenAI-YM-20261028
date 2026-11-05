import YM.Extra.SOURCE_HISTORIES.Motion


/-! Staged transfer with the engineering multiplier. Always one History,
real-to-complex and symmetry-accountable (origin-calibrated). -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (H : History G) (N p m d : ℕ)

def liftVac (V : Config G (H.S.side m p)) : ℂ := ((H.rep N p m).eval V:ℝ)

lemma vac_integrable (h : H.Selected) (hp : m≤N) : Integrable (liftVac H N p m) (prior G _) :=
  ((Rep.envelope _ (h.represents N p m hp).good).integrable _).ofReal

lemma vac_transfer (h : H.Selected) (hp : m<N) :
    liftVac H N p m = (H.levels.clock.op m p).push (H.β N p (m+1)) (liftVac H N p (m+1)) := by
  funext V
  unfold liftVac
  rw [(h.steps N p m hp).1]
  let S := H.levels.clock.op m p
  let R := H.rep N p (m+1)
  let F := Complex.ofRealCLM
  have he := F.integral_comp_comm (StepData.push_slice (H.levels.transition_mass m p R.beta) V R.eval
    ((R.envelope (h.represents N p (m+1) hp).good).integrable _))
  change F (S.push R.beta R.eval V) = ∫ U, S.density R.beta U V • F (R.eval U) ∂prior G _
  simp_rw [← F.map_smul]; exact he.symm

/-- `Selected` gives genuine pointwise vacuum symmetry here. -/
lemma vac_pull (h : H.Selected) (hp : m ≤ N) (s : Signed) (t : Site (H.S.side m p)) (U) :
    liftVac H N p m (pull s t U) = liftVac H N p m U := by
  induction hp using Nat.decreasingInduction with
  | self => simp only [liftVac, (h.starts N p).2, bare_pull]
  | of_succ k hk ih =>
    rw [vac_transfer H N p k h hk, ← push_pull H k p _ s t _ (vac_integrable H N p (k+1) h hk)]
    simp_rw [ih]

lemma vac_dance (h : H.Selected) (hp : m ≤ N) (z : Motion) : dance z (liftVac H N p m) = liftVac H N p m := by
  funext U; rw [dance,vac_pull H N p m h hp]; exact scalar_real ..

def blast (f : Config G (H.S.side (m+1) p) → ℂ) := ((H.S.block m).val:ℂ)^d •
  (H.levels.clock.op m p).push (H.β N p (m+1)) f

lemma blast_dance (z : Motion) (f : Config G (H.S.side (m+1) p) → ℂ) (hi : Integrable f (prior G _)) :
    blast H N p m d (dance z f) = dance z (blast H N p m d f) := by
  rw [blast,push_dance H m p _ z f hi]
  funext U
  unfold dance blast; simp only [Pi.smul_apply,smul_eq_mul, scalar_mul]; unfold scalar; split <;> simp

lemma blast_sum {ι : Type*} [Countable ι] {f : ι → Config G (H.S.side (m+1) p) → ℂ}
    (h : Dominated f) (hp : ∀ i, Measurable (f i)) (V : Config G (H.S.side m p)) :
    blast H N p m d (fun U => ∑' i, f i U) V = ∑' i, blast H N p m d (f i) V := by
  unfold blast
  simp only [Pi.smul_apply,smul_eq_mul,tsum_mul_left]
  rw [(push_tsum (H.levels.transition_mass ..) h hp V).tsum_eq]

lemma blast_vac (h : H.Selected) (hp : m<N) : blast H N p m d (liftVac H N p (m+1))=
    ((H.S.block m).val:ℂ)^d • liftVac H N p m := by rw [vac_transfer H N p m h hp]; rfl

/-- Spell actual decay of physical `a^d` from step length. -/
lemma unit_vowel (F : Labels.Frame G d) : vowel F (H.S.block m) (unitVec F H (m+1)) = unitVec F H m := by
  ext i
  unfold vowel unitVec Frame.e0
  by_cases hi : i=0
  · subst i
    simp only [H.S.a_step, Complex.ofReal_div, Complex.ofReal_natCast, F.zero_degree, Nat.sub_zero,
      Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one]
    have hq := show (↑(H.S.block m).val:ℂ) ≠ 0 by exact_mod_cast (H.S.block m).property.ne'
    rw [← mul_pow, mul_div_cancel₀ _ hq]
  simp [Pi.single_eq_of_ne hi]

lemma play_integrable {m d p : ℕ} {F : Labels.Frame G d} {B : SectionData F} {A : Hol G}
    {P : Coefficient F (H.S.side m p)} {o} {t v : ℝ}
    (h : H.Selected) (hp : m≤N) (hP : P.Format o A (H.rep N p m)) (hb : P.remBound o (H.rep N p m) v t) :
    Integrable (P.density o B (H.rep N p m)) (prior G _) := by
  have he := Coefficient.envelope B (h.represents N p m hp).good hb hP
  obtain ⟨c,hc⟩ := he.cost
  exact Integrable.of_bound he.meas.aestronglyMeasurable c (.of_forall hc)

end YM.Extra.Histories
