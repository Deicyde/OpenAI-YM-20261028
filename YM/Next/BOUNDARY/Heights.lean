import YM.Work.C23
import YM.Work.C24


/-!
# Common Chamber, uncorrelated approach heights

Produce vector limits for **joint** Schwartz tests in the same OS Chamber,
using arbitrary (strict positive) heights and admissible insertion widths.
Continuum Bochner integrals with respect to volume on `Points`. The merger reverses the
coordinates used to test the bra, without a reflection of their real times,
and the bra test is conjugated. Gram in the two heights is a FULL product
limit (including empty sides). Convergence of these smeared heat vectors is
in Hilbert norm. No claim of an algebraic field domain containing all joint
test vectors. No claim of convergence in operator norm on the tests.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory
open Boundary OS
open scoped Topology InnerProductSpace BigOperators NNReal ContDiff

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber T timeAxis}
variable {n m : ℕ} {B : Small S V} {Y : Waves S} {W : Surface S} {J : StarOp S}

/-- `p∈(0,1)`, heights positive strictly ascending with *all* heights and
pairwise (forward) gaps > 4p. For n=0 this STILL restricts p to `(0,1)`,
heights impose nothing. -/
def margins (n : ℕ) : Set (ℝ≥0 × Heights n) :=
  {x | x.2∈positiveHeight n ∧ Small.ample x.1 x.2}



/-- y -> 0 within the margins. No other restriction, e.g. ratios, or p
as function of y. -/
def edgeFilter (n : ℕ) : Filter (ℝ≥0 × Heights n) :=
  comap Prod.snd (𝓝 (0:Heights n)) ⊓ 𝓟 (margins n)

lemma heights_zero (n : ℕ) : Tendsto Prod.snd (edgeFilter n) (𝓝 (0:Heights n)) :=
  tendsto_comap.mono_left inf_le_left

lemma heights_valid (n : ℕ) : ∀ᶠ x in edgeFilter n, x∈margins n := mem_inf_of_right (by simp)

lemma profile_edge (n : ℕ) :
    Tendsto (fun t => (Small.logD t, Small.profile t n)) till (edgeFilter n) := by
  apply tendsto_inf.mpr
  refine ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · apply tendsto_pi_nhds.mpr
    intro i
    have he := (tendsto_id.mono_left (nhdsWithin_le_nhds (a:=0) (s:=Ioi (0:ℝ)))).const_mul ((i.val:ℝ) + 1)
    simpa only [mul_zero] using! he
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ⟨Small.imminent ht, Small.suitable ht⟩

lemma edge_nontrivial (n : ℕ) : (edgeFilter n).NeBot := (profile_edge n).neBot

lemma doubled_corner (n m : ℕ) :
    Tendsto (fun q => Bid.bothH q.1.2 q.2.2) (edgeFilter n ×ˢ edgeFilter m)
      (𝓝[east (n+m)] 0) := by
  have he : Tendsto (fun q => Bid.bothH q.1.2 q.2.2)
      (edgeFilter n ×ˢ edgeFilter m) (𝓝 (0:Heights (n+m))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [comp_apply, Bid.bothH, Fin.append_left, Pi.zero_apply, neg_zero] using!
        (tendsto_pi_nhds.mp ((heights_zero n).comp (tendsto_fst (g:=edgeFilter m))) j.rev).neg
    intro j
    simpa only [comp_apply, Bid.bothH, Fin.append_right, Pi.zero_apply] using!
      (tendsto_pi_nhds.mp ((heights_zero m).comp (tendsto_snd (f:=edgeFilter n))) j)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨he, ?_⟩
  filter_upwards [tendsto_fst.eventually (heights_valid n), tendsto_snd.eventually (heights_valid m)]
    with q h g
  exact Work.C24.ordered h.1 g.1

/-- Adjacent test blocks: reversed in the first coordinates, test conjugated
**once** in the first factor; same Lebesgue orientations. -/
def joinedTest (f : Joint n) (g : Joint m) : Joint (n+m) :=
  Probe.along Work.C24.merger.symm (Probe.combine (Probe.bar f) g)

lemma joinedTest_at (f : Joint n) (g : Joint m) (x : Points n) (y : Points m) :
    joinedTest f g (Bid.bothP x y)=star (f x)*g y := by
  change joinedTest f g (Work.C24.merger (x, y))=_
  simp [joinedTest]

theorem joinedTest_cont (n m : ℕ) :
    Continuous (fun p : Joint n × Joint m => joinedTest p.1 p.2) := by
  exact (Probe.along _).continuous.comp
    (Probe.normCont.comp ((Probe.bar.continuous.comp continuous_fst).prodMk continuous_snd))

/-- Joint Schwartz smearing of the actual heat recipe. No complex-time
polytope sign change: uses `Small.shot` verbatim. -/
def hot (B : Small S V) (v : Fin n → S.Union) (f : Joint n) (q : ℝ≥0 × Heights n) :=
  ∫ x : Points n, f x • B.shot q.1 n v q.2 x

lemma hot_int (B : Small S V) (v : Fin n → S.Union) (f : Joint n) {q : ℝ≥0 × Heights n}
    (h : q∈margins n) : Integrable (fun x => f x • B.shot q.1 n v q.2 x) :=
  Work.C23.shot_int B q.1 v q.2 f h.2

/-- Hot Gram formula with all spectator variables tested jointly. Compare
Work.C24.integrated (one real profile parameter per block, product tests). -/
theorem hot_pair (h : Bid.Hull B Y J) (int : Y.NonTangentialFree W)
    (v : Fin n → S.Union) (w : Fin m → S.Union) (f : Joint n) (g : Joint m)
    (q : ℝ≥0 × Heights n) (p : ℝ≥0 × Heights m) (hq : q∈margins n) (hp : p∈margins m) :
    inner ℂ (hot B v f q) (hot B w g p) = ∫ x,
      Y.restricted (Bid.bothT v w J) (Bid.bothH q.2 p.2) x * joinedTest f g x := by
  let z := fun x : Points (n+m) =>
    Y.restricted (Bid.bothT v w J) (Bid.bothH q.2 p.2) x * joinedTest f g x
  let e := Work.C24.merger (n:=n) (m:=m)
  have hi : Integrable (z ∘ e) :=
    (Work.C24.preserves.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr
      (int.int _ _ _ (Work.C24.ordered hq.1 hp.1) _)
  calc
    _ = ∫ x : Points n, ∫ y : Points m, (z ∘ e) (x, y) := by
      rw [hot, ← inner_conj_symm, ← integral_inner (hot_int B v f hq), ← integral_conj]
      apply integral_congr_ae; filter_upwards with x
      rw [inner_conj_symm, hot, ← integral_inner (hot_int B w g hp)]
      apply integral_congr_ae; filter_upwards with y
      change inner ℂ (_ • B.shot q.1 n v q.2 x) (_ • B.shot p.1 m w p.2 y) = z (Bid.bothP x y)
      rw [inner_smul_left, inner_smul_right, h.join _ _ _ _ _ _ _ _ hq.1 hp.1 hq.2 hp.2]
      dsimp only [z]
      rw [joinedTest_at]
      change _ = _ * ((starRingEnd ℂ) (f x) * g y)
      ring
    _ = ∫ u, (z ∘ e) u ∂(volume.prod volume) := (integral_prod _ hi).symm
    _ = ∫ x, z x := Work.C24.preserves.integral_comp e.toHomeomorph.measurableEmbedding z



theorem hot_inner (h : Bid.Hull B Y J) (int : Y.NonTangentialFree W)
    (v : Fin n → S.Union) (w : Fin m → S.Union) (f : Joint n) (g : Joint m) :
    Tendsto (fun q => inner ℂ (hot B v f q.1) (hot B w g q.2)) (edgeFilter n ×ˢ edgeFilter m)
      (𝓝 (W.W (n+m) (Bid.bothT v w J) (joinedTest f g))) := by
  refine ((int.corner (n+m) (Bid.bothT v w J) (joinedTest f g)).comp (doubled_corner n m)).congr' ?_
  filter_upwards [tendsto_fst.eventually (heights_valid n), tendsto_snd.eventually (heights_valid m)]
    with q hq hp
  exact (hot_pair h int v w f g q.1 q.2 hq hp).symm

-- `Boundary.norms_kernel` with arbitrary net of positive profiles
theorem vector_limit {α : Type*} {R : Filter α} [R.NeBot] (X : Hilbert) (f : α → X)
    (z : ℂ) (h : Tendsto (fun q => inner ℂ (f q.1) (f q.2)) (R ×ˢ R) (𝓝 z)) :
    ∃ x, Tendsto f R (𝓝 x) := by
  have hn : Tendsto (fun q => ⟪f q.1, f q.1⟫_ℂ) (R ×ˢ R) (𝓝 z) := h.comp (tendsto_fst.prodMk tendsto_fst)
  have hp : Tendsto (fun q => ⟪f q.2, f q.2⟫_ℂ) (R ×ˢ R) (𝓝 z) := h.comp (tendsto_snd.prodMk tendsto_snd)
  have hc : Tendsto (fun q => ⟪f q.2, f q.1⟫_ℂ) (R ×ˢ R) (𝓝 z) := h.comp (tendsto_snd.prodMk tendsto_fst)
  have he : Tendsto (fun q => inner ℂ (f q.1-f q.2) (f q.1-f q.2)) (R ×ˢ R) (𝓝 0) := by
    simp_rw [inner_sub_right,inner_sub_left]
    simpa only [sub_self] using! (hn.sub hc).sub (h.sub hp)
  apply cauchy_map_iff_exists_tendsto.mp (cauchy_map_iff'.mpr (tendsto_uniformity_iff_dist_tendsto_zero.mpr ?_))
  change Tendsto (fun p => dist (f p.1) (f p.2)) (R ×ˢ R) (𝓝 0)
  simp_rw [dist_eq_norm, @norm_eq_sqrt_re_inner ℂ]
  simpa using!
    (Real.continuous_sqrt.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp he))

theorem limiting_pair (h : Bid.Hull B Y J) (int : Y.NonTangentialFree W)
    (v : Fin n → S.Union) (w : Fin m → S.Union) (f : Joint n) (g : Joint m) (x y : V.H)
    (hx : Tendsto (hot B v f) (edgeFilter n) (𝓝 x)) (hy : Tendsto (hot B w g) (edgeFilter m) (𝓝 y)) :
    inner ℂ x y = W.W (n+m) (Bid.bothT v w J) (joinedTest f g) := by
  haveI := edge_nontrivial n
  haveI := edge_nontrivial m
  exact tendsto_nhds_unique ((hx.comp tendsto_fst).inner (hy.comp tendsto_snd)) (hot_inner h int v w f g)

theorem heated (h : Bid.Hull B Y J) (int : Y.NonTangentialFree W) (v : Fin n → S.Union) :
    ∃! U : Joint n →L[ℂ] V.H, ∀ f : Joint n, Tendsto (hot B v f) (edgeFilter n) (𝓝 (U f)) := by
  haveI := edge_nontrivial n
  choose F hf using fun f : Joint n => vector_limit V.H _ _ (hot_inner h int v v f f)
  have add (f g) : F (f+g)=F f+F g := by
    refine tendsto_nhds_unique_of_eventuallyEq (hf _) ((hf f).add (hf g)) ?_
    filter_upwards [heights_valid n] with i hi
    unfold hot
    simp only [_root_.add_apply, add_smul]
    rw [integral_add (hot_int B v f hi) (hot_int B v g hi)]
  have scale (t : ℂ) (f) : F (t • f)=t • F f := by
    refine tendsto_nhds_unique_of_eventuallyEq (hf _) (tendsto_const_nhds.smul (hf f)) ?_
    filter_upwards [heights_valid n] with i _
    unfold hot
    simp only [_root_.smul_apply, smul_eq_mul, mul_smul, integral_smul]
  have H (f g) := limiting_pair h int v v f g (F f) (F g) (hf f) (hf g)
  have he : Continuous F := by
    refine continuous_iff_continuousAt.mpr (fun f => ketC (D := V.H) F f ?_ ?_)
    · simp_rw [H]
      exact ((W.W _ _).continuous.comp
        ((joinedTest_cont n n).comp (continuous_id.prodMk continuous_id))).continuousAt
    simp_rw [H]
    exact ((W.W _ _).continuous.comp
      ((joinedTest_cont n n).comp (continuous_const.prodMk continuous_id))).continuousAt
  refine ⟨⟨⟨⟨F, add⟩, scale⟩, he⟩, hf, fun g hg => ?_⟩
  ext1 f
  exact tendsto_nhds_unique (hg f) (hf f)

/-- Ordered multiplication word in the field domain. Empty input gives the
empty word, not a constant operator assumption. -/
def tensorWord (v : Fin n → S.Union) (f : Fin n → Test4) : Sentence S := List.ofFn fun i => (v i, f i)

lemma hot_profile (B : Small S V) (v : Fin n → S.Union) (f : Fin n → Test4) (t : ℝ) :
    hot B v (Joint.materialize n f) (Small.logD t, Small.profile t n)=B.heatCup (tensorWord v f) t := by
  rw [Work.C23.heatCup_n B _ t n (by simp [tensorWord])]
  simp [tensorWord, hot]
end YM.Next.BOUNDARY
