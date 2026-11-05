import YM.Next.BOUNDARY.Stage
/-!
Joint Schwartz tests of compact frequency support. With these one can
recover the very hot OS vectors, not only their limits: in the Gram
formula, including at partial boundaries, simply tilt the Fourier-side
tests. This uses the full joint temperateness and the full spectrum
support; no density assertion in a spectral analytic-vector topology.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter MeasureTheory Measure Boundary Probe Next.BOUNDARY
open scoped Topology NNReal InnerProductSpace ContDiff

variable {n m : ℕ}

def reversed (f : Joint n) : Joint n := along (ContinuousLinearEquiv.neg ℝ) f
@[simp] lemma reversed_at (f : Joint n) (x) : reversed f x=f (-x) := rfl

lemma plane_mul_integrable (x : Points n) (f : Joint n) : Integrable (fun q => plane q x*f q) :=
  f.integrable.mono ((plane_cont.comp (continuous_id.prodMk (continuous_const (y:=x)))).mul f.continuous).aestronglyMeasurable
    (ae_of_all _ fun i => by simp)

lemma hat_bra (x : Points n) (f : Joint n) : hat (bar (reversed f)) x=star (hat f x) := by
  rw [hat_eq,hat_eq]
  letI : (volume : Measure (Points n)).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Points n ≃ₗᵢ[ℝ] Points n).measurePreserving.map_eq⟩
  rw [← integral_neg_eq_self (fun q : Points n => plane q (-x) * f q)]
  change _=(starRingEnd ℂ) _; rw [← integral_conj]
  apply integral_congr_ae; filter_upwards with i
  simp only [bar_at,reversed_at,map_mul]
  change plane i (-x) * _ = star (plane (-i) (-x)) * star _
  rw [show plane (-i) (-x)=plane i x by simp [plane], plane_inverse]

open Work.C24
lemma merged_inner (x y : Points n) (p q : Points m) :
    inner ℝ (Bid.bothP x p) (Bid.bothP y q)=inner ℝ x y + inner ℝ p q := by
  change inner ℝ (glue (WithLp.toLp 2 (x,p))) (glue (WithLp.toLp 2 (y,q))) = _
  rw [LinearIsometryEquiv.inner_map_map]; rfl
lemma split_plane (x u : Points n) (p v : Points m) :
    plane (Bid.bothP x p) (-(Bid.bothP u v))= plane x (-u)*plane p (-v) := by
  unfold plane; rw [inner_neg_right,merged_inner]
  rw [inner_neg_right,inner_neg_right,neg_add,Complex.ofReal_add,add_mul,Complex.exp_add]

lemma joined_fourier (f : Joint n) (g : Joint m) :
    hat (joinedTest (reversed f) g) = joinedTest (hat f) (hat g) := by
  ext1 r
  obtain ⟨⟨x,p⟩,rfl⟩ := (merger (n:=n) (m:=m)).surjective r
  let B (i : Points (n+m)) := plane i (-Bid.bothP x p)*joinedTest (reversed f) g i
  let A (i : Points n) := plane i (-x) * (bar (reversed f)) i
  let C (i : Points m) := plane i (-p) * g i
  have hp : B ∘ merger = fun u : Points n × Points m => A u.1 * C u.2 := by
    funext u
    change plane _ _ * joinedTest (reversed f) g (Bid.bothP u.1 u.2)=_
    rw [joinedTest_at]
    change plane (Bid.bothP u.1 u.2) _ * (bar (reversed f) u.1*g u.2)=_
    rw [split_plane]; unfold A C; ring
  rw [hat_eq]
  change (∫ q, B q) = joinedTest (hat f) (hat g) (Bid.bothP x p)
  rw [joinedTest_at,← hat_bra,hat_eq,hat_eq,← preserves.integral_comp merger.toHomeomorph.measurableEmbedding B]
  change (∫ q : Points n × Points m, (B ∘ merger) q ∂(volume.prod volume)) = (∫ q, A q)*(∫ q, C q)
  rw [hp,integral_prod_mul]

lemma merge_height (x : Heights n) (y : Heights m) : dawn (Bid.bothH x y)=Bid.bothP (-dawn x) (dawn y) := by
  ext1 i; refine Fin.addCases ?_ ?_ i <;> intro j <;> apply Mink.ext_by <;> simp [dawn,place,Bid.bothH,Bid.bothP]

lemma along_compact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) {f : Probe F} (h : HasCompactSupport ⇑f) : HasCompactSupport ⇑(along e f) := by
  change HasCompactSupport ((⇑f) ∘ e.toHomeomorph)
  exact h.comp_homeomorph _

lemma bar_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Probe E} (h : HasCompactSupport ⇑f) : HasCompactSupport ⇑(bar f) := by
  rw [show (⇑(bar f)) = star ∘ (⇑f) from funext fun _ => bar_at ..]
  exact h.comp_left (show star (0:ℂ)=0 from star_zero ℂ)

lemma joined_compact (f : Joint n) (g : Joint m) (h : HasCompactSupport ⇑f) (hp : HasCompactSupport ⇑g) :
    HasCompactSupport ⇑(joinedTest (reversed f) g) := by
  have hh : HasCompactSupport ⇑(reversed f) := along_compact (ContinuousLinearEquiv.neg ℝ) h
  unfold joinedTest
  exact along_compact merger.symm (compact_combine (f:=bar (reversed f)) (g:=g) (bar_compact hh) hp)

def chilled (x : Heights n) (f : Joint n) (h : HasCompactSupport ⇑f) : Joint n := lifts (-dawn x) f h

lemma chilled_zero (f : Joint n) (h : HasCompactSupport ⇑f) : chilled 0 f h=f := by
  rw [chilled, show dawn (0:Heights n)=0 by ext1 i; apply Mink.ext_by <;> simp [dawn,place]]
  ext1; simp

lemma Braided (x : Heights n) (y : Heights m) (f : Joint n) (g : Joint m)
    (h : HasCompactSupport ⇑f) (hp : HasCompactSupport ⇑g) :
    chilled (Bid.bothH x y) (joinedTest (reversed f) g) (joined_compact f g h hp) =
      joinedTest (reversed (chilled x f h)) (chilled y g hp) := by
  ext1 p
  obtain ⟨⟨u,v⟩,rfl⟩ := (merger (n:=n) (m:=m)).surjective p
  unfold chilled; change lifts _ _ _ (Bid.bothP u v) = joinedTest _ _ (Bid.bothP u v)
  rw [rises, joinedTest_at, joinedTest_at, reversed_at, reversed_at, rises, rises, merge_height,
    inner_neg_left,merged_inner,inner_neg_left]
  simp [Complex.exp_add,← Complex.exp_conj]
  ring

variable {G : Gauge} {C : Family G} {S : Table C.book}

lemma boundary_tilt {W : Surface S} {K : Blanket (n+m)} (h : K.Modified) (hc : Bid.cones W)
    (x : Heights n) (y : Heights m) (w : Fin (n+m) → S.Union)
    (he : dawn (Bid.bothH x y) ∈ shores (n+m))
    (f : Joint n) (g : Joint m) (hf : HasCompactSupport ⇑f) (hg : HasCompactSupport ⇑g) :
    K.partialD (W.W _ w) (dawn (Bid.bothH x y)) (joinedTest (hat f) (hat g)) =
      W.W _ w (joinedTest (hat (chilled x f hf)) (hat (chilled y g hg))) := by
  rw [← joined_fourier, Blanket.partialD,Distn.inverse_at, comes,ContinuousLinearMap.comp_apply]
  rw [Work.C15.blanketed_eq h (Distn.fourier _) (hc _ _) _ he _ (joined_compact f g hf hg)]
  rw [Distn.fourier_at]; rw [← joined_fourier,← Braided x y f g hf hg]; rfl

end YM.EveryPhase
