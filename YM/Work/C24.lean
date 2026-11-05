import YM.Analysis.Polydisc
import YM.Bid.Grow

/-! # From the mixed point kernel to Gram convergence of independently heated words -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C24
open Bid Set Filter Function Boundary OS MeasureTheory WithLp
open scoped Topology InnerProductSpace BigOperators NNReal

variable {n m : ℕ} {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber T timeAxis}

/-- Analogue of `Table.Pairing.glues` with a reversed first tuple, and no
geometric reflection of the real spacetime positions. -/
def glue : WithLp 2 (Points n × Points m) ≃ₗᵢ[ℝ] Points (n + m) where
  toFun p := bothP p.fst p.snd
  invFun x := toLp 2 (points (fun i => x (Fin.castAdd m i.rev)), points (fun i => x (Fin.natAdd n i)))
  left_inv p := by
    apply ofLp_injective 2
    apply Prod.ext <;> (apply PiLp.ext; intro i; simp [bothP])
  right_inv p := by
    apply PiLp.ext; intro i
    refine Fin.addCases ?_ ?_ i <;> (intro j; simp [bothP])
  map_add' x y := by
    apply PiLp.ext; intro i
    refine Fin.addCases ?_ ?_ i <;> (intro j; simp [bothP])
  map_smul' c x := by
    apply PiLp.ext; intro i
    refine Fin.addCases ?_ ?_ i <;> (intro j; simp [bothP])
  norm_map' p := by
    change ‖bothP p.fst p.snd‖ = ‖p‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2 _ p.fst, PiLp.norm_sq_eq_of_L2 _ p.snd, Fin.sum_univ_add]
    simp only [bothP, points_apply, Fin.append_left, Fin.append_right]
    exact congrArg (· + _) (Equiv.sum_comp Fin.revPerm (fun i : Fin n => ‖p.fst i‖^2))

def merger : (Points n × Points m) ≃L[ℝ] Points (n + m) :=
  (prodContinuousLinearEquiv 2 ℝ (Points n) (Points m)).symm.trans glue.toContinuousLinearEquiv

lemma preserves : MeasurePreserving (merger (n := n) (m := m)) :=
  glue.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)

lemma ordered {x : Heights n} {y : Heights m} (hx : x ∈ positiveHeight n) (hy : y ∈ positiveHeight m) :
    bothH x y ∈ east (n + m) := by
  intro i j; refine Fin.addCases ?_ ?_ i
  · intro a; refine Fin.addCases ?_ ?_ j
    · intro b h; simp [bothH]; exact hx.1 (Fin.rev_lt_rev.mpr h)
    intro b _
    simp only [bothH, Fin.append_left, Fin.append_right]
    linarith [hx.2 a.rev, hy.2 b]
  intro a; refine Fin.addCases ?_ ?_ j
  · intro b h
    change n + a.val < b.val at h; omega
  intro b h; change n + a.val < n + b.val at h
  simpa [bothH] using hy.1 (show a < b by omega)

lemma eventually_pos : ∀ᶠ p : ℝ × ℝ in till ×ˢ till, 0 < p.1 ∧ 0 < p.2 :=
  (tendsto_fst.eventually (show ∀ᶠ t : ℝ in till, 0 < t from self_mem_nhdsWithin)).and
    (tendsto_snd.eventually (show ∀ᶠ t : ℝ in till, 0 < t from self_mem_nhdsWithin))

lemma toward (n m : ℕ) :
    Tendsto (fun p : ℝ × ℝ => bothH (Small.profile p.1 n) (Small.profile p.2 m)) (till ×ˢ till)
      (𝓝[east (n+m)] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr ?_, ?_⟩
  · intro i; refine Fin.addCases ?_ ?_ i
    · intro j
      have h : Tendsto (fun p : ℝ × ℝ => p.1) (till ×ˢ till) (𝓝 0) := tendsto_fst.mono_right nhdsWithin_le_nhds
      simpa [bothH, Small.profile] using ((tendsto_const_nhds (x := (j.rev.val : ℝ) + 1)).mul h).neg
    intro j
    have h : Tendsto (fun p : ℝ × ℝ => p.2) (till ×ˢ till) (𝓝 0) := tendsto_snd.mono_right nhdsWithin_le_nhds
    simpa [bothH, Small.profile] using (tendsto_const_nhds (x := (j.val : ℝ) + 1)).mul h
  filter_upwards [eventually_pos] with p hp
  exact ordered (Small.imminent hp.1) (Small.imminent hp.2)

def bothL (v : Fin n → Letter S) (w : Fin m → Letter S) (J : StarOp S) : Fin (n + m) → Letter S :=
  Fin.append (fun i => Letter.op J (v i.rev)) w

def bothTest (v : Fin n → Letter S) (w : Fin m → Letter S) (J : StarOp S) :=
  Joint.materialize (n + m) fun i => (bothL v w J i).2

lemma bothTest_at (v : Fin n → Letter S) (w : Fin m → Letter S) (J : StarOp S) (x : Points n) (y : Points m) :
    bothTest v w J (bothP x y) = (starRingEnd ℂ) (Joint.materialize n (fun i => (v i).2) x) *
      Joint.materialize m (fun i => (w i).2) y := by
  simp only [bothTest, Joint.material_at, Fin.prod_univ_add, bothL, bothP, points_apply,
    Fin.append_left, Fin.append_right, Letter.op, Probe.bar_at, map_prod]
  exact congrArg (· * _) (Equiv.prod_comp Fin.revPerm (fun i => star ((v i).2 (x i))))

lemma bothL_get (v w : Sentence S) (J : StarOp S) :
    List.ofFn (bothL v.get w.get J) = Sentence.rev J v ++ w := by
  unfold bothL Sentence.rev
  rw [List.ofFn_fin_append, List.ofFn_get]
  congr 1
  refine List.ext_get (by simp) (fun i h h' => ?_)
  rw [List.get_ofFn, List.get_eq_getElem (l := List.reverse _), List.getElem_reverse, List.getElem_map]
  congr 1
  rw [List.get_eq_getElem]
  congr 1
  simp [Fin.val_rev]; omega

lemma expect_ofFn (W : Surface S) (q : Fin n → Letter S) :
    W.expect (List.ofFn q) = W.W n (fun i => (q i).1) (Joint.materialize n fun i => (q i).2) := by
  have key (b : Sentence S) (k : ℕ) (h : b.length = k) (v : Fin k → Letter S)
      (he : ∀ i, b.get i = v (Fin.cast h i)) :
      W.expect b = W.W k (fun i => (v i).1) (Joint.materialize k fun i => (v i).2) := by
    subst k; simp only [Surface.expect, he, Fin.cast_refl, id_eq]
  exact key _ _ (by simp) q (List.get_ofFn _)

lemma kernel_as (W : Surface S) (J : StarOp S) (v w : Sentence S) :
    W.kernel J v w = W.W (v.length + w.length) (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) J)
      (bothTest v.get w.get J) := by
  rw [Surface.kernel, ← bothL_get, expect_ofFn]
  unfold bothTest
  congr 2
  funext i; refine Fin.addCases ?_ ?_ i <;> (intro j; simp [bothT, bothL, Letter.op])

variable {B : Small S V} {F : Waves S} {J : StarOp S} {K : Spins S} {W : Surface S}

lemma integrated (roof : Roof B K) (h : Hull B F J) (int : F.NonTangentialFree W) (v w : Sentence S)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    inner ℂ (B.heatCup v t) (B.heatCup w u) = ∫ x, F.restricted
        (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) J)
        (bothH (Small.profile t v.length) (Small.profile u w.length)) x * bothTest v.get w.get J x := by
  let a := Small.profile t v.length
  let b := Small.profile u w.length
  let M := bothTest v.get w.get J
  let d (x : Points (v.length + w.length)) := F.restricted
    (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) J) (bothH a b) x * M x
  let e := merger (n := v.length) (m := w.length)
  have ha : a ∈ positiveHeight _ := Small.imminent ht
  have hb : b ∈ positiveHeight _ := Small.imminent hu
  have hi : Integrable (d ∘ e) := (preserves.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr
    (int.int _ _ _ (ordered ha hb) _)
  calc
    _ = ∫ x : Points v.length, ∫ y : Points w.length, (d ∘ e) (x, y) := by
      rw [Small.heatCup, ← inner_conj_symm, ← integral_inner (roof.uses v t ht), ← integral_conj]
      apply integral_congr_ae; filter_upwards with x
      rw [inner_conj_symm, Small.heatCup, ← integral_inner (roof.uses w u hu)]
      apply integral_congr_ae; filter_upwards with y
      change inner ℂ (_ • B.shot _ _ _ a x) (_ • B.shot _ _ _ b y) = d (bothP x y)
      rw [inner_smul_left, inner_smul_right, h.join _ _ _ _ _ _ _ _ ha hb (Small.suitable ht) (Small.suitable hu)]
      dsimp only [d, M]
      rw [bothTest_at]; ring
    _ = ∫ z, (d ∘ e) z ∂(volume.prod volume) := (integral_prod _ hi).symm
    _ = ∫ x, d x := preserves.integral_comp e.toHomeomorph.measurableEmbedding d

theorem answer : YM.Bid.C24 := by
  intro G L S T V P A B F J K W _ _ h roof hull
  refine ⟨roof.uses, fun v w => ?_, roof.time⟩
  rw [kernel_as W J v w]
  have H := (h.corner _ (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) J) (bothTest v.get w.get J)).comp
    (toward v.length w.length)
  apply H.congr'
  filter_upwards [eventually_pos] with p hp using (integrated roof hull h v w hp.1 hp.2).symm

end YM.Work.C24
