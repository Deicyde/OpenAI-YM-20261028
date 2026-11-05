import YM.Work.F05.Transport

/-!
# Independence of the unmasked readouts under the change of slice

Paths, orientations, and tags are physical ones. No translation or
permutation of operands to make the two readouts agree is needed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Lattice Wilson RG Precision Exterior Tree
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {c f n : Side} {G : Gauge} {S : StepData c f}
  {p : Clip} {W : PathData G} {σ C Λ : ℝ}

lemma slot_cover_gauge (s : RG.Slot) (U : CoverConfig G) (t : Cover → G.El) :
    s.eval (Lattice.gauge t U) = G.adjoint (t 0) (s.eval U) := by
  simp only [Slot.eval, travel_gauge, face_gauge, Gauge.curvature_conjugate]
  simp only [← G.adjoint_mul, Slot.offset, inv_mul_cancel_right]

lemma slot_gauge (s : RG.Slot) (U : Config G n) (t : Site n → G.El) (x : Site n) :
    s.atSite (Lattice.gauge t U) x = G.adjoint (t x) (s.atSite U x) := by
  unfold Slot.atSite
  rw [expandAt_gauge, slot_cover_gauge, map_zero, zero_add]

lemma uncut_gauge {m : ℕ} (R : ℕ → Atom G m) (h : ∀ i, (R i).Invariant)
    (U : Config G n) (t : Site n → G.El) : uncut R (Lattice.gauge t U) = uncut R U := by
  have he (i : ℕ) x : (R i).unmasked (Lattice.gauge t U) x = (R i).unmasked U x := by
    simp only [Atom.unmasked, slot_gauge]; exact h i ..
  simp only [uncut, he]

lemma ell_gauge (h : W.Bounds p σ C Λ) (U : Config G n) (t : Site n → G.El) (i : Face (Per n)) :
    W.ell (Lattice.gauge t U) i = G.adjoint (t i.1) (W.ell U i) := by
  unfold PathData.ell
  let F := (G.adjoint (t i.1)).toContinuousLinearMap
  have he j : W.ellTerms i j (Lattice.gauge t U) = F (W.ellTerms i j U) := by
    unfold PathData.ellTerms
    rw [slot_gauge, F.map_smul]
    rfl
  simp_rw [he]
  exact (F.map_tsum ((W.ell_dominated h i).summable U)).symm

lemma quadratic_gauge (h : W.Bounds p σ C Λ) (U : Config G n) (t : Site n → G.El) :
    quadratic p W (Lattice.gauge t U) = quadratic p W U := by
  simp only [quadratic, face_gauge, G.price_conj, ell_gauge h, G.norm_adjoint]

lemma pull_gauge_zero (U : Config G n) (t : Site n → G.El) (s : Signed) :
    pull s 0 (Lattice.gauge t U) = Lattice.gauge (fun i => t (affine s 0 i)) (pull s 0 U) := by
  funext ⟨x,i⟩
  change ((posDir i).rotate s).read (Lattice.gauge t U) (affine s 0 x) = _
  rw [Step.gauge_read]
  simp only [Lattice.gauge, Step.vec_rotate, Step.vec_pos, pull, affine, Signed.act_add, add_zero]

lemma mainTerm_gauge (h : W.Bounds p σ C Λ) (U : Config G n) (t : Site n → G.El) :
    mainTerm p W (Lattice.gauge t U) = mainTerm p W U := by
  simp only [mainTerm, pull_gauge_zero, quadratic_gauge h,
    uncut_gauge W.cubic (fun i => (h.invariant i).2.1),
    uncut_gauge W.quartic (fun i => (h.invariant i).2.2)]

lemma loop_gauge (h : W.Bounds p σ C Λ) (U : Config G n) (t : Site n → G.El) :
    Precision.loop W (Lattice.gauge t U) = Precision.loop W U := by
  simp only [Precision.loop, pull_gauge_zero,
    uncut_gauge W.loop (fun i => (h.invariant i).1)]

lemma root_noise (hs : S.patch.Branches S.kernel G) (V : Config G c) (U : Config G f)
    (t : Site f → G.El) (ht : ∀ x, t (S.ratio.embed x) = 1) (r : S.Choices) :
    noiseTaylor S V (Lattice.gauge t U) r = noiseTaylor S V U r := by
  have he : S.prediction (Lattice.gauge t U) r = S.prediction U r := by
    funext i
    rw [StepData.prediction, S.updateGauged hs]
    simp only [ht, one_mul, inv_one, mul_one]
    rfl
  unfold noiseTaylor
  rw [he]

variable (B T : Forest S.ratio)

/-- The exact fine representative after switching trees is the gauged
original representative, by a root-fixed gauge. Local in additive inputs. -/
lemma fine_switch : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
    lifting T (represent z.1) (switch B T z.1 z.2) = Profiles.wiped T (lifting B (represent z.1) z.2) := by
  filter_upwards [exposure_switch B T (G:=G)] with z hz
  rw [← drape_exposure, hz, ← drape_exposure]
  apply Profiles.wears

lemma tested_switch (hs : S.patch.Branches S.kernel G) (h : W.Bounds p σ C Λ) (r : S.Choices) :
    ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
      tested B r p W z.1 z.2 = tested T r p W z.1 (switch B T z.1 z.2) := by
  filter_upwards [fine_switch (G:=G) B T] with z hz
  simp only [tested, hz, Profiles.wiped, mainTerm_gauge h,
    root_noise hs _ _ _ (fun _ => T.fold_root ..)]

lemma loop_switch (h : W.Bounds p σ C Λ) : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
    Precision.loop W (lifting B (represent z.1) z.2) =
      Precision.loop W (lifting T (represent z.1) (switch B T z.1 z.2)) := by
  filter_upwards [fine_switch (G:=G) B T] with z hz
  simp only [hz, Profiles.wiped, loop_gauge h]

end YM.Work.F05
