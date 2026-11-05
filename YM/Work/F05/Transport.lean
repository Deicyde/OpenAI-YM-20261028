import YM.Analysis.Polydisc
import YM.Bid.Station
import YM.PCalc.Profiles

/-!
# Real changes of slice coordinates

All germs here are in the joint variables (coarse coordinate, additive fine
coordinate in the given tree slice). They can therefore be used off a graph
as well as on one. No sizes of neighborhoods are claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Lattice Wilson RG Precision Exterior Tree
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {g : Ratio c f}

lemma hold_near {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {V : X × Y → Prop}
    {x : X} {y : Y} (h : ∀ᶠ z in 𝓝 (x,y), V z) : ∀ᶠ y' in 𝓝 y, V (x,y') :=
  (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually h

lemma hold_jet {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : X → Y → Z} {x : X} {y : Y} (h : ContDiffAt ℝ ω (uncurry V) (x,y)) :
    ContDiffAt ℝ ω (V x) y :=
  h.comp (f:=fun z : Y => (x,z)) y (by fun_prop)


/-- The chart into the product-of-links realization of the slice. -/
def exposure (B : Forest g) (x : Bid.Dir G c) (y : AxisChart G B) : B.Slice G :=
  fun i => G.lieExp (y i) * replica g (represent x) i

lemma drape_exposure (B : Forest g) (x : Bid.Dir G c) (y : AxisChart G B) :
    B.drape (exposure B x y) = lifting B (represent x) y := rfl

/-- Links in the T slice measured relative to the background from x. -/
def relink (B T : Forest g) (x : Bid.Dir G c) (y : AxisChart G B) : T.Slice G :=
  fun i => Profiles.reroute B T G (exposure B x y) i * (replica g (represent x) i)⁻¹

/-- Switch from B coordinates to T coordinates; `plog` readout only asserted
correct near the origin. -/
def switch (B T : Forest g) (x : Bid.Dir G c) (y : AxisChart G B) : AxisChart G T :=
  fun i => G.plog (G.mat (relink B T x y i))

variable (B T : Forest g)

lemma exposure_zero : exposure B (0 : Bid.Dir G c) 0 = 1 := by
  funext i
  simp only [exposure, Pi.zero_apply, Precision.link_one, Precision.replica_one, Pi.one_apply,
    G.mat_lieExp_zero, one_mul]

lemma reroute_exposure_zero : Profiles.reroute B T G (exposure B 0 0) = 1 := by
  have he (F : Forest g) : F.drape (exposure F (0 : Bid.Dir G c) 0) = 1 := by
    rw [drape_exposure, lifted, Precision.link_one, Precision.replica_one]
  change Profiles.wick T (B.drape (exposure B 0 0)) = 1
  rw [he, ← he T, Profiles.wick_root, exposure_zero]

lemma relink_zero : relink B T (0 : Bid.Dir G c) 0 = 1 := by
  funext i
  rw [relink, reroute_exposure_zero, Precision.link_one, Precision.replica_one]
  simp

lemma switch_zero : switch B T (0 : Bid.Dir G c) 0 = 0 := by
  funext i
  rw [switch, relink_zero]
  simp

private lemma replica_continuous (i : Edge (Site f)) :
    Continuous (fun x : Bid.Dir G c => replica g (represent x) i) := by
  unfold replica
  split
  · exact continuous_const
  unfold represent increment collect
  simp only [Pi.one_apply, mul_one]
  exact G.lieExp_cont.comp (continuous_apply _)

lemma exposure_continuous : Continuous (uncurry (exposure B (G:=G))) := by
  refine continuous_pi (fun i => ?_)
  exact (G.lieExp_cont.comp ((continuous_apply i).comp continuous_snd)).mul
    ((replica_continuous (G:=G) i.val).comp continuous_fst)

lemma relink_continuous : Continuous (uncurry (relink B T (G:=G))) := by
  refine continuous_pi (fun i => ?_)
  exact ((continuous_apply i).comp ((Profiles.reroute B T G).continuous.comp
    (exposure_continuous B))).mul (((replica_continuous (G:=G) i.val).comp continuous_fst).inv)

private lemma replica_jet (i : Edge (Site f)) :
    ContDiffAt ℝ ω (fun x : Bid.Dir G c => G.mat (replica g (represent x) i)) 0 := by
  unfold replica
  split
  · exact contDiffAt_const
  unfold represent increment collect
  simp only [Pi.one_apply, mul_one]
  exact G.exp_jet.contDiffAt.comp _ (contDiffAt_apply _ _ _ _)

lemma exposure_jet (i : B.Free) :
    ContDiffAt ℝ ω (fun z : Bid.Dir G c × AxisChart G B => G.mat (exposure B z.1 z.2 i)) 0 := by
  simp only [exposure, G.mat_mul]
  apply ContDiffAt.mul
  · exact G.exp_jet.contDiffAt.comp _ ((contDiffAt_apply _ _ _ _).comp _ contDiffAt_snd)
  exact (replica_jet (g:=g) (G:=G) i.val).comp (f:=Prod.fst) (0 : Bid.Dir G c × AxisChart G B) contDiffAt_fst

lemma relink_jet (i : T.Free) :
    ContDiffAt ℝ ω (fun z : Bid.Dir G c × AxisChart G B => G.mat (relink B T z.1 z.2 i)) 0 := by
  let U (z : Bid.Dir G c × AxisChart G B) := B.drape (exposure B z.1 z.2)
  have h (j : Edge (Site f)) : ContDiffAt ℝ ω (fun z => G.mat (U z j)) 0 := by
    by_cases hj : j ∈ B.trunks
    · have hw z : U z j = 1 := B.on_tree _ ⟨j,hj⟩
      simp only [hw]; exact contDiffAt_const
    have hw z : U z j = exposure B z.1 z.2 ⟨j,hj⟩ := B.off_tree _ ⟨j,hj⟩
    simp only [hw]; exact exposure_jet B _
  have hs (V : Bid.Dir G c × AxisChart G B → G.El)
      (hv : ContDiffAt ℝ ω (fun z => G.mat (V z)) 0) :
      ContDiffAt ℝ ω (fun z => G.mat ((V z)⁻¹)) 0 := by
    simp only [G.mat_inv]
    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hv
  -- Same walk induction as the flat-response `YM.Push.stroll`, here
  -- with both sets of coordinates as parameters.
  have ht (x : Site f) (p : Walk) : ContDiffAt ℝ ω (fun z => G.mat (travel (U z) x p)) 0 := by
    induction p generalizing x with
    | nil => exact contDiffAt_const
    | cons j l ih =>
      simp only [travel, G.mat_mul]
      apply ContDiffAt.mul _ (ih _)
      unfold Step.read
      split
      · exact hs _ (h _)
      exact h _
  have hb (x : Site f) : ContDiffAt ℝ ω (fun z => G.mat (T.foldAt (U z) x)) 0 := hs _ (ht _ _)
  change ContDiffAt ℝ ω (fun z => G.mat (
    (T.foldAt (U z) i.val.1 * U z i.val * (T.foldAt (U z) _)⁻¹) *
      (replica g (represent z.1) i.val)⁻¹)) 0
  simp only [G.mat_mul]
  apply ContDiffAt.mul
  · exact ((hb _).mul (h _)).mul (hs _ (hb _))
  exact hs _ ((replica_jet (g:=g) (G:=G) i.val).comp (f:=Prod.fst) (0 : Bid.Dir G c × AxisChart G B) contDiffAt_fst)

lemma switch_jet : ContDiffAt ℝ ω (uncurry (switch B T (G:=G))) 0 := by
  refine contDiffAt_pi.mpr fun i => ?_
  let F (z : Bid.Dir G c × AxisChart G B) := G.mat (relink B T z.1 z.2 i)
  have he : F 0 = 1 := by
    change G.mat (relink B T 0 0 i) = 1
    rw [relink_zero]
    exact G.mat_one
  have ht : ContDiffAt ℝ ω G.plog (F 0) := he.symm ▸ G.plog_diff
  exact ht.comp _ (relink_jet B T i)

lemma exposure_switch : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
    exposure T z.1 (switch B T z.1 z.2) = Profiles.reroute B T G (exposure B z.1 z.2) := by
  have hh (i : T.Free) : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
      G.lieExp (switch B T z.1 z.2 i) = relink B T z.1 z.2 i := by
    have hv := ((continuous_apply i).comp (relink_continuous B T (G:=G))).tendsto
      (0 : Bid.Dir G c × AxisChart G B)
    change Tendsto _ _ (𝓝 (relink B T 0 0 i)) at hv
    rw [relink_zero] at hv
    exact hv.eventually G.plog_right
  filter_upwards [eventually_all.mpr hh] with z hz
  funext i
  rw [exposure, hz, relink, inv_mul_cancel_right]

lemma switch_switch : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
    switch T B z.1 (switch B T z.1 z.2) = z.2 := by
  have hh (i : B.Free) : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
      G.plog (G.mat (G.lieExp (z.2 i))) = z.2 i :=
    (((continuous_apply i).comp continuous_snd).tendsto (0 : Bid.Dir G c × AxisChart G B)).eventually
      G.plog_left
  filter_upwards [exposure_switch B T, eventually_all.mpr hh] with z hz hw
  have he : relink T B z.1 (switch B T z.1 z.2) = fun i => G.lieExp (z.2 i) := by
    funext i
    rw [relink, hz, show Profiles.reroute T B G = (Profiles.reroute B T G).symm from rfl,
      Homeomorph.symm_apply_apply, exposure, mul_inv_cancel_right]
  funext i
  rw [switch, he]
  exact hw i

end YM.Work.F05
