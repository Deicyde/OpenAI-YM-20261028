import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Analysis.Polydisc
import YM.Bid.Tar



/-!
# Identifying the two `NearPair.Panes` germs at a Euclidean point

Read each pane on a totally real slice (real space and PURE IMAGINARY time,
including variations of those imaginary times). On *different open subsets*
of that slice they evaluate the same off-coincidence smooth function. This
gives ALL-order jet agreement on the slice at the point in question. Upgrade
to full germ agreement by complex analyticity.

No need for the spin, how the panes were built, obtaining causal frequency
support, or realizing/testing the partial distributions from the germs here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C20
open Function Set Filter Metric Complex Boundary
open scoped Topology ContDiff ENNReal

section analytic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

/-- Agreement just on the open side is enough to identify any derivatives
which are continuous up to the point (here packaged with `ContDiffAt`). -/
theorem jets_on_open_side {p : E} {U : Set E} {f g : E → ℂ} (hu : IsOpen U)
    (hp : (𝓝[U] p).NeBot) (h : f =ᶠ[𝓝[U] p] g) (m : ℕ)
    (hf : ContDiffAt ℝ m f p) (hg : ContDiffAt ℝ m g p) :
    iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m g p := by
  have heq : iteratedFDeriv ℝ m f =ᶠ[𝓝[U] p] iteratedFDeriv ℝ m g := by
    filter_upwards [self_mem_nhdsWithin, eventually_eventually_nhdsWithin.2 h] with y hy hs
    have h' : f =ᶠ[𝓝[U] y] g := hs
    rw [hu.nhdsWithin_eq hy] at h'
    exact (h'.iteratedFDeriv ℝ m).eq_of_nhds
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf.continuousAt_iteratedFDeriv le_rfl).tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.continuousAt_iteratedFDeriv le_rfl).tendsto.mono_left nhdsWithin_le_nhds)
    heq

/-- The real jets on the slice are just restrictions of the complex jets. -/
theorem pullback_jet {M : E →L[ℝ] V} {p : E} {f : V → ℂ} {m : ℕ}
    (hf : ContDiffAt ℂ m f (M p)) (u : Fin m → E) :
    iteratedFDeriv ℝ m (f ∘ M) p u = iteratedFDeriv ℂ m f (M p) (fun i => M (u i)) := by
  -- Get an open set to apply the within-version of composition on the right.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((hf.restrict_scalars ℝ).eventually (by simp))
  have ho : IsOpen (M ⁻¹' ball (M p) r) := isOpen_ball.preimage M.continuous
  have huz : M p ∈ ball (M p) r := mem_ball_self hr
  have hu : ContDiffOn ℝ m f (ball (M p) r) := fun y hy =>
    (show ContDiffAt ℝ m f y from hball hy).contDiffWithinAt
  have h := M.iteratedFDerivWithin_comp_right hu isOpen_ball.uniqueDiffOn ho.uniqueDiffOn huz le_rfl
  rw [iteratedFDerivWithin_of_isOpen m ho (show p ∈ M ⁻¹' ball (M p) r from huz),
    iteratedFDerivWithin_of_isOpen m isOpen_ball huz,
    ← hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ)] at h
  rw [h]
  rfl

/-- Germ equality from all real jets of a real-linear pullback whose image
spans the complex space. -/
theorem complex_germ {M : E →L[ℝ] V} {p : E} {f g : V → ℂ}
    (hf : AnalyticAt ℂ f (M p)) (hg : AnalyticAt ℂ g (M p))
    (hspan : Submodule.span ℂ (range M) = ⊤)
    (hjet : ∀ m, iteratedFDeriv ℝ m (f ∘ M) p = iteratedFDeriv ℝ m (g ∘ M) p) :
    f =ᶠ[𝓝 (M p)] g := by
  have hall (m : ℕ) : iteratedFDeriv ℂ m f (M p) = iteratedFDeriv ℂ m g (M p) := by
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply MultilinearMap.ext_of_span_eq_top (γ := fun _ : Fin m => E)
      (g := fun {_} (x : E) => M x) (fun _ => hspan)
    intro u
    change iteratedFDeriv ℂ m f (M p) (fun i => M (u i)) = iteratedFDeriv ℂ m g (M p) (fun i => M (u i))
    rw [← pullback_jet hf.contDiffAt u, ← pullback_jet hg.contDiffAt u, hjet m]
  obtain ⟨a, r, hr⟩ := hf
  obtain ⟨b, s, hs⟩ := hg
  filter_upwards [eball_mem_nhds (M p) hr.r_pos, eball_mem_nhds (M p) hs.r_pos] with y hy hz
  have he := hr.hasSum_iteratedFDeriv (y := y-M p) (by
    rw [mem_eball, ← edist_sub_right y (M p) (M p), sub_self] at hy; exact hy)
  have hx := hs.hasSum_iteratedFDeriv (y := y-M p) (by
    rw [mem_eball, ← edist_sub_right y (M p) (M p), sub_self] at hz; exact hz)
  simp_rw [hall] at he
  simpa using he.unique hx

end analytic

variable {n : ℕ}

/-- `space -> space` (real), `time -> I*time`, in absolute coordinates. -/
def wickSlice (n : ℕ) : Points n →L[ℝ] Full n := LinearMap.toContinuousLinearMap
  { toFun := fun x : Points n => WithLp.toLp 2 fun i : Fin n × Axis =>
      (x i.1 i.2 : ℂ) * if i.2 = timeAxis then I else 1
    map_add' := by intro x y; ext1 i; by_cases h : i.2 = timeAxis <;> simp [h, add_mul]
    map_smul' := by intro c x; ext1 i; simp [mul_assoc, Complex.real_smul] }

theorem wick_apply (x : Points n) (i : Fin n × Axis) :
    wickSlice n x i = (x i.1 i.2 : ℂ) * if i.2 = timeAxis then I else 1 := rfl

theorem wick_span (n : ℕ) : Submodule.span ℂ (range (wickSlice n)) = ⊤ := by
  apply top_unique
  intro z _
  -- z = slice u + I * slice v
  let u : Points n := points fun i => WithLp.toLp 2 fun a =>
    if a = timeAxis then (z (i,a)).im else (z (i,a)).re
  let v : Points n := points fun i => WithLp.toLp 2 fun a =>
    if a = timeAxis then -(z (i,a)).re else (z (i,a)).im
  have he : wickSlice n u + I • wickSlice n v = z := by
    ext1 i
    obtain ⟨i,a⟩ := i
    apply Complex.ext <;> by_cases h : a = timeAxis <;> simp [wick_apply, u, v, h]
  rw [← he]
  exact Submodule.add_mem _ (Submodule.subset_span (mem_range_self _))
    (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _)))

/-- Euclidean heights, not Minkowski times of the pane's base. -/
def readings (q : Points n) : Heights n := fun i => time (q i)

theorem place_same (q : Points n) : place (Boundary.trace q) (readings q) = q := by
  ext1 i
  simp [place, Boundary.trace, readings]

theorem wick_glow (q : Points n) : wickSlice n q =
    glow (place (Boundary.trace q) 0) (dawn (readings q)) := by
  ext1 i
  obtain ⟨i,a⟩ := i
  refine Fin.lastCases ?_ (fun k => ?_) a
  · rw [wick_apply]; change _ * (if timeAxis = timeAxis then I else 1) =
      (time (place (Boundary.trace q) 0 i) : ℂ) + (time (dawn (readings q) i) : ℂ)*I
    simp [place, dawn, readings]; rfl
  · simp [wick_apply, glow, dawn, Boundary.trace, spatial, place, position, readings, time]

theorem wick_name (X : NearPair n) (q : Points n) : X.name (wickSlice n q) = wickSlice n (X.switch q) := by
  unfold NearPair.name
  rw [wick_glow, re_glow, im_glow, wick_glow]
  rfl

theorem readings_place (t : SpacePoints n) (y : Heights n) : readings (place t y) = y := by
  funext i
  simp [readings, place]

def ordered (n : ℕ) : Set (Points n) := readings ⁻¹' east n

theorem ordered_open (n : ℕ) : IsOpen (ordered n) :=
  (open_east n).preimage (show Continuous (@readings n) by unfold readings; fun_prop)

theorem wick_tube : MapsTo (wickSlice n) (ordered n) (tube n) := by
  intro u hu
  have hv : readings u ∈ east n := hu
  rw [wick_glow]
  change shade _ ∈ fields n
  rw [im_glow]; exact etched hv

/-- There really are ordered Euclidean configurations approaching. -/
theorem ordered_neBot {q : Points n} (h : readings q ∈ sunrise n) :
    (𝓝[ordered n] q).NeBot := by
  have hn : (𝓝[east n] (readings q)).NeBot := awaits h
  have he : Tendsto (place (Boundary.trace q)) (𝓝[east n] (readings q)) (𝓝[ordered n] q) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (place (Boundary.trace q)) := by
        change Continuous (fun t : Heights n => WithLp.toLp 2 (fun i => Mink.divide.symm (_,t i)))
        fun_prop
      simpa only [place_same] using (hc.tendsto (readings q)).mono_left
        (nhdsWithin_le_nhds (s := east n))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (show readings _ ∈ east n from readings_place (Boundary.trace q) y |>.symm ▸ hy)
  exact he.neBot

theorem switch_neBot (X : NearPair n) {q : Points n} (h : readings (X.switch q) ∈ sunrise n) :
    (𝓝[X.switch ⁻¹' ordered n] q).NeBot := by
  have hn := ordered_neBot h
  have he : Tendsto X.switch.symm (𝓝[ordered n] (X.switch q)) (𝓝[X.switch ⁻¹' ordered n] q) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (X.switch.symm.continuous.tendsto (X.switch q)).mono_left
        (nhdsWithin_le_nhds (s := ordered n))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  exact he.neBot

theorem before_east {y : Heights n} {X : NearPair n} (h : X.spectator y) : y ∈ sunrise n := by
  intro a b hab
  rcases lt_or_eq_of_le hab with hl|hl
  · by_cases hij : a ≠ X.i ∨ b ≠ X.j
    · exact (h.2 a b hl hij).le
    push Not at hij
    rw [hij.1, hij.2, h.1]
  exact (congr_arg y hl).le

theorem same_height {y : Heights n} {X : NearPair n} (h : y X.i = y X.j) (s : SpacePoints n) :
    readings (X.switch (place s y)) = y := by
  funext i
  rw [readings, NearPair.switch_at]; simp only [place, points_apply, time_position]
  by_cases hi : i = X.i
  · simp [hi, NearPair.s, h]
  by_cases hj : i = X.j
  · simp [hj, NearPair.s, h]
  rw [NearPair.s, Equiv.swap_apply_of_ne_of_ne hi hj]

/-- The Euclidean point in question is not on any collision diagonal. -/
theorem euclid_conf {y : Heights n} {X : NearPair n} (h : X.spectator y) {x : Points n} (hx : x ∈ X.gap) :
    place (Boundary.trace x) y ∈ conf n := by
  have hw : spatial (x X.i) ≠ spatial (x X.j) := by
    intro hh
    rw [NearPair.gap, Set.mem_setOf, Mink.lateral, sub_eq_add_neg, Mink.rest_add, Mink.rest_neg, hh] at hx
    simp at hx
    exact (abs_nonneg _).not_gt hx
  let q := place (Boundary.trace x) y
  have he (i j : Fin n) (hlt : i < j) : q i ≠ q j := by
    intro hh
    by_cases hij : i ≠ X.i ∨ j ≠ X.j
    · have hs := congr_arg time hh
      simp only [q, place, points_apply, time_position] at hs
      exact (h.2 i j hlt hij).ne hs
    push Not at hij
    rw [hij.1, hij.2] at hh
    have hs := congr_arg spatial hh
    exact hw (by simpa [q, place, Boundary.trace] using hs)
  intro i j hij
  by_contra H
  exact (lt_or_gt_of_ne H).elim (fun hi => he i j hi hij) (fun hi => he j i hi hij.symm)

variable {G : Gauge} {L : Register G} {S T : Table L} {F : Waves S}
  {Y : Surface S} {D : ∀ i, Blanket i} {Z : Y.Aurora D}

theorem emit_table (ht : T.Symmetric) (hr : T.respects S) (hR : F.Region T) (hF : Z.FullBody F)
    (w : Fin n → L.Token) {q : Points n} (h : q ∈ ordered n) :
    Z.emit (fun i => S.pin (w i).1 (S.project _ (w i).2)) (wickSlice n q) = T.read q w := by
  let t := Boundary.trace q
  have hy : readings q ∈ east n := h
  have hspace : Boundary.trace (place t 0) = t := by funext i; simp [Boundary.trace, place, t]
  have htime : shift (place t 0) (readings q) = (fun i => (time (q i) : ℂ)*I) := by
    funext i
    simp [shift, readings, place]
  rw [wick_glow, hF.pure n _ _ _ hy, Waves.restricted, htime, hspace]
  exact F.root_raw ht hr hR w q hy

theorem answer : YM.Bid.C20 := by
  intro G L S T P F Y D Z hs hi ht hh hr hR hF n v y X A x hx hz
  let p := place (Boundary.trace x) y
  let M := wickSlice n
  let f := (A.original x hx).extendF
  let g := (A.tilted x hx).extendF
  have hy : X.spectator y := A.permitted.willing
  have hup : readings p = y := readings_place ..
  have hvp : readings (X.switch p) = y := same_height hy.1 _
  have hp := euclid_conf hy hx
  have hspace : Boundary.trace p = Boundary.trace x := by funext i; simp [Boundary.trace, p, place]
  have hx0 : readings x = 0 := funext hz
  have hM : M p = glow x (dawn y) := by
    unfold M
    rw [wick_glow, hup, hspace, ← hx0, place_same]
  change f =ᶠ[𝓝 _] g
  have ha : AnalyticAt ℂ f (M p) := hM.symm ▸ (A.original x hx).doc
  have hb : AnalyticAt ℂ g (M p) := hM.symm ▸ (A.tilted x hx).doc

  -- Lift actual Union labels only once (including in both orientations).
  obtain ⟨d, b, hv⟩ := P.joint hs hi v
  choose l hl using fun i => S.onto d (b i)
  let w : Fin n → L.Token := fun i => ⟨d, l i⟩
  have hw : v = fun i => S.pin (w i).1 (S.project _ (w i).2) := by
    funext i
    exact (congr_fun hv i).trans (congr_arg (S.pin d) (hl i).symm)
  let C := fun x => T.read x w
  have hC : ContDiffAt ℝ ∞ C p := (T.smooth_read hh w).contDiffAt ((conf_open n).mem_nhds hp)

  have hu : Tendsto M (𝓝[ordered n] p) (𝓝[tube n] (glow x (dawn y))) := by
    rw [← hM]
    exact M.continuous.continuousWithinAt.tendsto_nhdsWithin wick_tube
  have heq : f ∘ M =ᶠ[𝓝[ordered n] p] C := by
    have hf : f ∘ M =ᶠ[𝓝[ordered n] p] Z.emit v ∘ M := hu.eventually (A.original x hx |>.fits)
    refine hf.trans ?_
    rw [hw]
    filter_upwards [self_mem_nhdsWithin] with i hi using emit_table ht hr hR hF w hi

  let V : Set (Points n) := X.switch ⁻¹' ordered n
  have hu' : Tendsto M (𝓝[V] p) (𝓝[X.name ⁻¹' tube n] (glow x (dawn y))) := by
    rw [← hM]
    refine M.continuous.continuousWithinAt.tendsto_nhdsWithin fun u hu => ?_
    change X.name (wickSlice n u) ∈ tube n
    rw [wick_name]; exact wick_tube (show X.switch u ∈ ordered n from hu)
  have heq' : g ∘ M =ᶠ[𝓝[V] p] C := by
    have hg : g ∘ M =ᶠ[𝓝[V] p] ((Z.emit (v ∘ X.s)) ∘ X.name) ∘ M :=
      hu'.eventually (A.tilted x hx |>.fits)
    refine hg.trans ?_
    rw [hw]
    have hn : ∀ᶠ u in 𝓝[V] p, u ∈ conf n :=
      Eventually.filter_mono nhdsWithin_le_nhds ((conf_open n).mem_nhds hp)
    filter_upwards [self_mem_nhdsWithin, hn] with u hu hc
    simp only [Function.comp_apply, M, wick_name]
    exact (emit_table ht hr hR hF (w ∘ X.s) (show X.switch u ∈ ordered n from hu)).trans
      (ht.same X.s hc w)

  rw [← hM]
  refine complex_germ ha hb (wick_span n) fun m => ?_
  have hm : ContDiffAt ℝ m C p := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffAt ℂ m f (M p) := ha.contDiffAt
  have hg : ContDiffAt ℂ m g (M p) := hb.contDiffAt
  have hne := ordered_neBot (q := p) (hup.symm ▸ before_east hy)
  have hne' := switch_neBot X (q := p) (hvp.symm ▸ before_east hy)
  exact (jets_on_open_side (ordered_open n) hne heq m ((hf.restrict_scalars ℝ).comp p M.contDiff.contDiffAt)
    hm).trans (jets_on_open_side ((ordered_open n).preimage X.switch.continuous) hne' heq'.symm m
      hm ((hg.restrict_scalars ℝ).comp p M.contDiff.contDiffAt))

end YM.Work.C20
