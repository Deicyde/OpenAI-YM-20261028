import YM.Extraction.StepSum
import YM.Extraction.Ties

/-!
# Step extraction: turn genuine generic limits into ordered limits on *all* separated tests

Check the continuum use of the finite-quadrature / JLIP proposal. Do not assume
estimates through ties beyond ordinary compact bounds. Handles support near
coordinate ties. Inner and outer a.e. exceptional sets harmless *at integration*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter MeasureTheory Lattice
open scoped Topology ContDiff BigOperators

variable {G : Gauge}

/-- Lift periodic positions before wrapping; applies with arbitrary cover coordinates. -/
def lifted (C : Family G) (N p : ℕ) {n : ℕ} (v : Fin n → C.book.Token) (b : Fin n → Cover) :=
  C.numeric N p v (wrap _ ∘ b)

/-- Ports. Preceding producers (notably chessboard) must realize them. Note
precisely where we need each fixed period vs eventual-R. -/
structure Bound (C : Family G) (g : Order) : Prop where
  cyclic (n : ℕ) (v : Fin n → C.book.Token) (p : ℕ) (K : Set (Points n)) (hK : IsCompact K) (hv : K ⊆ NoHit C.S p n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j : ℕ in atTop, ∀ b, tag (C.S.a (g.mesh j)) b ∈ K →
      ‖lifted C (g.mesh j) p v b‖ ≤ D
  volume (n : ℕ) (v : Fin n → C.book.Token) (K : Set (Points n)) (hp : IsCompact K) (hx : K ⊆ conf n) :
    ∃ D : ℝ, 0 ≤ D ∧ g.late (fun N p => ∀ b, tag (C.S.a N) b ∈ K → ‖lifted C N p v b‖ ≤ D)

theorem Bound.further {C : Family G} {f : Order} (h : Bound C f) (g : Order) : Bound C (f.refine g) := by
  constructor
  · intro n v p K hK hv
    obtain ⟨D,hD,h⟩ := h.cyclic n v p K hK hv
    exact ⟨D,hD,g.mesh.cofinal.eventually h⟩
  intro n v K hK hV
  obtain ⟨D,hD,h⟩ := h.volume n v K hK hV
  exact ⟨D,hD,Order.late_refine f g h⟩

namespace Order
variable (f : Order) (C : Family G) {P : ℕ → Table C.book} {S : Table C.book} {n : ℕ} {p : ℕ}

/-- Sup norm bound of one test (before scaling). -/
lemma testSup (t : Test n) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖t x‖ ≤ D := by
  obtain ⟨D,h⟩ := t.continuous.bounded_above_of_compact_support t.hasCompactSupport
  exact ⟨D,(norm_nonneg (t 0)).trans (h 0), fun x => h x⟩

lemma mesh_pointwise (H : f.Meshes C P) {t : Test n} (h : suitable C.S p t) (v : Fin n → C.book.Token) {x : Points n}
    (he : x ∈ Cyclic C.S p n) :
    Tendsto (fun j => densityCell C (f.mesh j) p v t x) atTop (𝓝 (t x * (P p).read x v)) := by
  by_cases hx : x ∈ Fund C.S p n
  · simp_rw [stepped C _ p hx v t]
    let r (i) := address (C.S.a (f.mesh i)) x
    have hi := chosen (S := C.S) x |>.comp f.mesh.cofinal
    have hp : Tendsto (fun j => C.numeric (f.mesh j) p v (bucket _ _ x)) atTop (𝓝 ((P p).read x v)) :=
      f.evaluated C H p n v x he r hi
    exact (t.continuous.continuousAt.tendsto.comp (show
      Tendsto (fun j => tag (C.S.a (f.mesh j)) (r j)) atTop (𝓝 x) from hi)).mul hp
  have hw : t x = 0 := by
    by_contra hT
    have hu : x ∈ Inside C.S p n := h (subset_closure hT)
    exact hx (show ∀ i a, _ < x i a ∧ x i a ≤ _ from fun i a => ⟨(hu i a).1, (hu i a).2.le⟩)
  simp_rw [densityCell,stair,indicator_of_notMem hx, hw, zero_mul]; exact tendsto_const_nhds

theorem intraperiod (Hp : Bound C f) (H : f.Meshes C P) {t : Test n} (h : suitable C.S p t) (v : Fin n → C.book.Token) :
    Integrable (fun x : Points n => t x * (P p).read x v) ∧
    Tendsto (fun j => smears C (f.mesh j) p v t) atTop (𝓝 (t.applyTo fun x => (P p).read x v)) := by
  classical
  obtain ⟨D, hD,Hb⟩ := Hp.cyclic n v p _ t.hasCompactSupport (readable C.S p t h)
  obtain ⟨R,H₁,H₂⟩ := testSup t
  let B := (Fund C.S p n).indicator (fun _ => R*D)
  have HI : Integrable B := (integrable_indicator_iff (full_box _ _ _).1).mpr
    (integrableOn_const (full_box _ _ _).2.ne)
  let F := fun j : ℕ => densityCell C (f.mesh j) p v t
  have Hs (j) : AEStronglyMeasurable (F j) volume := (stair_int _).aestronglyMeasurable
  have hb : ∀ᶠ j : ℕ in atTop, ∀ x, ‖F j x‖ ≤ B x := by
    filter_upwards [Hb] with i hi x
    by_cases he : x ∈ Fund C.S p n
    · unfold F B; rw [stepped C _ p he, indicator_of_mem he]
      let a := address (C.S.a (f.mesh i)) x
      let y := tag (C.S.a (f.mesh i)) a
      change ‖t y * lifted C (f.mesh i) p v a‖ ≤ _
      rcases eq_or_ne (t y) 0 with HT|HT
      · rw [HT,zero_mul,norm_zero]; exact mul_nonneg H₁ hD
      exact (norm_mul_le ..).trans (mul_le_mul (H₂ _) (hi a (subset_closure HT)) (norm_nonneg _) H₁)
    simp [F,B,densityCell,stair,he]
  have hg : ∀ᵐ x : Points n, Tendsto (fun j => F j x) atTop (𝓝 (t x * (P p).read x v)) :=
    (almostCyclic C.S p n).mono fun _ hx => f.mesh_pointwise C H h v hx
  constructor
  · refine HI.mono' (aestronglyMeasurable_of_tendsto_ae atTop Hs hg) ?_
    filter_upwards [hg] with x hx; exact le_of_tendsto hx.norm (hb.mono fun i hi => hi x)
  simp_rw [← exactSmear C]
  exact tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall Hs)
    (hb.mono fun i H => Eventually.of_forall H) HI hg

/-- Outer domination from genuine double eventuality plus mesh limits on every p. -/
theorem ring_bound (H : Bound C f) (hw : f.Meshes C P) (t : Test n) (v : Fin n → C.book.Token) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j : ℕ in atTop, ∀ x ∈ tsupport t, x ∈ generic n → ‖(P (f.per j)).read x v‖ ≤ D := by
  obtain ⟨K,hk,h₁,h₂⟩ := exists_compact_between t.hasCompactSupport (conf_open n)
    (show tsupport t ⊆ conf n from t.tsupport_subset)
  obtain ⟨D,hD,H⟩ := H.volume n v K hk h₂
  unfold late at H
  refine ⟨D,hD,?_⟩
  filter_upwards [H,f.per.cofinal.eventually (room C.S hk)] with i hi hr x hx hG
  let p := f.per i
  have ht : x ∈ Cyclic C.S p n := (no_wrap_tie C.S (hr (interior_subset (h₁ hx)))).mpr hG
  have hu := chosen (S := C.S) x |>.comp f.mesh.cofinal
  let a j := address (C.S.a (f.mesh j)) x
  have hg := f.evaluated C hw p n v x ht a hu
  refine le_of_tendsto hg.norm ?_
  filter_upwards [hi, hu.eventually (mem_interior_iff_mem_nhds.mp (h₁ hx))] with k hl hn
  exact hl _ hn

theorem ordinary (H : Bound C f) (hM : f.Meshes C P) (hp : f.VolumePoints C S P) (t : Test n) (v : Fin n → C.book.Token) :
    Integrable (fun x => t x * S.read x v) ∧
    Tendsto (fun i => t.applyTo fun x => (P (f.per i)).read x v) atTop (𝓝 (t.applyTo (fun x => S.read x v))) := by
  classical
  let K := tsupport t
  have he := f.per.cofinal.eventually (reading C.S t)
  let F := fun i x => t x * (P (f.per i)).read x v
  have ha : ∀ᶠ i : ℕ in atTop, Integrable (F i) := he.mono fun i hi => (f.intraperiod C H hM hi v).1
  obtain ⟨D,hD,Hb⟩ := f.ring_bound C H hM t v
  obtain ⟨R, hR, Hr⟩ := testSup t
  let B := K.indicator fun _ : Points n => R*D
  have hk : IsCompact K := t.hasCompactSupport
  have ht : ∀ᶠ i : ℕ in atTop, ∀ x, x ∈ generic n → ‖F i x‖ ≤ B x := by
    filter_upwards [Hb] with i hi x hg
    by_cases hx : x ∈ K
    · unfold B; rw [indicator_of_mem hx]
      exact (norm_mul_le ..).trans (mul_le_mul (Hr x) (hi x hx hg) (norm_nonneg _) hR)
    have hq : t x = 0 := by_contra fun w => hx (subset_closure w)
    simp [F,B,hq,hx]
  let Y := fun x => t x * S.read x v
  have hr : ∀ᵐ x : Points n, Tendsto (fun i => F i x) atTop (𝓝 (Y x)) := by
    filter_upwards [almostGeneric n] with x hx
    have hl : Tendsto (fun i => (P (f.per i)).read x v) atTop (𝓝 (S.read x v)) := by
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      filter_upwards [hp n {x} isCompact_singleton (singleton_subset_iff.mpr hx) v ε hε] with i hi
      simpa only [dist_eq_norm] using hi x (mem_singleton _)
    exact hl.const_mul (t x)
  have hy : Integrable B := (integrable_indicator_iff hk.measurableSet).mpr (integrableOn_const hk.measure_lt_top.ne)
  constructor
  · apply hy.mono'
    · obtain ⟨i,hi⟩ := eventually_atTop.mp ha
      exact aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun (j : ℕ) => F (i+j)) (fun j => (hi (i+j) (by omega)).aestronglyMeasurable)
        (hr.mono fun x hx => hx.comp (show Tendsto (fun (j : ℕ) => i+j) atTop atTop from
          (show StrictMono fun j => i+j from fun _ _ h => by simp only; omega).tendsto_atTop))
    filter_upwards [hr,almostGeneric n] with x hx hw
    exact le_of_tendsto hx.norm (ht.mono fun i hi => hi x hw)
  exact tendsto_integral_filter_of_dominated_convergence B (ha.mono fun i h => h.aestronglyMeasurable)
    (ht.mono fun i hi => (almostGeneric n).mono (hi ·)) hy hr

theorem poses (H : Bound C f) (h : f.PointLimits C S) : f.Ordered C S := by
  obtain ⟨P,hP,hY⟩ := h
  refine ⟨fun n v t => ⟨f.per.cofinal.eventually (reading C.S t), fun p => t.applyTo fun x => (P p).read x v,
    (fun i hi => (f.intraperiod C H hP hi v).2), (f.ordinary C H hP hY t v).2⟩⟩
end Order
end YM.Extraction
