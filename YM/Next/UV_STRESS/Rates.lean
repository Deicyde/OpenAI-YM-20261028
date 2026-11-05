import YM.Next.UV_STRESS.Station
import YM.Next.UV_STRESS.Weak

/-!
# One comparison curve extracted from estimates at finite weights, boxes and tolerances
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {C : Family G} {S : Table C.book} {F : Order} {n : ℕ}

/-- Rates here are independent of the cutoff & period indices. -/
structure Zoom where
  r : ℕ → ℝ
  positive : ∀ k, 0 < r k
  shrinking : StrictAnti r
  limits : Tendsto r atTop (𝓝 0)

abbrev sizeHint (k : ℕ) : ℝ := ↑k+1
abbrev costHint (k : ℕ) : ℝ := (sizeHint k)⁻¹
lemma cost_pos (k : ℕ) : 0 < costHint k := by unfold costHint sizeHint; positivity
lemma size_ascends : Tendsto sizeHint atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
lemma cost_clears : Tendsto costHint atTop (𝓝 0) := tendsto_inv_atTop_zero.comp size_ascends

lemma Stations.ranging {a : (Bel C.book).RealSpin} (T : Stations C F a) :
    ∃ (R : Zoom) (X : (k : ℕ) → Station C k),
      ∀ k, (X k).r=R.r k ∧ (X k).Admissible F a k (sizeHint k) (costHint k) := by
  have hv k δ (hd : 0<δ) := T.arbitrarily k k (sizeHint k) (costHint k) δ (by unfold sizeHint; simp) (cost_pos _) hd
  let Good (k : ℕ) := {X : Station C k // X.Admissible F a k (sizeHint k) (costHint k) ∧ X.r ≤ costHint k}
  let b : Good 0 := ⟨(hv 0 (costHint 0) (cost_pos _)).choose,(hv 0 _ (cost_pos _)).choose_spec⟩
  have he (k : ℕ) (X : Good k) : ∃ y : Good (k+1), y.val.r < X.val.r := by
    obtain ⟨Y,hY,H⟩ := hv (k+1) (min (X.val.r/2) (costHint _)) (lt_min (half_pos X.val.rad) (cost_pos _))
    exact ⟨⟨Y,hY,H.trans (min_le_right ..)⟩,(H.trans (min_le_left ..)).trans_lt (half_lt_self X.val.rad)⟩
  let p (k : ℕ) : Good k := Nat.rec b (fun k x => (he k x).choose) k
  have h (k : ℕ) : (p (k+1)).val.r < (p k).val.r := (he k (p k)).choose_spec
  refine ⟨⟨fun k => (p k).val.r,fun k => (p k).val.rad,strictAnti_nat_of_succ_lt h,?_⟩,
    fun k => (p k).val,fun k => ⟨rfl,(p k).property.1⟩⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun k => (p k).val.rad.le)
    (fun k => (p k).property.2)

lemma smoothDisc (ht : T.Smooth) (v : Fin n → T.Tag) : ContDiffOn ℝ ∞ (disc v) (conf n) := T.class_smooth T ht v

lemma smoothZoom (ht : T.Smooth) (v : Fin n → T.Tag) {r : ℝ} (hr : 0<r) :
    ContDiffOn ℝ ∞ (fun y => disc v (r • y)) (conf n) :=
  (smoothDisc ht v).comp (show ContDiff ℝ ∞ (fun p : Points n => r • p) by fun_prop).contDiffOn
    (fun x hx => (enlarged hr x).1 hx)

/-- No rank claims in this estimate. Same actual and free hierarchy; arbitrary
but fixed finite tuples. -/
structure Approaches (R : Zoom) (U : ℕ → Panel S) : Prop where
  values (n : ℕ) (v : Fin n → (Bel C.book).Tag) : Fades (fun k => tested (R.r k) (U k) v - disc v)

theorem Stations.build_curve {H : S.Hierarchy} (hs : F.Ordered C S) (h : (Bel C.book).Hierarchy)
    (ht : Stations C F h.spin) :
    ∃ (R : Zoom) (U : ℕ → Panel S),
      (∀ d, ∀ᶠ k in atTop, StraightAt H.spin h.spin (U k) d) ∧
        (∀ k, U k 0 ((Bel C.book).unit 0)=S.unit 0) ∧ Approaches R U := by
  obtain ⟨R,X,hX⟩ := ht.ranging
  choose U hU hu hz using fun k => harvested H hs h.spin (X k) (hX k).2
  refine ⟨R,U,fun d => (eventually_ge_atTop d).mono fun k hk => hU k d hk, hu,
    ⟨fun n v => ⟨fun k => (smoothZoom H.smooth (panels (U k) ∘ v) (R.positive k)).sub (smoothDisc h.smooth _),?_⟩⟩⟩
  intro s hK hC M hp ε he
  have hh : Tendsto (fun k => costHint k * Station.charge v * M) atTop (𝓝 0) := by
    simpa using (cost_clears.mul_const (Station.charge v)).mul_const M
  filter_upwards [eventually_ge_atTop n, eventually_all.mpr (fun i => eventually_ge_atTop (v i).1),
    size_ascends.eventually (Work.A05.compact_fits hK hC), hh.eventually (ge_mem_nhds he)] with k hk hs ht hx t hw hb
  -- signed integrals, no interchanging weak and continuum differentiations
  rw [test_sub]
  · rw [← (hX k).1]; exact (hz k n hk v hs t (hw.trans ht) M hp hb).trans hx
  · exact (smoothZoom H.smooth (panels (U k) ∘ v) (R.positive k)).continuousOn
  exact (smoothDisc (T:=(Bel C.book)) h.smooth v).continuousOn
end YM.Next.UVStress
