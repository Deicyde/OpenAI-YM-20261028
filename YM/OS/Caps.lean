import YM.OS.Schwinger

/-! Use point cap, no cluster-volume bound needed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter MeasureTheory Analysis Word
open scoped Topology BigOperators NNReal
variable {G : Gauge} {L : Register G} {S : Table L}

/-- Positions of v and translated w sharing no seam. -/
def composite (v w : L.Word) (x : E4) : Points (v.length+w.length) :=
  points (Fin.append (positions v).ofLp (Points.across x (positions w)).ofLp)

lemma placements (v w : L.Word) (x : E4) : v ++ carry w x =
    realize (Fin.append (tokens v) (tokens w)) (composite v w x) := by
  let A := fun p : L.Plant => (p.1+x,p.2)
  let b := A ∘ w.get
  unfold realize
  have he : carry w x = List.ofFn b := by
    have ht : (List.ofFn w.get).map A= List.ofFn b := List.map_ofFn
    rw [List.ofFn_get] at ht; exact ht
  rw [he, show (fun i => ((composite v w x).ofLp i, Fin.append (tokens v) (tokens w) i)) = Fin.append v.get b from ?eq]
  · rw [List.ofFn_fin_append,List.ofFn_get]
  case eq =>
    ext1 i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [composite]; rfl
    intro j; simp [composite]; rfl

lemma translations_cont (v w : L.Word) : Continuous (composite v w) := by
  let n := v.length+w.length
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
  have he : Continuous (fun x : E4 => (composite v w x).ofLp) := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [composite]; exact continuous_const
    simp [composite]; fun_prop
  exact L.symm.continuous.comp he

lemma no_collision (a) (v w : Future L a) {x : E4} (hx : 0 ≤ x a) :
    composite (reflect v.val a) w.val x ∈ conf _ := by
  apply (realized _ _).1
  rw [← placements]
  apply twoSides v.property
  refine ⟨still w.property.1 x,?_⟩
  intro p hp; obtain ⟨q,h,rfl⟩ := List.mem_map.mp hp
  exact add_pos_of_pos_of_nonneg (w.property.2 _ h) hx

lemma uniformAway (a) (v w : Future L a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x : E4, 0 ≤ x a → spaced r (composite (reflect v.val a) w.val x) := by
  let A := reflect v.val a
  let p := composite A w.val
  have hs (i) : 0 < positions w.val i a := w.property.2 _ (List.get_mem ..)
  have ht (i) : positions A i a < 0 := strictly v.property (List.get_mem ..)
  have he (i : Fin (A.length+w.val.length)) (j : Fin (A.length+w.val.length)) : ∀ᶠ r : ℝ in 𝓝[>] 0, i ≠ j →
      ∀ x : E4, 0 ≤ x a → r ≤ cubedist (p x i) (p x j) := by
    rcases eq_or_ne i j with hk|hk
    · exact Eventually.of_forall fun _ h => (h hk).elim
    have hd : 0 < cubedist (p 0 i) (p 0 j) := by
      unfold cubedist
      exact dist_pos.mpr fun H => hk ((show Function.Injective _ from no_collision a v w (x := 0) le_rfl)
        (WithLp.ofLp_injective _ H))
    have hcr (s : Fin A.length) (t : Fin w.val.length) : ∀ᶠ r : ℝ in 𝓝[>] 0,
        ∀ (x : E4), 0 ≤ x a → r ≤ cubedist (positions A s) ((Points.across x (positions w.val)) t) := by
      filter_upwards [(gt_mem_nhds (hs t)).filter_mono nhdsWithin_le_nhds] with r hr x hx
      let Y := (Points.across x (positions w.val)) t
      apply le_trans _ (dist_le_pi_dist (positions A s).ofLp Y.ofLp a)
      rw [Real.dist_eq,abs_of_nonpos]
      · have Ht : r < positions w.val t a := hr
        change _ ≤ -(positions A s a - (positions w.val t a + x a))
        linarith [ht s]
      change positions A s a - (positions w.val t a+x a) ≤ 0
      linarith [ht s,hs t]
    revert hk hd
    refine Fin.addCases ?_ ?_ i
    · intro l
      refine Fin.addCases ?_ ?_ j
      · intro t H he
        filter_upwards [(gt_mem_nhds he).filter_mono nhdsWithin_le_nhds] with r hr h x hx
        simp only [p,composite,points_apply,Fin.append_left] at *
        exact le_of_lt hr
      intro t _ _
      filter_upwards [hcr l t] with r hr _ x hx
      simpa only [p, composite, points_apply, Fin.append_left, Fin.append_right] using hr x hx
    intro k
    refine Fin.addCases ?_ ?_ j
    · intro l _ _
      filter_upwards [hcr l k] with r hr _ x hx
      simp only [p, composite, points_apply, Fin.append_left, Fin.append_right, cubedist] at *
      rw [dist_comm]; exact hr x hx
    intro l _ he
    filter_upwards [(gt_mem_nhds he).filter_mono nhdsWithin_le_nhds] with r hr _ x hx
    simp only [p, composite, points_apply, Fin.append_right, Points.across_coord, add_zero] at *
    apply le_trans (le_of_lt hr)
    simp only [cubedist, WithLp.ofLp_add]
    rw [dist_add_right]
  have ht' : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioc 0 (1 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨r, hr,h'⟩ := (ht'.and (eventually_all.mpr fun i => eventually_all.mpr (he i))).exists
  exact ⟨r, hr.1, hr.2, fun x hx i j h => h' i j h x hx⟩

lemma correl (H : S.Hierarchy) (a : Axis) (v w : Future L a) :
    let f := fun x => S.expect (reflect v.val a ++ carry w.val x)
    ContinuousOn f {x | 0 ≤ x a} ∧ ∃ C : ℝ, ∀ x, 0 ≤ x a → ‖f x‖ ≤ C := by
  intro f
  let W := reflect v.val a
  let b := Fin.append (tokens W) (tokens w.val)
  let p := composite W w.val
  have he (x : E4) : f x = S.read (p x) b := by unfold f; rw [placements,Table.readAt]
  obtain ⟨r,hp, hr, h⟩ := uniformAway a v w
  constructor
  · rw [funext he]; exact ((S.smooth_read H.smooth b).continuousOn).comp
      (translations_cont W w.val).continuousOn (fun _ hx => no_collision _ _ _ hx)
  obtain ⟨A,D,-,hd⟩ := H.order _ (fun i => (b i).1) (fun i => (b i).2) 0
  refine ⟨D * r⁻¹^A, fun x hx => ?_⟩
  rw [he]; exact (norm_iteratedFDeriv_zero (𝕜 := ℝ) (x := p x) (f := fun y => S.read y b)).symm.trans_le (hd _ hp hr (p x) (h x hx))
end YM.OS
