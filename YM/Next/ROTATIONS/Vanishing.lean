import YM.Next.ROTATIONS.Cove
/-!
# External packets go home. Weights are honest collinear word/projected-probe
kernels. No hypothesis of the rotation identity in these arguments.
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS Table Ward
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L}

def chart (a b l : Axis) (d : Axis) : ℝ := if d=a ∨ d=b then -100 else if d=l then -150 else -300
lemma chart_symm (a b l : Axis) : chart a b l=chart b a l := funext fun i => by unfold chart; simp only [or_comm]
lemma chart_bounds (a b l i : Axis) : -300 ≤ chart a b l i ∧ chart a b l i≤ -100 := by unfold chart; split_ifs <;> norm_num
lemma chart_here (a b l : Axis) : -150 ≤ chart a b l l := by by_cases h : l=a ∨ l=b <;> norm_num [chart,h]
lemma chart_there (a b l : Axis) : chart a b l b= -100 := by simp [chart]
lemma chart_away (a b l i : Axis) (h : i≠a) (e : i≠b) : chart a b l i= if i=l then -150 else -300 := by simp [chart,h,e]
lemma mixesLine (a b l : Axis) (h : a≠b) : Mixed (other l) (spar a b) ∧ ∃ i∈other l,spar a b i≠spar a b l := by
  -- avoid nonkernel decide proof dependence
  have hx : ∃ j : Axis, j∈other l ∧ spar a b j=false := by
    have ht : ∀ a b l : Axis, ∃ i : Axis, i∈other l ∧ spar a b i=false := by decide
    exact ht a b l
  have he : ∃ j : Axis, j∈other l ∧ spar a b j=true := by
    by_cases he:a=l
    · subst l; exact ⟨b,apart (Ne.symm h),by simp [spar,Ne.symm h]⟩
    exact ⟨a,apart he,by simp [spar,h]⟩
  obtain ⟨i,hi,hx⟩ := hx; obtain ⟨j,hj,he⟩ := he
  refine ⟨mix_if_both _ _ _ _ hi hj (by simp [hx,he]),?_⟩
  cases H : spar a b l
  · exact ⟨j,hj,by simp [he]⟩
  exact ⟨i,hi,by simp [hx]⟩

lemma partition_cross {d : Axis} (V : Chamber S d) (B A : Weight L) (f : E4→ℂ) (hf : fits V B A f)
    (s : Set E4) (hs : MeasurableSet s) : cross V B A (s.indicator f) + cross V B A (sᶜ.indicator f)=cross V B A f := by
  unfold cross; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add,integral_indicator hs,integral_indicator hs.compl,integral_add_compl hs (hf i)]
lemma track_sale (w : Axis→ℝ) (d : Axis) (V : Chamber S d) (H : S.Hierarchy) (B A : Weight L) (x y : Bool)
    (hx : Own B d x) (hy : Own A d y) (f : Panels) (hw : w d<0) (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) :
    ∀ᶠ n in atTop, Integrable (fun q => readsCluster S B A q * positionTest (tracks w d n f) q) ∧
    fits V B A (answer d (signValue x * signValue y) (tracks w d n f)) ∧
    signValue x * (∫ q, readsCluster S B A q * positionTest (tracks w d n f) q)=
      (toll:ℂ)*cross V B A (answer d (signValue x * signValue y) (tracks w d n f)) := by
  obtain ⟨u,hU,hV⟩ := ((descends d B).and (descends d A)).exists
  let e := signValue x * signValue y
  have he : ‖e‖=1 := by unfold e; rw [norm_mul]; cases x <;> cases y <;> simp [signValue]
  filter_upwards [track_far w d hw f h ((u+u:ℝ≥0):ℝ)] with n hn
  exact cross_slice V H B A hx hy _ (fun t h ht => ⟨u,hU,hV,hn t ht⟩)
    (fun j => runs_gap V H _ u (meets_air _ _ _ hU hV j) e he _ hn)

private lemma normal (w : Axis→ℝ) (d : Axis) (V : ∀ i, Chamber S i) (A : Weight L) (K : ℝ) (hw : ∀ i, -K≤1+w i) :
    Budget (K*3) (fun n => integral (ν (V d) A) (due w d 0 n)) := by
  let T := other d
  let M := ∏ _i∈T,SchwartzMap.seminorm ℝ 0 0 center
  let μ := ν (V d) A
  let X := ∫ p,low d 1 p ∂μ
  apply ((((budget_fuel (K*3)).times M).prod (constant_budget X)).rise (by simp)).priced
  filter_upwards with n; change ‖∫ p,due w d 0 n p ∂μ‖ ≤ M*fuel (K*3) n* X
  unfold X; rw [← integral_const_mul]; refine norm_integral_le_of_norm_le ((low_int V d A 1 (by norm_num)).const_mul _) ?_
  filter_upwards [before (V d) A] with p hp
  have hh : ‖crop (other d) (homes w n) p‖ ≤ M*fuel (K*3) n := by
    convert sum_cash (fun j => 1+w j) (fun _ => center) K n T (fun i _ => hw i) p using 1
    unfold M; simp [T,other]
  rw [due,cost,norm_mul,fuel0,mul_comm (M*_)]
  rw [Real.norm_of_nonneg (low_nn _ _ _ one_pos hp)]
  exact mul_le_mul_of_nonneg_left hh (low_nn _ _ _ one_pos hp)

lemma exterior_size (a b l d : Axis) (hd : d≠a) (hh : a≠b) (P : DiffPlan S) (hP : P.Derivatives S) (V : ∀ i, Chamber S i) (H : S.Hierarchy) (hi : P.Orientation H.spin)
    (J : Stress S) (hr : RawTensor H.spin J) (C : Conserved P H.spin J) (B A : Weight L) (he : equalRead S A (pick (J d b)))
    (hB : ∀ i,Own B i (spar a b i)) (hu : ∀ i∈other l,Pressed i B) (hA : ∀ i,Own A i (spar d b i)) (hg : ∀ i,Pressed i A)
    (f : Panels) (hf : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) :
    Budget (-101) (fun n => ∫ q, readsCluster S B A q * positionTest (tracks (chart a b l) d n f) q) := by
  let w := chart a b l; let e := signValue (spar a b d)*signValue (spar d b d)
  have hk i := chart_bounds a b l i
  change ∀ i,-300≤w i ∧ w i ≤ -100 at hk
  have hw i : w i < 0 := lt_of_le_of_lt (hk i).2 (by norm_num)
  have hj : ‖e‖=1 := by unfold e; rw [norm_mul]; cases spar a b d <;> cases spar d b d <;> simp [signValue]
  have hy := track_sale w d (V d) H B A _ _ (hB d) (hA d) f (hw d) hf
  have hz := ice w d (V d) H B A f hf 300 (fun i => (hk i).1) (hw d) e hj (-101)
  have hl := mixesLine a b l hh
  have hW i : 1+w i ≤ 0 := by linarith [(hk i).2]
  have hG : Colors Finset.univ (fun _ => center) := fun _ _ => ⟨center_ends,center_plus,center_even⟩
  let u := if d=l then (1:ℝ) else -(1+w l)+1
  let X := jar w d f e
  have hX : ∀ᶠ n in atTop, fits (V d) B A (X n) := hy.mono fun n hn j => (hn.2.1 j).indicator (cove_m ..)
  let T := due w d (-3000)
  have hT : Budget u (fun n => integral (ν (V d) B) (T n)) := line_cost V H l _ B hB hl.1 hl.2 hu d (fun i => 1+w i) hW 1 (-3000) (by norm_num) (by norm_num) _ hG
  have hY n : Integrable (T n) (ν (V d) B) := cost_int V d B _ (fuel_pos ..) _ _
  have ht : u≤150 := by
    have he : -150 ≤ w l := chart_here ..; unfold u; split_ifs <;> linarith
  have hp : Budget (-101) (fun n => cross (V d) B A (X n)) := by
    by_cases hc:d=b
    · subst b
      have hA : Own A d false := by simpa [spar] using hA d
      have hD : w d= -100 := chart_there ..
      let z := fun n => coneWeight d (fuel (-99) n) (homes w n)
      obtain ⟨hm,hs⟩ := mass V H J P hP hi hr C d A he hA (hg d) (fun i => 1+w i) (-99) (by norm_num)
        (fun i _ => by linarith [(hk i).2]) _ hG 1 (by norm_num)
      obtain ⟨M,hM,hN⟩ := bead_size w d f e hj hf (-3000) (-99) (by linarith)
      obtain ⟨N,hL,hO⟩ := mote_size w d f e hj hf (-3000)
      let Y n := cave d (-3000) n
      have hF : Budget (-101) (fun n => cross (V d) B A ((Y n).indicator (X n))) :=
        (balanced_mul (V d) B A _ (hX.mono fun n hn i => (hn i).indicator (cave_m ..)) u (1+(-99)*4) T z hY hm hT hs 3 M hM (fun n p H => ⟨due_nn _ _ _ _ p H,cone_nn _ _ _ (home_lit w n) p (fuel_pos ..) H,hN n p H⟩)).rise (by linarith)
      let U := due w d 0
      have hS := normal w d V A 300 (fun i => by linarith [(hk i).1])
      have hB : Budget (-101) (fun n => cross (V d) B A ((Y n)ᶜ.indicator (X n))) :=
        (balanced_mul (V d) B A _ (hX.mono fun n hn i => (hn i).indicator (cave_m .. |>.compl)) u (300*3) T U hY
          (fun n => cost_int V d A _ (fuel_pos ..) _ _) hT hS (3+(-3000)/2) N hL (fun n p H => ⟨due_nn _ _ _ _ p H,due_nn _ _ _ _ p H,hO n p H⟩)).rise (by linarith)
      exact (hF.add hB).same (hX.mono fun n hn => partition_cross _ _ _ (X n) hn _ (cave_m ..))
    let z := due w d (w d)
    obtain ⟨M,hM,hN⟩ := shear_size w d f e hj hf (-3000) (by linarith [(hk d).1])
    have hF : Budget 1 (fun n => integral (ν (V d) A) (z n)) := point_cost V H d A _ Finset.univ (Finset.mem_univ _) (spar_both d b hc) (fun i _ => hg i) (fun i _ => hA i) (fun i => 1+w i) (fun i _ => hW i) (w d) (hw d) _ hG 1 (by norm_num)
    refine (balanced_mul (V d) B A X hX u 1 T z hY (fun n => cost_int V d A _ (fuel_pos ..) _ _) hT hF (3+w d) M hM (fun n p H => ⟨due_nn _ _ _ _ p H,due_nn _ _ _ _ p H,hN n p H⟩)).rise ?_
    rw [show w d= _ from chart_away a b l d hd hc]; unfold u at *
    split_ifs with h <;> simp only [h, if_true, if_false] at ht <;> linarith
  have hQ : Budget (-101) (fun n => cross (V d) B A (answer d e (tracks w d n f))) :=
    (hp.add hz).same (hy.mono fun n hn => partition_cross _ _ _ _ hn.2.1 _ (cove_m ..))
  apply ((hQ.times (toll:ℂ)).times (signValue (spar a b d))).same (hy.mono fun n hn => ?_)
  change signValue _*((toll:ℂ)*cross (V d) B A (answer d _ _)) = _
  rw [← hn.2.2,← mul_assoc,sign_sq,one_mul]
end YM.Outer
