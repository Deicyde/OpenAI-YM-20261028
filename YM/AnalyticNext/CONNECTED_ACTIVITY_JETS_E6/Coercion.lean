import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Currents
import YM.Next.FREE_KERNELS.Amend
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Uniform Gram gap

Not assuming a uniform price on the stacked real action; using a single
accepted branch in-the-row for the floor, all directions in upper. Diagonal
completion only pays ghost at unused. `energized` uses physical Theta etc
not as split ordonnance of its own. Scheduling resumes at bound assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F)

def swept (L : Side) (d : ℕ) := (ballCost d:ℝ)*(L.val^4*Fintype.card Axis:ℕ)

lemma along_age {Z M : ℝ} (he : 2*M^2 * swept S.patch.L (3*X.B) ≤ 1/2) (u : Directions G f)
    (h : ∀ i : Bond f, ‖X.lens u i‖ ≤ Z*X.response (atEdge S i) u + M*X.current (atEdge S i) u) :
    ∑ i, ‖X.lens u i‖^2 ≤ 4*Z^2 * swept S.patch.L (Pressure.macroR S.patch+2) * ∑ p, ‖X.motion u p‖^2 := by
  let W := ∑ i, ‖X.lens u i‖^2; let V := ∑ p, ‖X.motion u p‖^2
  let L := S.patch.L; let d := Pressure.macroR S.patch+2
  have hk i : ‖X.lens u i‖^2 ≤ 2*Z^2 * (X.response (atEdge S i) u)^2 + 2*M^2 * (X.current (atEdge S i) u)^2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (h i) _).trans ?_
    nlinarith only [sq_nonneg (Z*X.response (atEdge S i) u - M*X.current (atEdge S i) u)]
  have ha : ∑ i, (X.response (atEdge S i) u)^2 ≤ swept L d*V := by
    have hp (i : Bond f) : (X.response (atEdge S i) u)^2=∑ j∈withinH (root S) (atEdge S i) (Pressure.macroR S.patch+2), ‖X.motion u j‖^2 := by rw [response,Real.sq_sqrt (by positivity)]
    simp_rw [hp]
    exact for_neighbors (perch S) _ (fun i => sq_nonneg _) _ _
  have hb : ∑ i, (X.current (atEdge S i) u)^2 ≤ swept L (3*X.B)*W := by
    have hp (i : Bond f) : (X.current (atEdge S i) u)^2=∑ j∈withinH (atEdge S) (atEdge S i) (3*X.B), ‖X.lens u j‖^2 := by rw [current,Real.sq_sqrt (by positivity)]
    simp_rw [hp]
    exact for_neighbors (perch S) _ (fun i => sq_nonneg _) _ _
  have hp := (Finset.sum_le_sum (s:=univ) (fun i _ => hk i))
  rw [sum_add_distrib, ← mul_sum,← mul_sum] at hp
  have hs : 2*M^2 * ∑ i, (X.current (atEdge S i) u)^2 ≤ 1/2*W := by
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans ?_; rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right he (by unfold W; positivity)
  change W ≤ 4*Z^2*swept L d*V
  apply le_of_mul_le_mul_left _ (show 0 < (1/2:ℝ) by norm_num)
  linarith only [show W≤_ from hp.trans (add_le_add (mul_le_mul_of_nonneg_left ha (show 0 ≤ 2*Z^2 by positivity)) hs)]

lemma raised (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) : ∃ a : ℝ, 0 < a ∧
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
      X.x=x → S.patch=D → S.patch.L=L → Room P S T X.x → X.manifest →
      ∀ u : Directions G f, ∑ i, ‖X.lens u i‖^2 ≤ a * ∑ p, ‖X.motion u p‖^2 := by
  obtain ⟨C,hC,hX⟩ := bounded_stencils P D hd
  obtain ⟨K,hK,H⟩ := cops_at G P L
  obtain ⟨s,hs,hg⟩ := flattening P L
  let U := units P K D
  have hU : 0<U := units_pos P hK.le D
  obtain ⟨Y,r,hY,hr,hW⟩ := chord_chart_cost G
  let M x := U*(C*(2*G.colorScale*((radiusB x:ℝ)+1)*(Y*s x)))
  let Z x := 2*M x^2 * swept L (3*radiusB x)
  have ht : Rate G L (-(1/2)) M := by
    have hh := (((((Rate.radius_price.add (Rate.const 1)).mul_left (2*G.colorScale)).mul (hs.mul_left Y)).mul_left C).mul_left U)
    simpa only [zero_add] using! hh
  have hz : Rate G L ((-(1/2))*(2:ℕ)+0:ℝ) Z := by
    have he := Census.width_rate G L 3 0; simp only [add_zero] at he
    exact Rate.mul ((ht.pow 2).mul_left 2) (he.mul_right _)
  have hh : 0 ≤ swept L (Pressure.macroR D+2) := by unfold swept; positivity
  refine ⟨1+4*U^2*swept L (Pressure.macroR D+2),by positivity,?_⟩
  filter_upwards [hz.below (by norm_num) _ (show (0:ℝ) < 1/2 by norm_num), hs.below (by norm_num) _ hr, hg]
    with x hx hs he c f S T F X ha hS hL hR hy u
  subst x
  obtain ⟨hn,he⟩ := he
  have hm (i : Bond f) : ‖X.lens u i‖ ≤ U*X.response (atEdge S i) u+ M X.x*X.current (atEdge S i) u := by
    by_cases h : X.Hot i
    swap
    · simp only [lens,h,↓reduceIte,norm_zero]
      have hM : 0 ≤ M X.x := by have := G.colorScale_pos; unfold M; positivity
      unfold current response; positivity
    let o := atEdge S i
    have hp := active_far X.seeds i h
    have hv : Clean X.V X.x o (2*X.B+1) := clean_far X.seeds X.V hy (fun he =>
      hp (Corona.halo_mono (by have hs : 100≤X.B := hR.sight.1; omega) (by rfl) he))
    obtain ⟨z,b,h',hb⟩ := he c f S T hL hR X.V o (2*X.B) (by unfold Coat.B; omega) hv
    have hn j (hl : separation o (Prod.fst j) ≤ 2*X.B) : G.chord (gauge z X.V j) ≤ Y*s X.x := by
      have h := (norm_le_pi_norm b (pole j)).trans hb
      rw [h' j hl,Work.F03.represent_link]; exact (hW _ ((h.trans (le_abs_self _)).trans hs)).trans (mul_le_mul_of_nonneg_left h hY.le)
    apply (X.driving hR hC (hX c f S T hS hR.accepted) hK.le i
      (fun U hu hv => H S T X.x hL hR F U 1 X.k hu i hv) h z (show 0 ≤ Y*s X.x by positivity) hn u).trans_eq
    rw [show units P K S.patch = U by unfold U; rw [hS], mul_add,←mul_assoc]
  have hi : 2*(M X.x)^2 * swept S.patch.L (3*X.B) ≤ 1/2 := by rw [hL]; exact (le_abs_self (Z X.x)).trans hx
  apply (X.along_age hi u hm).trans; apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [hL, hS]; linarith

lemma sleepy_act (v : Tubular f G → ℝ) (i : Tubular f G) : (X.sleepy *ᵥ v) i = if X.Hot i.1 then 0 else v i := by
  change dotProduct _ _ = _
  unfold dotProduct; rw [sum_eq_single i]
  · by_cases he : X.Hot i.1 <;> simp [sleepy,he]
  · intro j _ hi; simp [sleepy,hi.symm]
  simp

lemma lens_split (u : Directions G f) :
    dotProduct (stand u) (stand u) = dotProduct (stand (X.lens u)) (stand (X.lens u)) +
      dotProduct (stand u) (X.sleepy *ᵥ stand u) ∧ 0 ≤ dotProduct (stand u) (X.sleepy *ᵥ stand u) := by
  unfold dotProduct; constructor
  · rw [← sum_add_distrib]; apply sum_congr rfl; intro i _
    by_cases he : X.Hot i.1 <;> simp [sleepy_act X _ i, lens,stand,he]
  apply sum_nonneg; intro i _; by_cases he : X.Hot i.1 <;> simp [sleepy_act X _ i, he,mul_self_nonneg]

lemma counted_up {q Ω C Λ} (h : T.up.Bounds q Ω C Λ) (x : Directions G f) :
    scale^2 * (∑ i, ‖X.motion x i‖^2)=dotProduct (stand x) ((X.form.transpose * X.form) *ᵥ stand x) := by
  rw [stand_squared, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ X.form.transpose, Matrix.vecMul_transpose]
  unfold dotProduct; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  rw [← X.charged_for h]; ring

lemma energized (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
      X.x=x → S.patch=D → S.patch.L=L → Room P S T X.x → X.manifest → Green.Bottom X.plate A := by
  obtain ⟨a,ha,h⟩ := raised P L D hd
  let k := min (scale^2/a) 1
  have ht := scale_pos
  have hk : 0 < k := lt_min (by positivity) zero_lt_one
  refine ⟨k,hk,?_⟩
  filter_upwards [h] with x H c f S T F X h HS hL hR hh v
  obtain ⟨Ω,Q,hu,-⟩ := hR.accepted.feeds
  let t := erect G v
  obtain ⟨hh',he⟩ := X.lens_split t
  have hx : k*dotProduct (stand (X.lens t)) (stand (X.lens t)) ≤ dotProduct v ((X.form.transpose*X.form) *ᵥ v) := by
    change _ ≤ dotProduct (stand t) ((X.form.transpose * X.form) *ᵥ stand t)
    rw [← stand_squared,← X.counted_up hu]
    apply (mul_le_mul_of_nonneg_left (H c f S T F X h HS hL hR hh t) hk.le).trans
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_div_iff₀ ha).mp (min_le_left _ _)) (by positivity)
  change k*dotProduct (stand t) (stand t) ≤ _
  rw [hh',plate,Matrix.add_mulVec, dotProduct_add,mul_add]
  exact add_le_add hx (mul_le_of_le_one_left he (min_le_right _ _))
end YM.ConnectedActivityE6.Coat
