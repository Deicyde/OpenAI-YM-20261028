import YM.Next.FLUCTUATIONS.Charts

/-!
# X and X' on the chart

Pay every path term's true length (including plaquette); no claim they
are short on the cover merely because of a short torus displacement.
Fields use real exponential charts, global small extension at this
point. Post-L.  for these pieces.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side}

-- Sum over path terms (not necessarily finite even before or after cutoff).
private lemma sum_path_cost (F : ℕ → G.Color) (g : ℕ → ℝ) (C D : ℝ) (hd : 0≤D)
    (h : SumBudget g C) (hf : ∀ i, ‖F i‖ ≤ g i * D) : ‖∑' i, F i‖ ≤ C*D := by
  have he : Summable fun i => ‖F i‖ := (h.2.1.mul_right D).of_nonneg_of_le (fun i => norm_nonneg _) hf
  apply (norm_tsum_le_tsum_norm he).trans
  apply (he.tsum_le_tsum hf (h.2.1.mul_right D)).trans
  rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hd

lemma shorten_summable {p : Clip} (P : PathData G) (U : Config G n) {σ C Λ}
    (hp : P.Bounds p σ C Λ) (R d : ℕ) (b : Cell n) : Summable (shortenTerm P R d U b) := by
  apply Summable.of_norm_bounded ((P.ell_dominated hp b).absolute U)
  intro i; dsimp only [shortenTerm]; split <;> simp

-- R and d measured in fine units.
private lemma slot_within (W : Config G n) (a : LogField G n) (q : Site n) (s : Slot)
    (R d : ℕ) (hd : 1 ≤ d) (he : s.length*d ≤ R) (A B h : ℝ) (hA : 0≤A) (hB : 0≤B) (hh : 0≤h)
    (hv : ∀ i, G.chord (W i) ≤ B*h) (hf : ∀ x : Cell n, ‖faceCurl x a‖ ≤ A*h ∧
      ‖G.curvature (faceValue W x) - faceCurl x a‖ ≤ A*h^2) (τ : ℝ) :
    ‖s.atSite W q - faceCurl (slotFace s q) a‖ ≤ A*(1+2*G.colorScale*B)*h * widen R h τ := by
  let x := slotFace s q
  let y := faceCurl x a
  let u := G.curvature (faceValue W x)
  let t := travel W q s.walk
  have hr : (s.walk.length : ℝ) ≤ R := by
    have he' := le_trans (show s.walk.length ≤ s.length from by unfold Slot.length; omega)
      ((le_mul_of_one_le_right (Nat.zero_le _) hd).trans he)
    exact_mod_cast he'
  have ht : G.chord t ≤ R*(B*h) := (travel_chord W s.walk q (B*h) hv).trans
    (mul_le_mul_of_nonneg_right hr (mul_nonneg hB hh))
  let D := 2 * G.colorScale * B
  have hS := G.colorScale_pos
  have hm : 2 * G.colorScale * G.chord t ≤ D*R*h := calc
    _ ≤ 2*G.colorScale*(R*(B*h)) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by unfold D; ring
  rw [atSite_path]
  change ‖G.adjoint t u - y‖ ≤ A*(1+D)*h * _
  calc
    _ ≤ ‖G.adjoint t u - G.adjoint t y‖ + ‖G.adjoint t y - y‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ A*h^2 + D*R*h * (A*h) := add_le_add (by rw [← map_sub,G.norm_adjoint]; exact (hf x).2)
      ((adjoint_norm_sub t y).trans (mul_le_mul hm (hf x).1 (norm_nonneg _) (by unfold D; positivity)))
    _ = A*h*h*(1+D*R) := by ring
    _ ≤ A*h*h*((1+D)*(1+R)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      have he : 0≤D := by unfold D; positivity
      linarith
    _ = A*(1+D)*h*((1+R)*h) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) (by unfold D; positivity)

private lemma tail_price {R d : ℕ} {σ h : ℝ} (hd : 0<d) (hs : 0≤σ) (hh : 0≤h)
    (s : Slot) (he : ¬ s.length*d ≤ R) : 1 ≤ Real.exp (σ*s.length) * widen R h (σ/d) := by
  have hx : (R:ℝ) ≤ s.length * (d:ℝ) := by exact_mod_cast le_of_lt (Nat.lt_of_not_ge he)
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  calc
    1 ≤ Real.exp (σ*s.length)*Real.exp (-(σ/d)*R) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have hv : σ/d*R ≤ σ*s.length := calc
        _ ≤ σ/d*(s.length*(d:ℝ)) := by gcongr
        _ = _ := by field_simp
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg (by positivity) hh))
      (Real.exp_pos _).le

lemma x_chart_cost (G : Gauge) (m : Stage) (d : ℕ) (hd : 0<d) :
    ∃ (C r : ℝ), 0<C ∧ 0<r ∧
    ∀ (n : Side) (P : PathData G) (Λ : ℝ), P.Bounds m.clip m.width m.paths Λ →
    ∀ (R : ℕ) (a : LogField G n) (h : ℝ), ‖a‖ ≤ h → h ≤ r → ∀ i,
      ‖xLin m.clip P a i‖ ≤ C * h ∧
      ‖plotted P m.clip R d (represent a) i - xLin m.clip P a i‖ ≤ C*h*widen R h (m.width/d) := by
  obtain ⟨A,r,hA,hr,ha⟩ := face_chart_cost G
  obtain ⟨B,v,hB,hv,hb⟩ := chord_chart_cost G
  let J := A*(1+2*G.colorScale*B)
  let Y := Real.sqrt m.clip.direct*A
  let C := Y + m.paths * J
  have hp := m.paths_pos
  have hh : 0 ≤ 2*G.colorScale*B := by have := G.colorScale_pos; positivity
  have hJ : A ≤ J := le_mul_of_one_le_right hA.le (by linarith)
  have hj : 0 < J := hA.trans_le hJ
  have hY : 0 ≤ Y := by unfold Y; positivity
  have he : m.paths * J ≤ C := le_add_of_nonneg_left hY
  have hl : Y ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C,min r v, (mul_pos hp hj).trans_le he, lt_min hr hv,?_⟩
  intro n P Λ hP R a h ht hk i
  let w := widen R h (m.width/d)
  have hn : 0≤h := (norm_nonneg _).trans ht
  have hv := widen_nonneg (τ:=m.width/d) R hn
  have hf (x : Cell n) : ‖faceCurl x a‖ ≤ A*h ∧ ‖G.curvature (faceValue (represent a) x) - faceCurl x a‖ ≤ A*h^2 := by
    obtain ⟨hs,he⟩ := ha a x
    refine ⟨hs.trans (by gcongr), (he (ht.trans (hk.trans (min_le_left ..)))).trans ?_⟩
    gcongr
  rcases i with ⟨x,b|b⟩
  · have hi := hf x
    simp only [xLin,plotted,Bool.false_eq_true,↓reduceIte,shoot, ← smul_sub,norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    refine ⟨?_,?_⟩
    · apply le_trans (mul_le_mul_of_nonneg_left hi.1 (Real.sqrt_nonneg _))
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hl hn
    apply le_trans (mul_le_mul_of_nonneg_left hi.2 (Real.sqrt_nonneg _))
    rw [sq,← mul_assoc,← mul_assoc]; exact mul_le_mul (mul_le_mul_of_nonneg_right hl hn)
      (le_widen _ hn) hn (mul_nonneg (hY.trans hl) hn)
  · have hc (i : Bond n) : G.chord (represent a i) ≤ B*h := by
      have hi := (norm_le_pi_norm a (pole i)).trans ht
      change G.chord (G.lieExp _ * 1) ≤ _
      rw [mul_one]; exact (hb _ (hi.trans (hk.trans (min_le_right ..)))).trans (by gcongr)
    let u i := (P.row x.2 i).1
    let p i := (P.row x.2 i).2
    let M i := Real.exp (m.width * (p i).length)
    let W i := |u i| * M i
    let f i := u i • faceCurl (slotFace (p i) x.1) a
    let g := shortenTerm P R d (represent a) x
    have hw : SumBudget W m.paths := hP.rows x.2
    have hm i : 1 ≤ M i := Real.one_le_exp (by have := m.width_pos; positivity)
    have hu i : |u i| ≤ W i := le_mul_of_one_le_right (abs_nonneg _) (hm _)
    change ‖∑' i, f i‖ ≤ _ ∧ ‖(∑' i, g i) - ∑' i, f i‖ ≤ _
    refine ⟨(sum_path_cost f W _ (J*h) (mul_nonneg hj.le hn) hw ?_).trans ?_,?_⟩
    · intro i; dsimp only [f]; rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hu i) ((hf _).1.trans (mul_le_mul_of_nonneg_right hJ hn))
        (norm_nonneg _) (hw.1 i)
    · rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right he hn
    have hg : Summable g := shorten_summable _ _ hP _ _ _
    rw [← hg.tsum_sub (ellLine_summable _ hP ..)]
    refine (sum_path_cost _ W _ (J*h*w) (by change 0 ≤ _*_ * widen ..; positivity) hw ?_).trans ?_
    · intro i
      dsimp only [g,shortenTerm,PathData.ellTerms]
      split
      next hi =>
        change ‖u i • (p i).atSite _ _ - u i • faceCurl _ a‖ ≤ _
        rw [← smul_sub,norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hu i) (slot_within _ a x.1 (p i) R d hd hi A B h hA.le hB.le hn hc hf (m.width/d))
          (norm_nonneg _) (hw.1 i)
      next hi =>
        have ht := tail_price (R:=R) (σ:=m.width) hd m.width_pos.le hn (p i) hi
        rw [zero_sub,norm_neg,show ‖f i‖ = |u i| * ‖faceCurl _ a‖ by unfold f; rw [norm_smul,Real.norm_eq_abs]]
        rw [show W i * (J*h*w) = |u i| * ((J*h) * (M i*w)) by unfold W; ring]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact ((hf _).1.trans (mul_le_mul_of_nonneg_right hJ hn)).trans
          (le_mul_of_one_le_right (mul_nonneg hj.le hn) ht)
    · simp only [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hn) hv
end YM.Next.Fluctuations
