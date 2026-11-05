import YM.Next.UV_STRESS.Fringe

/-!
# Cost powers in normalized comparison regimes.

E strip estimate. Haar volume in normalized Euclidean points incl ties.
All axes count in stripe geometry. Reassemble BEFORE invoking comparison
jets/combinatorics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Climb Ward
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} {n D : ℕ}

section stripes

abbrev Couples (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}
open Matrix
private lemma stripe_cost (p : Couples n × Axis) {R σ : ℝ} (hr : 0 ≤ R) (hs : 0 ≤ σ) :
    volume (Scaling.window R n ∩ {x| |Gaps.distances x p.1.val.1 p.1.val.2 p.2| ≤ 8*σ}) ≤
      ENNReal.ofReal ((16*σ)*(2*R)^(n*4-1)) := by
  rcases p with ⟨⟨⟨i,j⟩,hp⟩,a⟩
  let I := (i,a); let J := (j,a)
  have hh : J ≠ I := fun h => hp (Prod.mk.inj h.symm).1
  let T : Matrix.TransvectionStruct (Fin n × Axis) ℝ := ⟨J,I,hh,-1⟩
  let f := Matrix.toLin' T.toMatrix
  have ht := (Real.volume_preserving_transvectionStruct T).comp (preserves (n:=n))
  have hE : MeasurePreserving (f ∘ flat n) volume volume := ht
  let W (p : Fin n × Axis) := if p=J then Icc (-(8*σ)) (8*σ) else Icc (-R) R
  have hw : MeasurableSet (univ.pi W) := MeasurableSet.pi countable_univ fun i _ => by unfold W; split <;> exact measurableSet_Icc
  have hu (x) (y : Fin n × Axis) : (f ∘ flat n) x y = (flat n x) y - (if y=J then flat n x I else 0) := by
    by_cases h : y=J <;> simp [f,T,Matrix.transvection,Matrix.single_mulVec,h,sub_eq_add_neg]
    subst y; rfl
  refine (measure_mono (t:=(f ∘ flat n) ⁻¹' univ.pi W) ?_).trans_eq ?_
  · intro x hx l _
    obtain ⟨hx,hF⟩ := hx
    unfold W; rw [hu]
    split_ifs with he
    · subst l; exact abs_le.mp hF
    rw [sub_zero]; exact abs_le.mp (((PiLp.norm_apply_le (x l.1) l.2).trans (PiLp.norm_apply_le x l.1)).trans hx.2)
  rw [hE.measure_preimage hw.nullMeasurableSet,volume_pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun i => volume (W i)) (Finset.mem_univ J)]
  have he (p : Fin n × Axis) (h : p∈Finset.univ.erase J) : volume (W p)=ENNReal.ofReal (2*R) := by
    unfold W; rw [if_neg (Finset.ne_of_mem_erase h),Real.volume_Icc]; ring_nf
  rw [Finset.prod_congr rfl he, Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ J), Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_fin, show W J = _ from if_pos rfl, Real.volume_Icc,
    show 8*σ - -(8*σ)=16*σ by ring,ENNReal.ofReal_mul (by positivity : 0 ≤ 16*σ), ENNReal.ofReal_pow (by positivity)]

def cost_band (n : ℕ) (R : ℝ) : ℝ := ∑ _ : Couples n × Axis, (16:ℝ)*(2*R)^(n*4-1)


/-- Linear cost through arbitrarily many stripes meeting each other. n=0,1
includes empty strip region. -/
lemma band_cover (R : ℝ) (hr : 0 ≤ R) (σ : ℝ) (hs : 0 ≤ σ) :
    volume.real (Scaling.window R n \ openFilm n (8*σ)) ≤ cost_band n R*σ := by
  let W (p : Couples n × Axis) := Scaling.window R n ∩ {x| |Gaps.distances x p.1.val.1 p.1.val.2 p.2| ≤ 8*σ}
  let A := Scaling.window R n \ openFilm n (8*σ)
  have he : A ⊆ ⋃ p,W p := by
    intro x hx; obtain ⟨ht,hs⟩ := hx; change ¬ ∀ i j, i≠j → ∀ a, 8*σ < |Gaps.distances x i j a| at hs
    push Not at hs
    obtain ⟨i,j,hij,a,hh⟩ := hs
    exact mem_iUnion.mpr ⟨(⟨(i,j),hij⟩,a),ht,hh⟩
  let C' := fun _ : Couples n × Axis => (16*σ)*(2*R)^(n*4-1)
  have hQ : volume A ≤ ENNReal.ofReal (∑ i,C' i) := by
    apply (measure_mono he).trans; apply (measure_iUnion_fintype_le _ W).trans
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by unfold C'; positivity)]
    exact Finset.sum_le_sum (fun i _ => stripe_cost i hr hs)
  refine (ENNReal.toReal_mono (by simp) hQ).trans_eq ?_
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => by unfold C'; positivity),cost_band, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by unfold C'; ring

private lemma indicator_cost {A : Set (Points n)} (h : MeasurableSet A) (P : ℝ) :
    (∫ x, A.indicator (fun _ : Points n => P) x)=volume.real A*P := by
  rw [integral_indicator h, setIntegral_const]; rfl

/-- Weak order zero. Outside the ties require `f` bound of **constant** cost
α, inside through all projection ties require M; smoothness ensures `applyTo`
is a true integral. -/
theorem spot_high (R : ℝ) (hr : 0 ≤ R) (f : Points n → ℂ) (t : Test n) (ht : tsupport t ⊆ Scaling.window R n)
    (α σ A M : ℝ) (hs : 0≤σ) (ha : 0≤α) (hA : 0≤A) (hM : 0≤M) (hu : ∀ x, ‖t x‖ ≤ M)
    (h : ∀ x ∈ Scaling.window R n, ‖f x‖ ≤ A)
    (he : ∀ x ∈ Scaling.window R n, x ∈ openFilm n (8*σ) → ‖f x‖ ≤ α)
    (_hs : ContinuousOn f (conf n)) : ‖t.applyTo f‖ ≤ M*(α*volume.real (Scaling.window R n)+A*(cost_band n R*σ)) := by
  classical
  let W := Scaling.window R n
  let B := W \ openFilm n (8*σ)
  let P := W.indicator fun _ => M*α; let Q := B.indicator fun _ => M*A
  have hp : MeasurableSet W := (window_closed ..).measurableSet
  have hh : volume W < ⊤ := (window_closed ..).measure_lt_top
  have hx : MeasurableSet B := hp.diff (open_film _).measurableSet
  have hb : volume B < ⊤ := (measure_mono (show B ⊆ W from sdiff_subset)).trans_lt hh
  have hP : Integrable P := (integrable_indicator_iff hp).2 (integrableOn_const hh.ne)
  have hQ : Integrable Q := (integrable_indicator_iff hx).2 (integrableOn_const hb.ne)
  unfold Test.applyTo
  refine (norm_integral_le_of_norm_le (hP.add hQ) ?_).trans ?_
  · filter_upwards with x
    change ‖t x*f x‖ ≤ P x+Q x
    by_cases hw : x∈W
    · by_cases hz : x∈B
      · have hh := mul_le_mul (hu x) (h x hw) (norm_nonneg _) hM
        unfold P Q; rw [indicator_of_mem hw,indicator_of_mem hz,norm_mul]; linarith [mul_nonneg hM ha]
      have hh := mul_le_mul (hu x) (he x hw (by_contra fun p => hz ⟨hw,p⟩)) (norm_nonneg _) hM
      unfold P Q; rwa [indicator_of_mem hw,indicator_of_notMem hz,add_zero,norm_mul]
    have hz : x ∉ tsupport t := fun hh => hw (ht hh)
    unfold P Q; rw [indicator_of_notMem hw, indicator_of_notMem (show x∉B from fun h => hw h.1), image_eq_zero_of_notMem_tsupport hz]
    simp
  simp only [Pi.add_apply]; rw [integral_add hP hQ, show ∫ x,P x = _ from indicator_cost hp _,show ∫ x,Q x = _ from indicator_cost hx _]
  have he := mul_le_mul_of_nonneg_right (band_cover (n:=n) R hr σ hs) (mul_nonneg hM hA)
  calc
    _ ≤ volume.real W * (M*α) + (cost_band n R*σ)*(M*A) := add_le_add_right he _
    _ = _ := by unfold W; ring
end stripes
end YM.Next.UVStress
