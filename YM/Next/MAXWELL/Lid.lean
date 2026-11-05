import YM.Next.MAXWELL.Box

/-! # Escape estimates for the free energy argument -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Box Set Function Filter Tensor Analysis MeasureTheory WithLp
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {F M : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup M]
variable {G : Gauge} {j l : ℕ}

/-- E4 escape tail. -/
def Escape (r : ℕ) (f : E4 → M) := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop,
    ∀ z : E4, R ≤ ‖z‖ → ‖f z‖ ≤ C * R⁻¹^r

lemma escape_add {f g : E4 → M} {r : ℕ} (H : Escape r f) (K : Escape r g) : Escape r (f+g) := by
  obtain ⟨C,hc,hf⟩ := H; obtain ⟨D,hd,hg⟩ := K
  refine ⟨C+D,add_nonneg hc hd,?_⟩
  filter_upwards [hf,hg] with R hp hq
  intro x hx
  rw [add_mul]; exact (norm_add_le _ _).trans (add_le_add (hp _ hx) (hq _ hx))

lemma escape_zero (r : ℕ) : Escape r (0 : E4 → M) := ⟨0,le_rfl,Eventually.of_forall (by simp)⟩

lemma escape_scale {f : E4 → F} {r : ℕ} (H : Escape r f) (t : ℝ) : Escape r (t • f) := by
  obtain ⟨C,hc,hf⟩ := H; refine ⟨‖t‖*C,by positivity,?_⟩
  filter_upwards [hf] with R hp x hx
  rw [mul_assoc]; change ‖t • f x‖ ≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hp _ hx) (norm_nonneg _)

lemma escape_sum {ι : Type*} {r : ℕ} (s : Finset ι) (f : ι → E4 → M) (H : ∀ i ∈ s, Escape r (f i)) :
    Escape r (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! (escape_zero (M := M) r)
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact escape_add (H i (by simp)) (ih fun i h => H i (Finset.mem_insert_of_mem h))

lemma escape_pulse (p : Probe G j) (x : E4) (a b : Axis) : Escape 4 (pulse p x a b) := by
  have he (c : G.ColorIndex) : Escape 4 (fun z : E4 => pulse p x a b z c) := by
    obtain ⟨C,hc,H⟩ := (kernel_pole p (omegaLeg c a b)).bounds
    refine ⟨C * 2^4,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (2*‖x‖+2)] with R hR z hz
    have hr : 0 < R := by have := norm_nonneg x; linarith
    have hn : ‖x-z‖ ≥ R/2 := by
      rw [norm_sub_rev]; have ht := norm_sub_norm_le z x; linarith
    have ht : 1 ≤ ‖x-z‖ := by have := norm_nonneg x; linarith
    have hu : x ≠ z := by rintro rfl; rw [sub_self,norm_zero] at ht; norm_num at ht
    change ‖pulse p x a b z c‖ ≤ _
    rw [← K_observe p c a b hu]
    calc
      _ ≤ C * ‖x-z‖⁻¹^(4+j+0) := H _ (sub_ne_zero.mpr hu)
      _ ≤ C * ‖x-z‖⁻¹^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by positivity) (by calc
          _ ≤ (1:ℝ)⁻¹ := by gcongr
          _ = 1 := inv_one) (by omega)) hc
      _ ≤ C * (R/2)⁻¹^4 := by gcongr
      _ = _ := by ring
  have hu : pulse p x a b = fun y => ∑ c : G.ColorIndex, (pulse p x a b y c) • unitColor G c := by
    ext1 y; ext1 d; simp [unitPaint]
  rw [hu]
  apply escape_sum
  intro c _
  obtain ⟨C,hc,H⟩ := he c
  refine ⟨C,hc,?_⟩
  filter_upwards [H] with R h y hy; simpa only [norm_smul,unitColor, EuclideanSpace.single, PiLp.norm_single,norm_one,mul_one] using h y hy

lemma escape_cross {f g : Field F} (hf : ∀ a b, Escape 4 (f a b)) (hg : ∀ a b, Escape 4 (g a b)) (a b : Axis) :
    Escape 8 (cross f g a b) := by
  have he (i l a b : Axis) : Escape 8 (fun x : E4 => ⟪f i l x,g a b x⟫_ℝ) := by
    obtain ⟨C,hc,h⟩ := hf i l; obtain ⟨D,hd,H⟩ := hg a b
    refine ⟨C*D,by positivity,?_⟩
    filter_upwards [h,H] with R hr hs z hz
    refine (norm_inner_le_norm _ _).trans ?_
    calc
      _ ≤ (C*R⁻¹^4) * (D*R⁻¹^4) := by gcongr; exacts [hr z hz,hs z hz]
      _ = _ := by ring
  let A : E4 → ℝ := fun x => ∑ i : Axis, ∑ l : Axis, ⟪f i l x,g i l x⟫_ℝ
  let B : E4 → ℝ := fun x => ∑ c : Axis, (⟪f a c x,g b c x⟫_ℝ + ⟪f b c x,g a c x⟫_ℝ)
  have hw : cross f g a b = B + ((-(kr a b*(1/2))) • A) := by
    ext1 x; simp only [cross,A,B, Pi.add_apply,Pi.smul_apply, smul_eq_mul,neg_mul, sub_eq_add_neg]
  rw [hw]; apply escape_add
  · exact escape_sum _ _ fun i _ => escape_add (he a i b i) (he b i a i)
  exact escape_scale (escape_sum _ _ fun i _ => escape_sum _ _ fun j _ => he i j i j) _

namespace Box

def lid (R : ℝ) : Plain := fun _ => R

def base (a : Axis) (R : ℝ) : Plain := fun i => if a=i then 0 else -R

lemma sits (a : Axis) {R : ℝ} (h : 0 ≤ R) : base a R ≤ lid R := by
  intro i; unfold base lid; split_ifs <;> linarith

lemma eventually_inside {x : E4} {a : Axis} (hx : 0 < x a) :
    ∀ᶠ R : ℝ in atTop, x ∈ strictly (base a R) (lid R) := by
  filter_upwards [eventually_gt_atTop ‖x‖] with R hR
  intro i _
  have h : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  obtain ⟨h,h'⟩ := abs_lt.mp (lt_of_le_of_lt h hR)
  change (x i : ℝ) ∈ Ioo (if a=i then 0 else -R) R
  exact ⟨by split_ifs with H; exact H ▸ hx; exact h,h'⟩

lemma never_inside {x : E4} {a : Axis} (hx : x a < 0) (R : ℝ) : x ∉ enclosedBy (base a R) (lid R) := fun hi => by
  have ht : base a R a ≤ x a := hi.1 a
  simp [base] at ht; linarith

lemma face_area {R : ℝ} (hr : 0 ≤ R) (b a : Axis) :
    volume.real (face (base a R) (lid R) b) ≤ (2*R)^3 := by
  have ht := sits a hr
  unfold face Measure.real
  rw [Real.volume_Icc_pi_toReal (show base a R ∘ b.succAbove ≤ lid R ∘ b.succAbove from fun i => ht _)]
  calc
    _ ≤ ∏ i : SpaceAxis, (fun _ : SpaceAxis => 2*R) i := Finset.prod_le_prod
      (fun i _ => sub_nonneg.mpr (ht _)) (fun i _ => by unfold base lid; split_ifs <;> linarith)
    _ = _ := by simp

lemma disappearance {a b : Axis} {J : Axis → E4 → ℝ} (t : ℝ → ℝ)
    (H : Escape 8 (J b)) (he : ∀ᶠ R : ℝ in atTop, R ≤ |t R|) :
    Tendsto (fun R : ℝ => side (base a R) (lid R) J b (t R)) atTop (𝓝 0) := by
  obtain ⟨C,hc,h⟩ := H
  have ht : Tendsto (fun R : ℝ => (C*8)* R⁻¹^5) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero (𝕜:=ℝ)).pow 5).const_mul (C*8)
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [h,he,eventually_gt_atTop (0:ℝ)] with R H hh hr
  let B := face (base a R) (lid R) b
  change ‖∫ z : Section3 in B, J b (inFace b (t R) z)‖ ≤ _
  calc
    _ ≤ (C * R⁻¹^8) * volume.real B := norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top (fun z _ => H _
      (by simpa using hh.trans (show |t R| ≤ ‖inFace b (t R) z‖ from by
        simpa only [Real.norm_eq_abs,inFace_at] using PiLp.norm_apply_le (inFace b (t R) z) b)))
    _ ≤ (C * R⁻¹^8) * (2*R)^3 := by gcongr; exact face_area hr.le b a
    _ = _ := by field_simp; ring

/-- Only the outward bottom flux survives. This tends to a real number;
for now use expanding boxes rather than full plane integral. -/
def bottom (R : ℝ) (a : Axis) (J : Axis → E4 → ℝ) := - side (base a R) (lid R) J a 0

lemma surviving (a : Axis) (J : Axis → E4 → ℝ) (h : ∀ b, Escape 8 (J b)) :
    Tendsto (fun R => perimeter (base a R) (lid R) J - bottom R a J) atTop (𝓝 0) := by
  let F (b : Axis) (R : ℝ) := side (base a R) (lid R) J b R - if b=a then 0 else
    side (base a R) (lid R) J b (-R)
  have hf (b : Axis) : Tendsto (F b) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun R => side (base a R) (lid R) J b R) atTop (𝓝 0) :=
      disappearance _ (h b) (Eventually.of_forall fun R => le_abs_self _)
    have h₂ : Tendsto (fun R => side (base a R) (lid R) J b (-R)) atTop (𝓝 0) :=
      disappearance _ (h b) (Eventually.of_forall fun R => by simpa using le_abs_self R)
    by_cases hb : b=a
    · simpa [F,hb] using h₁
    simpa [F,hb] using h₁.sub h₂
  have he (R) : perimeter (base a R) (lid R) J - bottom R a J = ∑ b, F b R := by
    unfold perimeter bottom F
    let B := fun b t => side (base a R) (lid R) J b t
    have he (b : Axis) : side (base a R) (lid R) J b (base a R b) =
        (if b=a then B a 0 else 0) + if b=a then 0 else B b (-R) := by
      change B b _ = _
      split_ifs with ht
      · subst b; simp [base]
      rw [zero_add]; simp [base,Ne.symm ht]
    simp_rw [Finset.sum_sub_distrib,he,Finset.sum_add_distrib]
    simp only [lid, Finset.sum_ite_eq', Finset.mem_univ,↓reduceIte]; unfold B; abel
  simp_rw [he]
  simpa using tendsto_finsetSum (f := F) Finset.univ (fun i _ => hf i)

lemma readout (a : Axis) {x : E4} (hx : 0 < x a) {y : E4} (hy : y a < 0) (p : Probe G j) (q : Probe G l) :
    Tendsto (fun R => bottom R a (fun i z => cross (pulse p x) (pulse q y) i a z)) atTop
      (𝓝 (- K (raiseLeg (basis a) p) q x y)) := by
  let J (i : Axis) (z : E4) := cross (pulse p x) (pulse q y) i a z
  have hv : Tendsto (fun R => perimeter (base a R) (lid R) J) atTop (𝓝 (-K (raiseLeg (basis a) p) q x y)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_inside hx,eventually_ge_atTop (0:ℝ)] with R hR hr
      exact (energy_through (a:=a) (sits a hr) hR (never_inside hy R) p q).symm)
  simpa only [sub_sub_cancel,sub_zero] using hv.sub (surviving a J fun i => escape_cross (fun i l => escape_pulse p x i l) (fun i l => escape_pulse q y i l) i a)
end Box
end YM.Maxwell.Free
