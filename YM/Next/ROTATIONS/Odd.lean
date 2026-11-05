import YM.Next.ROTATIONS.Energy
/-! # Odd subtracted response (also on profiles whose support touches zero) -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Nodes Boundary Probe Metric
open scoped Topology NNReal ENNReal BigOperators ContDiff

def OddB (m : ℕ) (s : ℝ) (f : Profile) := slash 1 (bake m s (pump 1 f))
def Tail (m : ℕ) (s : ℝ) (f : Profile) := f-OddB m s f
lemma OddB.far (m s f) : Far (OddB m s f) := slash_far (bake_far ..) _
lemma OddB.parity (m s f) : Reflects true (OddB m s f) := by
  intro p
  unfold OddB; rw [slash_at (bake_far m s _),bake_even m s _ p]; simp [slash_at (bake_far m s _)]
lemma pump_back (k : ℕ) (f : Profile) (h : Far f) : pump k (slash k f) = f := by
  ext x; rw [pump_at,slash_at h]
  by_cases hx : x=0; · subst x; simp [h.at_zero]
  rw [inv_pow]; field_simp
lemma Tail.correct (m : ℕ) (s) (hs : 0<s) (f : Profile) (hf : Ends f) (he : Reflects true f) :
    Centred (2*m) (Tail m s f) := by
  have hv : pump 1 (Tail m s f)=Resid m s (pump 1 f) := by
    unfold Tail; rw [map_sub, OddB,pump_back 1 _ (bake_far ..)]; rfl
  have hh : Reflects false (pump 1 f) := fun x => by
    rw [pump_at,he x]; simp [pump_at]
  intro j hj
  rcases Nat.even_or_odd j with H|H
  · unfold Tail; rw [map_sub, tally_odd true _ he _ (by simpa),tally_odd true _ (OddB.parity m s f) _ (by simpa),sub_self]
  obtain ⟨k,hk⟩ := H
  rw [show tally j (Tail m s f) = tally (2*k) (Resid m s (pump 1 f)) from ?_]
  · exact _root_.YM.Outer.correct m s hs _ (hf.pumps _) hh (2*k) (by omega)
  rw [← hv,hk]; unfold tally; simp only [ContinuousLinearMap.comp_apply,pump_pump]
lemma odd_rep (m s f E) (hE : 0<E) : Lap (-1) (stamp (Tail m s f)) E =
    (-2*I)*↑(directLap E (Resid m s (pump 1 f))) := by
  rw [oddLap (Tail m s f) E hE]
  congr 2; unfold directLap; congr 1; ext x
  simp only [Tail,Resid,_root_.sub_apply,pump_at,pow_one]
  have hv := congr_arg (fun g : Profile => g x) (pump_back 1 _ (bake_far m s (pump 1 f)))
  change pump 1 (OddB m s f) x= _ at hv
  rw [pump_at,pow_one] at hv
  unfold raw; rw [← hv]; rw [div_eq_mul_inv,add_comm (_^_)]; ring

private lemma gradient (f : Profile) (he : Reflects true f) : ∃ C : ℝ,0≤C ∧ ∀ p, ‖f p‖ ≤ C*|p| := by
  let C := SchwartzMap.seminorm ℝ 0 1 f
  refine ⟨C,apply_nonneg _ _,fun p => ?_⟩
  have hp : ∀ x, ‖fderiv ℝ f x‖ ≤ C := by
    intro x; rw [← norm_iteratedFDeriv_one]
    exact f.norm_iteratedFDeriv_le_seminorm _ _ _
  have ht := Convex.norm_image_sub_le_of_norm_fderiv_le (C:=C) (x:=0) (y:=p) (f:=f) (𝕜:=ℝ)
    (fun x _ => f.differentiableAt) (fun x _ => hp x) convex_univ (mem_univ _) (mem_univ _)
  have hh := he 0; simp only [neg_zero, ↓reduceIte] at hh
  simp_rw [show f 0=0 by linarith,sub_zero,Real.norm_eq_abs] at ht; exact ht

private lemma priced (m : ℕ) (s : ℝ) (hs : 0<s) : ∃ C : ℝ,0≤C ∧ ∀ (p E v : ℝ), sun v≠0 → |p| ≤ s → 0<E →
    kernel m (s*v) p E ≤ C*(1+E)⁻¹^(2*m) := by
  let P := kernelPrice m
  have hP : 0<P := kernel_price_pos m
  let k := 2*m
  let R := max ((2:ℝ)^k) (P*((2*s)^k))
  refine ⟨R,(show 0 ≤ (2:ℝ)^k by positivity).trans (le_max_left ..),fun p E v hv hp he => ?_⟩
  have hh : 0<1+E := by linarith
  rcases le_or_gt E 1 with ht|ht
  · apply (kernel_box _ _ _ _ _ hs hv hp).2.trans
    apply le_trans (b:=2^(2*m)*(1+E)⁻¹^(2*m)) ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
    rw [← mul_pow]; apply one_le_pow₀; rw [← div_eq_mul_inv,one_le_div hh]; linarith
  apply (kernel_ceiling _ _ _ _ _ hs hv hp he).trans
  have hy : s/E ≤ 2*s*(1+E)⁻¹ := by rw [← div_eq_mul_inv,div_le_div_iff₀ he hh]; nlinarith
  calc
    _ ≤ P*(2*s*(1+E)⁻¹)^(2*m) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy _) hP.le
    _ = P*(2*s)^k*(1+E)⁻¹^k := by unfold k; rw [mul_pow (2*s),mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)

private lemma parcel (m : ℕ) (s : ℝ) (hs : 1≤s) (f : Profile) (ht : Reflects true f) (R : ℝ)
    (hr : 1≤R) (hT : Room f R) : ∃ C : ℝ,0≤C ∧ ∀ (w E v : ℝ), 0<w → R*w≤s → 0<E → sun v≠0 →
    ‖positiveLap m s (pump 1 (width w f)) E v‖ ≤ C*(E+w)⁻¹*(1+E)⁻¹^(2*m) := by
  have hS : 0<s := by linarith
  have hr' : 0<R := by linarith
  obtain ⟨P,hP,h⟩ := priced m s hS
  obtain ⟨L,hL,hG⟩ := gradient f ht
  let c := 2*L*R^2
  have hc : 0≤c := by unfold c; positivity
  refine ⟨2*R*c*P,by positivity,fun w E v hw hb he hv => ?_⟩
  let g := pump 1 (width w f)
  let T := R*w
  have hx : Room (width w f) T := by dsimp only [T]; rw [mul_comm]; exact hT.grow _ hw
  have Ht : Room g T := hx.pumps _
  let k := 2*m
  let z := c / (w*(E+w)) * (P*((1+E)⁻¹)^k)
  let D := Icc (-T) T
  let H (p : ℝ) := g p*(raw E p * kernel m (s*v) p E)
  have ha (p : ℝ) (hp : g p≠0) : ‖H p‖ ≤ z := by
    have Hz : ‖g p‖ ≤ L/w^2*p^2 := by
      unfold g; rw [pump_at,pow_one,norm_mul,width_at,norm_mul, Real.norm_of_nonneg (inv_pos.mpr hw).le]
      apply le_trans (b:=‖p‖*(w⁻¹*(L*|p/w|))) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hG _) (inv_nonneg.mpr hw.le)) (norm_nonneg _))
      refine le_of_eq ?_
      rw [abs_div,abs_of_pos hw,Real.norm_eq_abs]
      field_simp; nlinarith [sq_abs p]
    have hQ : |p|≤s := (Ht p hp).trans hb
    obtain ⟨ho,hc⟩ := kernel_box m E p v s hS hv hQ
    have hy := h p E v hv hQ he
    unfold H; rw [← mul_assoc,norm_mul,Real.norm_of_nonneg ho,norm_mul, Real.norm_of_nonneg (raw_n ..)]
    have Hr : ‖g p‖*raw E p ≤ c/(w*(E+w)) := by
      apply (mul_le_mul_of_nonneg_right Hz (raw_n ..)).trans
      have hd : 0 < p^2+E^2 := by positivity
      have hw' : 0<w*(E+w) := by positivity
      unfold c raw
      rcases le_total E w with hj|hj
      · calc
          _ ≤ L/w^2 := by
            rw [mul_assoc,← div_eq_mul_inv (p^2)]
            refine mul_le_of_le_one_right (by positivity) ((div_le_one hd).mpr ?_)
            linarith [sq_nonneg E]
          _ ≤ 2*L/(w*(E+w)) := by
            rw [div_le_div_iff₀ (pow_pos hw _) hw']; nlinarith [mul_nonneg hL (sub_nonneg.mpr hj),mul_pos hw he]
          _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)) hw'.le
      · have hB : |p| ≤ R*w := Ht _ hp
        have HH : p^2≤R^2*w^2 := by rw [← sq_abs,← mul_pow]; gcongr
        have ht : L/w^2*p^2≤L*R^2 := (mul_le_mul_of_nonneg_left HH (show 0≤L/w^2 by positivity)).trans_eq (by field_simp)
        calc
          _ ≤ L*R^2*(E^2)⁻¹ := mul_le_mul ht (inv_anti₀ (pow_pos he _) (by linarith [sq_nonneg p])) (by positivity) (by positivity)
          _ ≤ _ := by
            rw [← div_eq_mul_inv,div_le_div_iff₀ (pow_pos he _) hw']
            calc L*R^2*(w*(E+w)) ≤ L*R^2*(E*(E+E)) := by gcongr
                 _ = _ := by ring
    refine mul_le_mul Hr hy ho (Hr.trans' (mul_nonneg (norm_nonneg _) (raw_n ..)))
  calc
    _ ≤ ∫ p : ℝ,D.indicator (fun _ => z) p := by
      apply norm_integral_le_of_norm_le ((integrableOn_const (by exact isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc)
      filter_upwards with p
      change ‖H p‖ ≤ _
      by_cases hz : g p=0
      · simp only [H,hz,zero_mul,norm_zero]; apply indicator_nonneg
        intro _ _; dsimp only [z]; positivity
      rw [indicator_of_mem (show p∈D from abs_le.mp (Ht p hz))]; exact ha _ hz
    _ = _ := by
      rw [integral_indicator (f:=fun _ => z) measurableSet_Icc,setIntegral_const]
      have hy : 0<T := mul_pos hr' hw
      rw [show volume.real D = _ from Real.volume_real_Icc_of_le (show -T≤T by linarith), smul_eq_mul]
      unfold z T k; field_simp; ring

lemma versus (m : ℕ) (s : ℝ) (hs : 1≤s) (f : Profile) (hf : Ends f) (ht : Reflects true f) (R : ℝ)
    (hr : 1≤R) (hT : Room f R) : ∃ C : ℝ,0≤C ∧ ∀ (w E : ℝ), 0<w → R*w≤s → Room (width w center) s → 0≤E →
    ‖Lap (-1) (stamp (Tail m s (width w f))) E‖ ≤ C*Mlamp m s (width w center) E := by
  obtain ⟨C,hC,H⟩ := parcel m s hs f ht R hr hT
  let a := (2:ℝ)⁻¹^m
  have ha : 0<a := pow_pos (by norm_num) _
  refine ⟨(2/a)*C,by positivity,fun w e hw hp hg he => ?_⟩
  have hi E (hE : 0<E) : ‖Lap (-1) (stamp (Tail m s (width w f))) E‖ ≤ 2/a*C*Mlamp m s (width w center) E := by
    let F := pump 1 (width w f)
    have hv := (Ends.width hf w).pumps 1
    have heq : ‖directLap E (Resid m s F)‖ ≤ C*(E+w)⁻¹*(1+E)⁻¹^(2*m) := by
      rw [sunny m s (by linarith) F hv E hE]
      calc
        _ ≤ ∫ v,sun v * (C*(E+w)⁻¹*(1+E)⁻¹^(2*m)) := by
          refine norm_integral_le_of_norm_le (sun.integrable.mul_const _) (ae_of_all _ fun v => ?_)
          rw [norm_mul, Real.norm_of_nonneg (sun_plus _)]
          by_cases h : sun v=0; · simp [h]
          exact mul_le_mul_of_nonneg_left (H w E v hw hp hE h) (sun_plus v)
        _ = _ := by rw [integral_mul_const, show (∫ v,sun v)=1 by simpa [counts] using sun_mass,one_mul]
    have hb : a*(E+w)⁻¹*(1+E)⁻¹^(2*m) ≤ Mlamp m s (width w center) E := lower m s w E hs hw hg hE.le
    rw [odd_rep _ _ _ E hE]
    simp only [norm_mul,norm_neg,norm_I, Complex.norm_real,mul_one]; norm_num only [Complex.norm_ofNat]
    apply (mul_le_mul_of_nonneg_left heq ?_).trans
    swap; · norm_num
    calc _ = 2/a*C*(a*(E+w)⁻¹*(1+E)⁻¹^(2*m)) := by norm_num; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  rcases eq_or_lt_of_le he with rfl|he
  · have H₁ := Lap_cont (-1) (by simp) (stamp (Tail m s (width w f))) |>.norm
    have H₂ := Mlamp_cont m s (width w center) |>.const_mul (2/a*C)
    apply le_of_tendsto_of_tendsto (to_zero _ (H₁ _ self_mem_Ici)) (to_zero _ (H₂ _ self_mem_Ici))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hi _ hx
  exact hi e he
end YM.Outer
