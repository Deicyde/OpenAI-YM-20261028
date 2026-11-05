import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.ROTATIONS.Response

/-! # Instead of the derivative on an orthant, a rescaled annular difference. -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table OS Row Word Nodes
open scoped Topology NNReal ENNReal BigOperators ContDiff
abbrev hiS : ℝ := 8
def liftSun (j : ℕ) := slash (2*j) sun
lemma base_sun : liftSun 0=sun := by ext1 x; simp [liftSun, slash_at sun_far]
lemma lift_far (j) : Far (liftSun j) := slash_far sun_far _
lemma lift_plus (j) : Plus (liftSun j) := by
  intro x; rw [liftSun,slash_at sun_far,pow_mul]; exact mul_nonneg (by positivity) (sun_plus _)
lemma lift_room (j) : Room (liftSun j) 2 := Room.split (fun _ => fun h => (sun_pos h).2) sun_far _
lemma lift_even (j) : Reflects false (liftSun j) := by
  intro x; simp only [liftSun,slash_at sun_far,inv_neg,pow_mul,neg_sq,sun_even x]; simp
lemma pumped (j) : pump 2 (liftSun (j+1))=liftSun j := by
  ext1 x; by_cases hx:x=0; · subst x; simp only [pump_at]; rw [(lift_far j).at_zero];simp
  simp only [pump_at,liftSun, slash_at sun_far]; rw [mul_add,pow_add,mul_one,inv_pow,inv_pow]; field_simp

def halve (w : ℝ) (q) := width w (liftSun q)
def debris (m : ℕ) (w : ℝ) (q : ℕ) := bake m hiS (halve w q)-bake m hiS (halve (2*w) q)
def gap (m : ℕ) (w : ℝ) (q : ℕ) := (halve w q - halve (2*w) q)-debris m w q
lemma gap_eq (m w q) : gap m w q=Resid m hiS (halve w q)-Resid m hiS (halve (2*w) q) := by
  unfold gap debris Resid; abel
lemma gap_moment (m w q) (_ : 0<w) : Centred (2*m) (gap m w q) := by
  rw [gap_eq]; intro i hi; rw [map_sub]; unfold Resid halve
  rw [correct m hiS (by unfold hiS;norm_num) _ ((lift_far q).1.width _) ((lift_even q).tall _) _ hi,
    correct m hiS (by unfold hiS;norm_num) _ ((lift_far q).1.width _) ((lift_even q).tall _) _ hi]; simp

def fee (m w q E) := Mlamp m hiS (halve w q) E-Mlamp m hiS (halve (2*w) q) E
lemma fee_at (m w q) (E : ℝ) (he : 0≤E) : Lap 1 (stamp (gap m w q)) E=↑(fee m w q E) := by
  rw [gap_eq,map_sub,Lap_sub 1 _ _ E he,even_cast _ _ _ E he,even_cast _ _ _ E he, fee, Complex.ofReal_sub]

private lemma kernel_down (m : ℕ) (p v s E : ℝ) (hs : 0<s) (hv : sun v≠0) (h : |2*p|≤s) :
    kernel m (s*v) (2*p) E≤kernel m (s*v) p E := by
  apply Finset.prod_le_prod (fun i _ => slot_nonneg _ _ _ _ _ hs hv h)
  intro i _
  apply div_le_div_of_nonneg_right _ (by positivity); nlinarith [sq_nonneg p]

private lemma fall (m w q v E) (hw : 0<w) (hW : w≤1) (he : 0<E) (hv : sun v ≠0) :
    positiveLap m hiS (halve (2*w) q) E v ≤ positiveLap m hiS (halve w q) E v := by
  unfold positiveLap halve
  rw [pat (2*w) (by positivity), pat w hw]
  have ht (t : ℝ) : Continuous (fun x : ℝ => raw E (t*x) * kernel m (hiS*v) (t*x) E) := (Continuous.mul (raw_c he) (slice_cont m hiS E v he)).comp (f:=fun x => t*x) (by fun_prop)
  apply integral_mono ((lift_far q).1.paid (ht _)) ((lift_far q).1.paid (ht _))
  intro p
  by_cases h : liftSun q p=0; · simp [h]
  have hl := lift_room q p h
  have hz : |2*(w*p)| ≤ hiS := by
    unfold hiS
    rw [abs_mul,abs_mul,abs_of_pos hw,abs_of_pos (by norm_num : (0:ℝ)<2)]; nlinarith [abs_nonneg p]
  dsimp only; rw [mul_assoc 2]
  refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (kernel_down m (w*p) v hiS E (by unfold hiS; norm_num) hv hz) (kernel_box m E _ _ _ (by unfold hiS; norm_num) hv hz).1 (raw_n ..)) (lift_plus q _)
  -- explicate
  unfold raw; apply inv_anti₀ (by positivity); nlinarith [sq_nonneg (w*p)]
lemma fee_pos (m w q E) (hw : 0<w) (hW : w ≤ 1) (he : 0≤E) : 0 ≤ fee m w q E := by
  unfold fee; rcases eq_or_lt_of_le he with h|he
  · subst E; rw [at_ground,at_ground,show halve w q 0=0 from ((lift_far q).width _).at_zero, show halve (2*w) q 0=0 from ((lift_far q).width _).at_zero]; simp
  rw [sub_nonneg,lamp_lit _ _ _ _ he,lamp_lit _ _ _ _ he]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hS : 0<hiS := by unfold hiS; norm_num
  unfold halve; rw [sunny _ _ hS _ ((lift_far q).1.width _) _ he,sunny _ _ hS _ ((lift_far q).1.width _) _ he];
  refine integral_mono (sunny_m _ ((lift_far q).1.width _) he) (sunny_m _ ((lift_far q).1.width _) he) ?_
  intro v; by_cases h : sun v=0; · simp [h]
  exact mul_le_mul_of_nonneg_left (fall m w q v E hw hW he h) (sun_plus _)

private lemma relief (w E p : ℝ) (hw : 0<w) (he : 0<E) (hp : sun p≠0) :
    1/400*w^2/(E+w)^4 ≤ raw E (w*p)-raw E (2*w*p) := by
  let x := (w*p)^2+E^2
  let y := (2*w*p)^2+E^2
  have hx : 0<x := by unfold x; positivity
  have hy : 0<y := by unfold y; positivity
  have ha : x*y≤400*(E+w)^4 := by
    obtain ⟨hs,ht⟩ := sun_pos hp
    have hv : p^2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg p]
    have hb : y ≤ 20*(E+w)^2 := by unfold y; rw [mul_pow (2*w) p]; nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg (2*w))]
    calc
      _ ≤ (20*(E+w)^2)*(20*(E+w)^2) := mul_le_mul ((by unfold x y; nlinarith [sq_nonneg (w*p)] : x≤y).trans hb) hb hy.le (by positivity)
      _ = _ := by ring
  change _ ≤ x⁻¹-y⁻¹
  rw [show x⁻¹-y⁻¹=(y-x)/(x*y) by field_simp]
  calc
    _ = w^2/(400*(E+w)^4) := by field_simp
    _ ≤ w^2/(x*y) := by gcongr
    _ ≤ _ := by
      gcongr
      dsimp only [y,x]; obtain ⟨hs,-⟩ := sun_pos hp
      have ht : 1≤p^2 := by rw [← sq_abs]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg w)]

private def Hlevel (m : ℕ) := (2:ℝ)⁻¹^m * ((2:ℝ)⁻¹)^(2*m)
private lemma sub_above (m w v E) (hw : 0<w) (hW : w≤1) (he : 0<E) (hh : E ≤ 1) (hv : sun v≠0) :
    1/400*w^2/(E+w)^4*Hlevel m ≤ positiveLap m hiS (halve w 0) E v - positiveLap m hiS (halve (2*w) 0) E v := by
  unfold positiveLap halve; rw [base_sun, pat (2*w) (by positivity), pat w hw]
  have ht (t : ℝ) : Continuous (fun x : ℝ => raw E (t*x) * kernel m (hiS*v) (t*x) E) := (Continuous.mul (raw_c he) (slice_cont m hiS E v he)).comp (f:=fun x => t*x) (by fun_prop)
  rw [← integral_sub (sun_far.1.paid (ht _)) (sun_far.1.paid (ht _))]
  let c := 1/400*w^2/(E+w)^4
  have hl : 0≤c := by unfold c; positivity
  calc
    _ = ∫ p,sun p*(c*Hlevel m) := by rw [integral_mul_const, show (∫ v,sun v)=1 by simpa [counts] using sun_mass,one_mul]
    _ ≤ _ := by
      refine integral_mono (sun.integrable.mul_const _) ((sun_far.1.paid (ht _)).sub (sun_far.1.paid (ht _))) ?_
      intro p
      dsimp only
      by_cases hp : sun p=0; · simp [hp]
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ (sun_plus _)
      have hS : 0<hiS := by unfold hiS; norm_num
      have hz : |2*w*p|≤hiS := by
        have hh := (sun_pos hp).2
        unfold hiS; rw [abs_mul,abs_of_pos (by positivity : 0<2*w)]; nlinarith [abs_nonneg p]
      let A := kernel m (hiS*v) (2*w*p) E
      have ha : Hlevel m≤A := by
        apply le_trans _ (kernel_floor m E _ _ _ (by unfold hiS; norm_num) hv hz he); unfold Hlevel; gcongr; linarith
      have hy : 0≤A := ha.trans' (by unfold Hlevel; positivity)
      have hx : A ≤ kernel m (hiS*v) (w*p) E := by
        rw [mul_assoc 2] at hz; unfold A; rw [mul_assoc 2]; exact kernel_down m (w*p) v hiS E hS hv hz
      refine le_trans (b:=c*A) (mul_le_mul_of_nonneg_left ha hl) ?_
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_right (relief w E p hw he hp) hy
        _ ≤ _ := by rw [sub_mul]; exact sub_le_sub_right (mul_le_mul_of_nonneg_left hx (raw_n ..)) _

lemma grant (m : ℕ) : ∃ C : ℝ,0<C ∧ ∀ E w : ℝ, 0<w → w≤1 → 0≤E → E≤1 →
    C*E*w^2/(E+w)^4 ≤ fee m w 0 E := by
  let C := Hlevel m
  have hC : 0<C := by unfold C Hlevel; positivity
  refine ⟨1/400*C*2,by positivity,fun E w hw hW he h => ?_⟩
  rcases eq_or_lt_of_le he with rfl|he
  · simpa using fee_pos m w 0 0 hw hW le_rfl
  unfold fee
  rw [lamp_lit _ _ _ _ he,lamp_lit _ _ _ _ he,← mul_sub]
  have hS : 0<hiS := by unfold hiS; positivity
  let X := positiveLap m hiS (halve w 0) E; let Y := positiveLap m hiS (halve (2*w) 0) E
  rw [sunny _ _ hS (halve w 0) (show Ends (halve w 0) from (lift_far 0).1.width w) E he,sunny _ _ hS _ (show Ends (halve (2*w) 0) from (lift_far 0).1.width _) E he]
  change _ ≤ 2*E*((∫ x,sun x*X x) - ∫ x,sun x*Y x)
  rw [← integral_sub (sunny_m (halve w 0) _ he) (sunny_m (halve (2*w) 0) _ he)]
  rotate_left
  · exact (lift_far 0).1.width _
  · exact (lift_far 0).1.width _
  let c := 1/400*w^2/(E+w)^4*C
  calc
    _ = 2*E * ∫ y,sun y*c := by rw [integral_mul_const,show (∫ v,sun v)=1 by simpa [counts] using sun_mass,one_mul]; dsimp only [c]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine integral_mono (sun.integrable.mul_const _) ((sunny_m (halve w 0) ?_ he).sub (sunny_m (halve (2*w) 0) ?_ he)) ?_
      · exact (lift_far 0).1.width _
      · exact (lift_far 0).1.width _
      · intro v; change sun v*c≤sun v*X v - sun v*Y v
        by_cases hv : sun v=0; · simp [hv]
        rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (sub_above m w v E hw hW he h hv) (sun_plus _)

lemma lamp_tally {f : Profile} (E : ℝ) (hf : Ends f) (ht : tally 0 f=0) (hh : 0≤E) :
    Lap 1 (stamp (pump 2 f)) E=(-(E:ℂ)^2)*Lap 1 (stamp f) E := by
  rcases eq_or_lt_of_le hh with rfl|he
  · simp_rw [zeroLap,pump_at]; simp
  -- p²/(E²+p²)= 1 - E²/(E²+p²)
  let g (p : ℝ) := 2*E/(E^2+p^2)
  have hg : Continuous g := by unfold g; fun_prop (disch:=(intro;positivity))
  have heq : (∫ p,pump 2 f p*g p)= -(E^2*∫ p,f p*g p) := by
    have hz p : pump 2 f p*g p= (2*E*f p)-E^2*(f p*g p) := by rw [pump_at]; unfold g; field_simp; ring
    simp_rw [hz]; rw [integral_sub (f.integrable.const_mul _) ((hf.paid hg).const_mul _),integral_const_mul, integral_const_mul]
    rw [show (∫ p,f p)=0 from by simpa only [counts,pow_zero,one_mul] using ht,mul_zero,zero_sub]
  simp_rw [evenLap _ _ he]
  change Complex.ofReal (∫ p : ℝ,pump 2 f p*g p)= _
  rw [heq]; simp [g]
lemma gap_far (m w q) : Far (gap m w q) := by
  unfold gap debris
  have he (f g : Profile) (h : Far f) (l : Far g) : Far (f-g) := by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact h.add (l.scale _)
  have hf w : Far (halve w q) := (lift_far q).width w
  exact he _ _ (he _ _ (hf _) (hf _)) (he _ _ (bake_far ..) (bake_far ..))
lemma lamp_more {f : Profile} (E : ℝ) (k : ℕ) (hh : 0≤E) (hf : Ends f) (h : Centred (2*k) f) :
    Lap 1 (stamp (pump (2*k) f)) E= (-(E:ℂ)^2)^k*Lap 1 (stamp f) E := by
  induction k with
  | zero => rw [show pump (2*0) f=f by ext; simp [pump_at]]; simp
  | succ k ih =>
    have hp : Centred (2*k) f := fun j hj => h j (by omega)
    have hu : tally 0 (pump (2*k) f)=0 := by
      have he := h (2*k) (by omega); simpa [counts,pump_at] using he
    rw [show 2*(k+1)=2+ (2*k) by omega,← pump_pump, lamp_tally E (hf.pumps _) hu hh, ih hp,pow_succ']; ring
end YM.Outer
