import YM.Next.ROTATIONS.Lap
import YM.Next.ROTATIONS.Subtract
/-! # Sign-controlled kernel identity including node factors. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Nodes
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff

def Resid (m : ℕ) (s : ℝ) (f : Profile) := f-bake m s f



def raw (E p : ℝ) := (p^2+E^2)⁻¹
def directLap (E : ℝ) (f : Profile) := ∫ p, f p * raw E p
def positiveLap (m : ℕ) (s : ℝ) (f : Profile) (E v : ℝ) := ∫ p,f p*(raw E p * kernel m (s*v) p E)
lemma raw_n (p E : ℝ) : 0≤raw E p := inv_nonneg.mpr (by positivity)
lemma raw_c {E} (h : 0<E) : Continuous (raw E) := by unfold raw; fun_prop (disch:= (intro;positivity))
lemma nod_cont (m : ℕ) (s : ℝ) (E : ℝ) (h : 0<E) : Continuous fun z : ℝ × ℝ => kernel m (s*z.1) z.2 E := by
  unfold kernel; fun_prop (disch:= (intro;positivity))
lemma slice_cont (m s E v) (h : 0<E) : Continuous fun p : ℝ => kernel m (s*v) p E :=
  (nod_cont m s E h).comp (f:=fun p : ℝ => (v,p)) (by fun_prop)

lemma sunny_m {m : ℕ} {s E : ℝ} (f : Profile) (hf : Ends f) (hE : 0<E) : Integrable
    (fun v => sun v*positiveLap m s f E v) (volume : Measure ℝ) := by
  simp only [positiveLap,← integral_const_mul]
  refine Integrable.integral_prod_left (f:=fun z : ℝ × ℝ => sun z.1 * (f z.2*(raw E z.2 * kernel m (s*z.1) z.2 E))) ?_
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (sun.continuous.comp continuous_fst).mul ((f.continuous.comp continuous_snd).mul (((raw_c hE).comp continuous_snd).mul (nod_cont m s E hE)))
  · apply HasCompactSupport.intro (IsCompact.prod (s:=tsupport sun) (t:=tsupport f) sun_far.1 hf)
    intro p hp; rw [mem_prod] at hp
    by_cases hv : p.1∈ tsupport sun
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hv,h⟩)]
    simp [image_eq_zero_of_notMem_tsupport hv]

lemma sunny (m : ℕ) (s : ℝ) (hs : 0<s) (f : Profile) (hf : Ends f) (E : ℝ) (hE : 0<E) :
    directLap E (Resid m s f)=∫ v,sun v*positiveLap m s f E v := by
  have he := bake_test m s hs f hf _ (raw_c hE)
  let c := ∫ p,f p*raw E p
  have hh : (∫ p,bake m s f p*raw E p)= ∫ v,(sun v*c - sun v*positiveLap m s f E v) := by
    rw [he]; congr 1; funext v
    by_cases H : sun v=0
    · simp [H]
    rw [← mul_sub]; congr 1
    have hi := fun p : ℝ => scaled_interp m p E (s*v) hE (mul_ne_zero hs.ne' (fun h => H (h ▸ sun_far.at_zero)))
    let g (p : ℝ) := raw E p * kernel m (s*v) p E
    unfold c positiveLap
    rw [← integral_sub (hf.paid (raw_c hE)) (hf.paid (g:=g) ((raw_c hE).mul (slice_cont _ _ _ _ hE)))]
    congr 1; funext p; unfold g raw; rw [← hi]; ring
  rw [integral_sub (sun.integrable.mul_const _) (sunny_m f hf hE),integral_mul_const,
    show (∫ y,sun y)=1 by simpa [counts] using sun_mass,one_mul] at hh
  unfold directLap Resid
  simp_rw [_root_.sub_apply,sub_mul]; rw [integral_sub (hf.paid (raw_c hE)) ((bake_far m s f).1.paid (raw_c hE)),hh]; exact sub_sub_cancel _ _

/-- Real part keeps normalization harmless. Actual imaginary part zero. -/
def Mlamp (m : ℕ) (s : ℝ) (f : Profile) (E : ℝ) := (Lap 1 (stamp (Resid m s f)) E).re
lemma even_cast (m s f E) (he : 0≤E) : Lap 1 (stamp (Resid m s f)) E=(Mlamp m s f E:ℂ) := by
  unfold Mlamp; rcases eq_or_lt_of_le he with h|h; · subst E; rw [zeroLap]; rfl
  rw [evenLap _ _ h]; rfl
lemma at_ground (m s f) : Mlamp m s f 0=pref ℝ * f 0 := by
  unfold Mlamp; rw [zeroLap]; change _*(Resid m s f) 0=_; unfold Resid; simp [(bake_far m s f).at_zero]
lemma lamp_lit (m s f E) (hE : 0<E) : Mlamp m s f E=2*E*directLap E (Resid m s f) := by
  rw [Mlamp,evenLap _ _ hE,ofReal_re,directLap,← integral_const_mul]; congr 1; funext p
  unfold raw; rw [add_comm (E^2),div_eq_mul_inv]; ring

/-- Respective moment interpolation required on the true panel. -/
def Room (f : Profile) (s : ℝ) := ∀ p : ℝ, f p ≠ 0 → |p| ≤ s
lemma Ends.room {f : Profile} (h : Ends f) : ∃ s : ℝ, Room f s := by
  have he : IsCompact (tsupport f) := h
  obtain ⟨R,hR⟩ := he.isBounded.subset_closedBall 0
  exact ⟨R,fun p hp => by simpa using hR (subset_tsupport _ hp)⟩
lemma Room.inc {f : Profile} {s t} (h : Room f s) (hs : s ≤ t) : Room f t := fun p hp => (h p hp).trans hs
lemma Room.grow {f s} (h : Room f s) (w : ℝ) (hw : 0<w) : Room (width w f) (w*s) := by
  intro p hp
  have he : f (p/w) ≠ 0 := by intro hz; apply hp; rw [width_at,hz,mul_zero]
  rw [mul_comm w]; apply (div_le_iff₀ hw).mp; simpa [abs_div,abs_of_pos hw] using h _ he
lemma Room.pumps {f s} (h : Room f s) (j) : Room (pump j f) s := fun p hp => h p (by intro he; apply hp; rw [pump_at,he,mul_zero])
lemma Room.split {f s} (h : Room f s) (he : Far f) (j) : Room (slash j f) s :=
  fun p hp => h p (by intro hx; apply hp; rw [slash_at he,hx,mul_zero])
lemma room_add (f g s) (h : Room f s) (p : Room g s) : Room (f+g) s := by
  intro x hx
  by_cases ht : g x=0
  · apply h
    intro hu; exact hx (by simp [ht,hu])
  exact p x ht

lemma size_node (s v : ℝ) (hs : 0<s) (hv : sun v≠0) (j : ℕ) : 4*s^2 ≤ (s*v*num j)^2 ∧ (s*v*num j)^2 ≤ (2*num j)^2*s^2 := by
  obtain ⟨hk,hx⟩ := sun_pos hv
  have he : 2*s ≤ |s*v*num j| := by
    rw [abs_mul,abs_mul,abs_of_pos (num_pos _),abs_of_pos hs]
    have hj : s*|v| *2 ≤ s*|v| *num j := by gcongr; exact num_ge j
    apply le_trans _ hj
    nlinarith
  have hy : |s*v*num j| ≤ 2*num j*s := by
    rw [abs_mul,abs_mul,abs_of_pos (num_pos _),abs_of_pos hs, show 2*num j*s=s*2*num j by ring]
    refine mul_le_mul_of_nonneg_right ?_ (num_pos _).le; gcongr
  have ht := sq_abs (s*v*num j)
  have hl : |s*v*num j|^2 ≤ (2*num j*s)^2 := by gcongr
  rw [ht,mul_pow (2*num j)] at hl; refine ⟨?_,hl⟩
  rw [← ht]; apply le_trans (b:=(2*s)^2) (le_of_eq (by ring)); gcongr

lemma slot_nonneg (j : ℕ) (E p v s : ℝ) (hs : 0<s) (hv : sun v≠0) (hp : |p|≤s) :
    0≤ ((s*v*num j)^2-p^2)/((s*v*num j)^2+E^2) := by
  have he := (size_node s v hs hv j).1
  refine div_nonneg ?_ (by positivity)
  have hw : p^2 ≤ s^2 := by rw [← sq_abs]; gcongr
  linarith [sq_nonneg s]
lemma kernel_box (m) (E p v s : ℝ) (hs : 0<s) (hv : sun v≠0) (hp : |p|≤s) :
    0≤kernel m (s*v) p E ∧ kernel m (s*v) p E ≤1 := by
  refine ⟨Finset.prod_nonneg fun j _ => slot_nonneg j _ _ _ _ hs hv hp,Finset.prod_le_one (fun j _ => slot_nonneg j _ _ _ _ hs hv hp) fun j _ => ?_⟩
  have he := (size_node s v hs hv j).1
  rw [div_le_one (by nlinarith [sq_nonneg E])]; linarith [sq_nonneg p,sq_nonneg E]
lemma lamp_sign (m s f E) (hs : 0<s) (he : 0≤E) (hf : Ends f) (hg : Plus f) (hr : Room f s) : 0≤Mlamp m s f E := by
  rcases eq_or_lt_of_le he with rfl|hE
  · rw [at_ground]; exact mul_nonneg prepos.le (hg _)
  rw [lamp_lit _ _ _ E hE, sunny m s hs f hf E hE]
  refine mul_nonneg (by positivity) (integral_nonneg ?_)
  intro v
  by_cases hv : sun v=0; · simp [hv]
  apply mul_nonneg (sun_plus v)
  unfold positiveLap
  apply integral_nonneg
  intro x
  by_cases h : f x=0; · simp [h]
  exact mul_nonneg (hg _) (mul_nonneg (raw_n ..) (kernel_box _ _ _ _ _ hs hv (hr x h)).1)

/-- A uniform upper bound for high energy in **arbitrary** interpolating band order
(m constants may depend on m; exponents used in estimates with m later decoupled). -/
def kernelPrice (m : ℕ) := ∏ j∈Finset.range m, (2*num j)^2
lemma kernel_price_pos (m : ℕ) : 0 < kernelPrice m := Finset.prod_pos fun i _ => by
  have he := num_pos i
  exact pow_pos (mul_pos (by norm_num) he) _

lemma kernel_ceiling (m E p v s) (hs : 0<s) (hv : sun v≠0) (hp : |p|≤s) (he : 0<E) :
    kernel m (s*v) p E ≤ kernelPrice m*(s/E)^(2*m) := by
  have H : kernelPrice m*(s/E)^(2*m) = ∏ j∈Finset.range m, ((2*num j)^2*(s/E)^2) := by
    unfold kernelPrice; rw [Finset.prod_mul_distrib, pow_mul, Finset.prod_const]; simp
  rw [H]
  apply Finset.prod_le_prod fun j _ => slot_nonneg j E p v s hs hv hp
  intro j _
  calc
    _ ≤ (s*v*num j)^2/E^2 := by
      refine le_trans ?_ (div_le_div_of_nonneg_left (by positivity : 0≤(s*v*num j)^2) (pow_pos he 2)
        (show E^2≤(s*v*num j)^2+E^2 by linarith [sq_nonneg (s*v*num j)]))
      gcongr; linarith [sq_nonneg p]
    _ ≤ ((2*num j)^2*s^2)/E^2 := by gcongr; exact (size_node s v hs hv j).2
    _ = _ := by rw [mul_div_assoc,div_pow]

lemma kernel_floor (m : ℕ) (E p v s : ℝ) (hs : 1≤s) (hv : sun v≠0) (hp : |p| ≤ s) (he : 0<E) :
    (2:ℝ)⁻¹^m * (1+E)⁻¹^(2*m) ≤ kernel m (s*v) p E := by
  rw [show (2:ℝ)⁻¹^m * (1+E)⁻¹^(2*m) = ∏ j∈Finset.range m, ((2:ℝ)⁻¹ * ((1+E)⁻¹^2)) by simp [mul_pow,pow_mul]]
  refine Finset.prod_le_prod (fun _ _ => by positivity) ?_
  intro j _; obtain ⟨h,hx⟩ := size_node s v (by linarith) hv j
  let b := (s*v*num j)^2
  have ha : s*s ≥ 1 := by nlinarith
  have hl : p^2 ≤ s^2 := by rw [← sq_abs]; gcongr
  have hu : (4:ℝ)≤b := h.trans' (by nlinarith)
  have hb : b+E^2 ≤ b*(1+E)^2 := calc
    _ ≤ b*(1+E^2) := by nlinarith [sq_nonneg E]
    _ ≤ _ := by gcongr; linarith
  refine (le_div_iff₀ (by change 0<b+E^2; linarith [sq_nonneg E])).mpr ?_
  apply le_trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hy : (0:ℝ)<1+E := by linarith
  rw [inv_pow]; field_simp
  rw [← mul_pow,← mul_pow]
  dsimp only [b]; linarith
end YM.Outer
