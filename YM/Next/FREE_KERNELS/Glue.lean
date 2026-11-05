import YM.Laurent.Art
import YM.Next.FREE_KERNELS.Moderate

/-!
# Gluing the fundamental cubes, real coefficient export

Use `Vane` (absolute Laurent estimate in axis *sum*-length with counting
coefficients). `market` uses normalized Lebesgue/Haar on the unit torus as
in `YM/Laurent/Rune`. We prove that real overlap identities suffice for this
conversion; no extension assumptions made about the formulas on singular sets
outside the cube. Useful e.g. after the principal pole is cancelled but each
separate formula still looks different at a reciprocal translate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

def relift (p : Momentum) : Cover := fun i => -⌊((p i).re+Real.pi)/(2*Real.pi)⌋

def inside (p : Momentum) := p + reciprocal (relift p)

def placed (f : Momentum → ℂ) (p : Momentum) := f (inside p)

@[simp] lemma reciprocal_imag (x : Cover) (i : Axis) : ((reciprocal x) i).im=0 := by
  simp [reciprocal]

lemma reciprocal_sum (x y : Cover) : reciprocal (x+y)=reciprocal x+reciprocal y := by
  ext i; simp [reciprocal, mul_add]

lemma bounded_inside (p : Momentum) (i : Axis) : |((inside p) i).re| ≤ Real.pi := by
  let z := ((p i).re+Real.pi)/(2*Real.pi)
  have hp := Real.pi_pos
  have hd : 0 < 2*Real.pi := by linarith
  have h1 : (⌊z⌋:ℝ) * (2*Real.pi) ≤ (p i).re+Real.pi := (le_div_iff₀ hd).mp (Int.floor_le z)
  have h2 : (p i).re+Real.pi < ((⌊z⌋:ℝ)+1) * (2*Real.pi) := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one z)
  unfold inside relift reciprocal
  simp only [Pi.add_apply, Complex.add_re, Int.cast_neg, mul_neg, Complex.neg_re, Complex.mul_re,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im]
  change |(p i).re + -((2*Real.pi-0*0)*(⌊z⌋:ℝ) - (2*0+0*Real.pi)*0)| ≤ Real.pi
  rw [abs_le]; constructor <;> linarith

lemma strip_shift {p : Momentum} {η : ℝ} (h : p ∈ strip η) (x : Cover) :
    p+reciprocal x ∈ strip η := by
  intro i
  simpa only [Pi.add_apply, Complex.add_im, reciprocal_imag, add_zero] using h i

lemma physical_shift {p : Momentum} (h : physical p) (x : Cover) : physical (p+reciprocal x) :=
  (physical_iff _).mpr fun i => by
    simp only [Pi.add_apply, Complex.add_im, reciprocal_imag, add_zero]; exact (physical_iff p).mp h i

lemma inside_base {p : Momentum} (h : physical p) : inside p ∈ baseCube :=
  ⟨physical_shift h _, bounded_inside p⟩

lemma inside_cube {p : Momentum} {η : ℝ} (hη : 0<η) (h : p ∈ strip η) :
    inside p ∈ cube η :=
  ⟨strip_shift h _, fun i => (bounded_inside p i).trans_lt (by linarith)⟩

/-- Only a real overlap law; summands on singular divisors of a covariance
recursion often won't themselves have continuous extension on overlaps. -/
def Overlaps (η : ℝ) (f : Momentum → ℂ) := ∀ p ∈ realCube η, ∀ x : Cover,
    p+reciprocal x ∈ realCube η → f (p+reciprocal x)=f p

lemma cube_convex (η : ℝ) : Convex ℝ (cube (α:=Axis) η) := by
  apply (Work.F07.stripConvex _).inter
  intro x hx y hy a b ha hb hz i
  have h₁ := abs_lt.mp (hx i)
  have h₂ := abs_lt.mp (hy i)
  rcases eq_or_lt_of_le ha with ha|ha
  · subst a; simp_all
  rcases eq_or_lt_of_le hb with hb|hb
  · subst b; simp_all
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_lt]
  constructor <;> nlinarith

private def reach (p : Momentum) (z : ℂ) : Momentum := fun i => ((p i).re:ℂ)+z*((p i).im:ℂ)

private lemma reach_convex_aux (p q : Momentum) (z w : ℂ) (a b : ℝ) (h : a+b=1) :
    reach p (a • z+b • w)+q = a • (reach p z+q)+b • (reach p w+q) := by
  funext i
  simp only [reach, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  have ht : (a:ℂ)+(b:ℂ)=1 := by exact_mod_cast h
  linear_combination -(((p i).re:ℂ)+q i)*ht

lemma physical_overlap_hol {η : ℝ} (hη : 0<η) (f : Momentum → ℂ)
    (hf : ∀ p ∈ cube η, DifferentiableAt ℂ f p) (hp : Overlaps η f) {p : Momentum}
    (h : p ∈ cube η) (x : Cover) (hx : p+reciprocal x ∈ cube η) : f (p+reciprocal x)=f p := by
  let U := {z : ℂ | reach p z ∈ cube η ∧ reach p z + reciprocal x ∈ cube η}
  have hc : Continuous (reach p) := by unfold reach; fun_prop
  have hop : IsOpen U := ((cube_open η).preimage hc).inter ((cube_open η).preimage (hc.add continuous_const))
  have hcx : Convex ℝ U := by
    intro z hz w hw a b ha hb hh
    constructor
    · rw [← add_zero (reach p _),reach_convex_aux _ _ _ _ _ _ hh,add_zero,add_zero]
      exact cube_convex η hz.1 hw.1 ha hb hh
    rw [reach_convex_aux _ _ _ _ _ _ hh]
    exact cube_convex η hz.2 hw.2 ha hb hh
  let g := fun z => reach p z + reciprocal x
  have hf1 : DifferentiableOn ℂ (f ∘ reach p) U := fun z hz =>
    ((hf _ hz.1).comp z (by unfold reach; fun_prop)).differentiableWithinAt
  have hf2 : DifferentiableOn ℂ (f ∘ g) U := fun z hz =>
    ((hf _ hz.2).comp z (by unfold g reach; fun_prop)).differentiableWithinAt
  have hr (t : ℝ) : physical (reach p (t:ℂ)) := (physical_iff _).mpr (fun i => by simp [reach])
  have hzero : (0:ℂ)∈U := by
    refine ⟨mem_cube_real ⟨?_,?_⟩ hη,mem_cube_real ⟨?_,?_⟩ hη⟩
    · simpa only [Complex.ofReal_zero] using hr 0
    · intro i; simpa [reach] using h.2 i
    · apply physical_shift
      simpa only [Complex.ofReal_zero] using hr 0
    intro i; simpa [reach] using hx.2 i
  have hi : reach p Complex.I=p := by funext i; apply Complex.ext <;> simp [reach]
  have hie : Complex.I ∈ U := by dsimp only [U,mem_setOf_eq]; rw [hi]; exact ⟨h,hx⟩
  have hh : ∃ᶠ (z : ℂ) in 𝓝[≠] 0, (f ∘ g) z = (f ∘ reach p) z := by
    rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
    intro V hv hv'
    obtain ⟨ε,hε,hv⟩ := Metric.isOpen_iff.mp (hv'.inter hop) _ ⟨hv,hzero⟩
    let s := ε/2
    have hs : 0<s := by unfold s; linarith
    have ht : (s:ℂ) ∈ V ∩ U := hv (by simp [mem_ball, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε,s]; linarith)
    have hi := ht.2
    exact ⟨(s:ℂ), ht.1,hp _ ⟨hr s,hi.1.2⟩ _ ⟨physical_shift (hr s) _,hi.2.2⟩,
      by simpa using hs.ne'⟩
  have he := (hf2.analyticOnNhd hop).eqOn_of_preconnected_of_frequently_eq
    (hf1.analyticOnNhd hop) hcx.isPreconnected hzero hh hie
  dsimp only [comp_apply,g] at he; rwa [hi] at he

lemma hol_on_thickening {f : Momentum → ℂ} {η C : ℝ} (hη : 0 < η) (hf : SafeCube η C f)
    (hp : Overlaps η f) : Vane (placed f) η ∧ (∀ p ∈ strip η, ‖placed f p‖ ≤ C) ∧
      ∀ p ∈ cube η, placed f p=f p := by
  have he (p : Momentum) (x : Cover) (hx : p+reciprocal x ∈ cube η) :
      placed f p = f (p+reciprocal x) := by
    have hh : p ∈ strip η := by
      intro i; simpa only [Pi.add_apply, Complex.add_im, reciprocal_imag, add_zero] using hx.1 i
    have h : inside p = p+reciprocal x + reciprocal (relift p - x) := by
      rw [inside,add_assoc,← reciprocal_sum]; congr 2; abel
    rw [placed, h]
    exact physical_overlap_hol hη f hf.hol hp hx _ (h ▸ inside_cube hη hh)
  refine ⟨⟨hη,fun p h => ?_,fun p h x => ?_⟩,fun p h => hf.bound _ (inside_cube hη h),fun p h => ?_⟩
  · let g (q : Momentum) := q+reciprocal (relift p)
    have hh : g p ∈ cube η := inside_cube hη h
    apply ((hf.hol _ hh).comp p (f:=g) (by unfold g; fun_prop)).congr_of_eventuallyEq
    have hg : Continuous g := continuous_id.add continuous_const
    exact (hg.continuousAt.eventually ((cube_open η).eventually_mem hh)).mono (fun q hq => he q _ hq)
  · unfold placed at *
    rw [he p (x+relift (p+reciprocal x)) ?_]
    · rw [reciprocal_sum,inside,add_assoc]
    rw [reciprocal_sum,← add_assoc]; exact inside_cube hη (strip_shift h _)
  have hr : reciprocal (0:Cover) = 0 := by ext i; simp [reciprocal]
  have hv : p+reciprocal (0:Cover)=p := by rw [hr,add_zero]
  exact (he p 0 (hv.symm ▸ h)).trans (congr_arg f hv)

/-- Real coefficient export of a cube symbol. -/
def tape (f : Momentum → ℂ) (x : Cover) : ℝ := (market (placed f) 0 x).re

def RRead (a : Cover → ℝ) : Momentum → ℂ := read fun i => (a i:ℂ)

lemma RRead_paints {f : Momentum → ℂ} {η C : ℝ} (hp : 0<η) (hf : SafeCube η C f)
    (ht : Overlaps η f) (hs : ∀ p ∈ realCube η, star (f (-p))=f p) (p : Momentum) (hy : p ∈ realCube η) :
    RRead (tape f) p = f p := by
  obtain ⟨hq,hb,hr⟩ := hol_on_thickening hp hf ht
  have hL := hq.issues hb (η/3) (η/3) (by positivity) (by positivity) (by linarith)
  unfold RRead tape
  have he := Work.F07.readRealPart hL (by linarith) hy.1
  have h1 := mem_cube_real hy hp
  have h2 := cube_neg _ h1
  rw [he,hq.paints hb p h1.1,hq.paints hb _ h2.1,hr _ h1,hr _ h2, hs p hy]
  ring

lemma realCube_mono {a b : ℝ} (ha : a ≤ b) : realCube a ⊆ realCube b :=
  fun _ hp => ⟨hp.1,fun i => (hp.2 i).trans_le (add_le_add_right ha _)⟩

lemma Overlaps.mono {η θ : ℝ} {f : Momentum → ℂ} (h : Overlaps η f) (ht : θ≤η) : Overlaps θ f :=
  fun p hp x hx => h p (realCube_mono ht hp) x (realCube_mono ht hx)

variable {ι : Type*} {f : ι → Momentum → ℂ} {w : ι → ℝ}

/-- Coefficient (not physical matrix size) promise. Exponents sum over all
axis lengths on the cover. -/
def SoundTape (w : ι → ℝ) (f : ι → Cover → ℝ) : Prop := ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ i,
  Width σ (C*w i) (f i)

lemma tapes_sound (h : Moderate w f) {η : ℝ} (hp : 0<η) (hg : ∀ i, Overlaps η (f i)) :
    SoundTape w (fun i => tape (f i)) := by
  obtain ⟨θ,C,ht,hC,h⟩ := h
  let s := min θ η
  have hs : 0 < s := lt_min ht hp
  let b := s/3
  have hb : 0 < b := by unfold b; linarith
  let B := (2*((1+b)/b))^(Fintype.card Axis)
  refine ⟨b,C*B,hb,by unfold B; positivity,fun i => ?_⟩
  obtain ⟨hv,hk,-⟩ := hol_on_thickening hs ((h i).mono (min_le_left ..) le_rfl) ((hg i).mono (min_le_right ..))
  have he := Work.F07.widthRealPart (hv.issues hk b b hb.le hb (by unfold b; linarith))
  dsimp only [tape]
  rw [mul_right_comm]; exact he

lemma tapes_read (h : Moderate w f) {η : ℝ} (hp : 0 < η) (hg : ∀ i, Overlaps η (f i))
    (hs : ∀ i, ∀ p ∈ realCube η, star (f i (-p))=f i p) :
    ∃ θ > 0, ∀ i, ∀ p ∈ realCube θ, RRead (tape (f i)) p=f i p := by
  obtain ⟨θ,C,ht,hC,h⟩ := h
  refine ⟨min θ η,lt_min ht hp,fun i => RRead_paints (lt_min ht hp) ((h i).mono (min_le_left ..) le_rfl)
    ((hg i).mono (min_le_right ..)) fun p hh => hs i p (realCube_mono (min_le_right ..) hh)⟩

end YM.Next.Free
