import YM.Maxwell.Bilinear
import YM.Next.MAXWELL.Jets

/-!
# Responses and mixed derivatives from both ends

One test source at `x`, field it produces at `y`; also basic linear-leg
manipulations common to Ward, spectral and Wick proofs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {j k l : ℕ}

/-- Convenient proof-free reader for one jet on a local solution. The
chosen extension doesn't matter on its open solution domain. -/
def sample (p : Probe G j) (f : Field G.Color) (x : E4) : ℝ :=
  extension p (nth f j x)

theorem sample_eval (p : Probe G j) {f : Field G.Color} {U : Set E4} (H : WaveOn U f) (hU : IsOpen U)
    {x : E4} (hx : x ∈ U) : sample p f x = p ⟨nth f j x,H.jets hU hx⟩ :=
  LinearMap.congr_fun (genuine p) ⟨_,H.jets hU hx⟩

@[simp] theorem sample_addLeg (p q : Probe G j) (f : Field G.Color) (x) :
    sample (p+q) f x = sample p f x + sample q f x := rfl

@[simp] theorem sample_smulLeg (t : ℝ) (p : Probe G j) (f : Field G.Color) (x) :
    sample (t • p) f x = t * sample p f x := rfl

theorem sample_smooth (p : Probe G j) {f : Field G.Color} {U : Set E4} (H : WaveOn U f) {x : E4} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (sample p f) x :=
  (extension p).toContinuousLinearMap.contDiff.contDiffAt.comp x (H.nth_smooth hx)





theorem sample_eq_of_germ {p : Probe G j} {f g : Field G.Color} {x : E4}
    (h : ∀ a b, f a b =ᶠ[𝓝 x] g a b) : sample p f x = sample p g x := by
  have he : nth f j x = nth g j x := funext fun a => funext fun b => Tensor.GermCoeff j (h a b)
  rw [sample, sample, he]

/-- At order zero or higher, actual coordinate derivative probes. -/
def leg (u : Fin j → E4) (c : G.ColorIndex) (i m : Axis) : Probe G j :=
  constrain (G := G) (fromF G u c i m)

theorem leg_eval (u : Fin j → E4) (c : G.ColorIndex) (i m : Axis) (A : Shell G j) :
    leg u c i m A = A.val i m u c := rfl

theorem sample_leg (u : Fin j → E4) (c : G.ColorIndex) (i m : Axis) {f : Field G.Color} {U : Set E4}
    (H : WaveOn U f) (hU : IsOpen U) {x : E4} (hx : x ∈ U) :
    sample (leg u c i m) f x = Tensor.coeff (f i m) j x u c := sample_eval _ H hU hx

theorem leg_probe_induction {P : Probe G j → Prop}
    (vars : ∀ u c i m, P (leg u c i m)) (zero : P 0)
    (add : ∀ p q, P p → P q → P (p+q)) (smul : ∀ t : ℝ, ∀ p, P p → P (t • p))
    (p : Probe G j) : P p := by
  refine Submodule.span_induction (p := fun p _ => P p) ?_ zero (fun p q _ _ => add p q)
    (fun t p _ => smul t p) (show p ∈ _ from spans.symm ▸ Submodule.mem_top)
  rintro q ⟨u,c,i,m,rfl⟩; exact vars u c i m

def raiseLeg (v : E4) : Probe G j →ₗ[ℝ] Probe G (j+1) where
  toFun p := p.comp (lower G.Color j v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem raises (v : E4) (u : Fin j → E4) (c : G.ColorIndex) (i m : Axis) :
    raiseLeg v (leg u c i m) = (↑(j+1 : ℕ) : ℝ) • leg (Fin.cons v u) c i m := by
  ext x
  rfl

theorem sample_deriv_label (u : E4) (p : Probe G j) {U : Set E4} {f : Field G.Color}
    (H : WaveOn U f) (hU : IsOpen U) {x : E4} (hx : x ∈ U) :
    sample p (fun i l => D u (f i l)) x = sample (raiseLeg u p) f x := by
  rw [sample_eval _ (wave_D H hU _) hU hx, sample_eval _ H hU hx]
  apply congr_arg p (Subtype.ext (samples_D H hU u hx))

theorem sample_deriv (p : Probe G j) (u : E4) {f : Field G.Color} {x : E4}
    (H : ∀ a b, ContDiffAt ℝ (↑(j+1 : ℕ)) (f a b) x) :
    D u (sample p f) x = sample p (fun a b => D u (f a b)) x := by
  let L := (extension p).toContinuousLinearMap
  have ht (a b : Axis) : DifferentiableAt ℝ (fun y => nth f j y a b) x :=
    (differentiableAt_const (Nat.factorial j : ℝ)⁻¹).smul ((H a b).differentiableAt_iteratedFDeriv (m := j)
      (Nat.cast_lt.mpr j.lt_succ_self))
  have hs := (hasFDerivAt_pi.mpr fun (a : Axis) => hasFDerivAt_pi.mpr fun (b : Axis) =>
    (ht a b).hasFDerivAt)
  change fderiv ℝ (L ∘ nth f j) x u = L _
  rw [fderiv_comp x L.differentiableAt (show DifferentiableAt ℝ (nth f j) x from hs.differentiableAt),
    L.fderiv,ContinuousLinearMap.comp_apply]
  congr 1
  rw [hs.fderiv]
  exact funext fun a => funext fun b => D_coeff (H a b) u

/-- Field produced by p at x, on the punctured space. (Totalized at x only
for the usual convention about test-functions.) -/
def pulse (p : Probe G j) (x : E4) : Field G.Color := fun a b y =>
  responded G (extension p) a b (x-y)

lemma pulse_wave (p : Probe G j) (x : E4) : WaveOn ({x}ᶜ) (pulse p x) := by
  let T : Field G.Color := fun i l z => responded G (extension p) i l (-z)
  have ht : WaveOn away T := wave_neg_pull (wave_mono (by
    rintro _ ⟨u,hu,rfl⟩; exact neg_ne_zero.mpr hu) (response (G := G) _))
  have he : ((fun y : E4 => y-x) '' ({x} : Set E4)ᶜ) ⊆ away := by
    rintro _ ⟨v,hv,rfl⟩; exact sub_ne_zero.mpr hv
  rw [show pulse p x = (fun a b y => T a b (y-x)) from by
    ext1 a; ext1 b; ext1 y; simp only [T,neg_sub,pulse]]
  exact wave_sub_pull x (wave_mono he ht)

@[simp] theorem pulse_add (p q : Probe G j) (x) : pulse (p+q) x = pulse p x + pulse q x :=
  funext fun i => funext fun m => funext fun y => by unfold pulse; rw [responds_add]; rfl

@[simp] theorem pulse_scale (p : Probe G j) (x) (t : ℝ) : pulse (t • p) x = t • pulse p x :=
  funext fun i => funext fun m => funext fun y => by unfold pulse; rw [responds_smul]; rfl

@[simp] theorem pulse_zero (x) : pulse (0 : Probe G j) x = 0 := by
  simpa only [zero_smul] using pulse_scale (0 : Probe G j) x 0

def K (p : Probe G j) (q : Probe G l) (x y : E4) := legKernel p q (x-y)

lemma K_pairing (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) :
    K p q x y = pairing (show x-y ∈ away from sub_ne_zero.mpr h) p q := rfl

theorem K_sample (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) :
    K p q x y = sample q (pulse p x) y := by
  have he : nth (pulse p x) l y = (-1 : ℝ)^l • nth (responded G (extension p)) l (x-y) :=
    funext fun i => funext fun m => oppositeCoeff x y
      (((response (G := G) (extension p)).smooth i m _ (sub_ne_zero.mpr h)).of_le
        (WithTop.coe_le_coe.mpr le_top))
  rw [sample, he, map_smul]; rfl

lemma K_symmetric (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) : K p q x y = K q p y x := by
  rw [K,K,← neg_sub x y]; exact exchange _ _ (sub_ne_zero.mpr h)

lemma K_across (p : Probe G j) (q : Probe G l) (x y t : E4) : K p q (x+t) (y+t) = K p q x y := by
  rw [K,K,add_sub_add_right_eq_sub]

lemma K_smooth (p : Probe G j) (q : Probe G l) (z : E4 × E4) (h : z.1 ≠ z.2) :
    ContDiffAt ℝ ∞ (fun (w : E4 × E4) => K p q w.1 w.2) z :=
  (kernel_smooth p q (x := z.1-z.2) (sub_ne_zero.mpr h)).comp z (contDiffAt_fst.sub contDiffAt_snd)

theorem K_right_D (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) (u : E4) :
    D u (K p q x) y = K p (raiseLeg u q) x y := by
  have he : K p q x =ᶠ[𝓝 y] sample q (pulse p x) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show y ∈ ({x} : Set E4)ᶜ from Ne.symm h)] with z hz
    exact K_sample _ _ (Ne.symm hz)
  rw [GermD u he, K_sample _ _ h, sample_deriv q u (fun a b =>
    ((pulse_wave p x).smooth a b y (Ne.symm h)).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact sample_deriv_label u q (pulse_wave p x) isOpen_compl_singleton (Ne.symm h)

theorem K_left_D (p : Probe G j) (q : Probe G l) {x y : E4} (h : x ≠ y) (u : E4) :
    D u (fun z => K p q z y) x = K (raiseLeg u p) q x y := by
  have he : (fun z => K p q z y) =ᶠ[𝓝 x] K q p y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ ({y} : Set E4)ᶜ from h)] with z hz
    exact K_symmetric p q hz
  rw [GermD u he,K_symmetric (raiseLeg u p) q h,K_right_D q p (Ne.symm h)]

/-- Zero-order leg. -/
def omegaLeg (c : G.ColorIndex) (i m : Axis) : Probe G 0 := leg (fun _ => 0) c i m

lemma K_observe (p : Probe G j) (c : G.ColorIndex) (a b : Axis) {x y : E4} (h : x ≠ y) :
    K p (omegaLeg c a b) x y = pulse p x a b y c := by
  rw [K_sample _ _ h, omegaLeg,sample_leg _ _ _ _ (pulse_wave ..) isOpen_compl_singleton
    (Ne.symm h), coeff_apply_zero]

lemma omega_K_eq (c d : G.ColorIndex) (i m a b : Axis) {x y : E4} (h : x ≠ y) :
    K (omegaLeg c i m) (omegaLeg d a b) x y = if c=d then bareCurl i m a b (x-y) else 0 := by
  rw [show K (omegaLeg c i m) (omegaLeg d a b) x y = _ from reads_mixed _ _ _ _ _ _ _ _ h]
  simp only [coeff_apply_zero]

end YM.Maxwell.Free
