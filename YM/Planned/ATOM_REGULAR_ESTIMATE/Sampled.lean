import YM.Next.WARD_BIN.Lies
import YM.Planned.ATOM_REGULAR_ESTIMATE.Parametric
import YM.Planned.ATOM_REGULAR_ESTIMATE.Taper


/-!
Probe calculus for the unscaled kernel. Localized germs here are a
lower-level input about a moving path of *measures/samples*, not about
how a given label, or even a regular test with Pi zero, responds. May
use disjoint unions including tagged terms of a signed expansion. Numerical
hypotheses price densities (including differentiated unmarked weights of
these integral expressions) and `f`-independent log-link travel of the samples.
The latter may use a gauge change. Always test the *same* response amplitudes;
no separate optimization of projected or terminal coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice Wilson RG MeasureTheory Push.Local WardBin.Lies
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n m : Side} {B P : BudgetPoint} {X : Support n} {Y : Support m}
    {o : Site n} {a w : ℝ} {V : Config G m}

/-- Domain for testing the weak integral identities. Arbitrary size, no
readout conditions. -/
structure Permitted (P : BudgetPoint) (o : Site n) (X : Support n) (f : Config G n → ℂ) : Prop where
  regular : P.Regular X f
  bound : ∃ C, P.supBounds o X f C

/-- Bulk-response functionals, tested locally as measures acting on the
`Permitted` tests. Else irrelevant. -/
abbrev Feed (G : Gauge) (m n : Side) := (Config G n → ℂ) → Config G m → ℂ

/-- Extra sample variables for one component/sector integral. Can even be
used *near a single base point*, allows locally changing frames,
stencil/Gaussian variables etc., provided weak identities on the SAME
actual kernel. No need for normalized `μ`; when using a normalized sample
law it too has to fit with `density` in these identities. -/
structure Sample (G : Gauge) (m n : Side) where
  Z : Type
  [space : MeasurableSpace Z]
  μ : MeasureTheory.Measure Z
  density : Z → Config G m → ℂ
  link : Z → Config G m → Config G n

/-- Lattice and gauge configurations coincide on all of X and its
one-time flags. -/
def Shadows (X : Support n) (U W : Config G n) :=
  ∃ g : Site n → G.El, Agrees (inspected X) (gauge g U) W
lemma Shadows.value {U W : Config G n} (h : Shadows X U W) {f : Config G n → ℂ} (hf : B.Regular X f) :
    f U = f W := by
  obtain ⟨g,hx⟩ := h; rw [← hf.symmetry g U]; exact hf.sites _ _ (agrees_mono hx fun i hi => Finset.mem_union_left _ hi)



/-- Keep the fine flags even when differentiating the principal kernel germ,
as in `Judged`. -/
def screens (X : Support n) := Finset.univ.filter (fun i : Link n => i.1∈inspected X ∧ i.1 + step i.2∈inspected X)

namespace Sample
attribute [instance] space
variable {S : Sample G m n} {C : Feed G m n} {l k d : ℕ} {U : Slab G m l} {z : S.Z} {f : Config G n → ℂ}
  {W : ℝ}

def inChart (S : Sample G m n) (f : Config G n → ℂ) (z : S.Z) (x : Config G m) :=
  S.density z x * f (S.link z x)

/-- The query-independent local germ of the *unmasked* bulk component as a
kernel acting on the actual fine stencil. The samples active at V according
to `Quiet ∨ ...` below evaluate at true healthy fine fields. Thus on the
prescribed coarse mask this also measures the input WITH fine mask; see
`Center`. Off the mask use the Borel extension in the read and ask locally for
the germ to ensure all derivatives on the closed healthy set.
-/
structure Measures (S : Sample G m n) (B : BudgetPoint) (o : Site n) (X : Support n)
    (V : Config G m) (k : ℕ) (C : Feed G m n) : Prop where
  read (f : Config G n → ℂ) : Permitted B o X f → C f ∘ increment V =ᶠ[𝓝 0]
      average S.μ (fun z => S.inChart f z ∘ increment V)
  covered (f : Config G n → ℂ) : Permitted B o X f → Covered S.μ (fun z => S.inChart f z ∘ increment V) k 0

/-- Travel test with no fine-derivative prediction needed (long or
secondary samples). -/
def Coasting (S : Sample G m n) (z : S.Z) (B : BudgetPoint) (o : Site n) (X : Support n)
    (V : Config G m) (U : Slab G m l) (w : ℝ) :=
  ∃ (g : Config G n) (ν : Panels l → Directions G n), ν 0=0 ∧ Healthy B.threshold X g ∧
    (∀ᶠ t in 𝓝 0, Shadows X (S.link z (journey V l U t)) (increment g (amp B o (ν t)))) ∧
    ContDiffAt ℝ l ν 0 ∧ ∀ i, 0 < i → i ≤ l → ‖iteratedFDeriv ℝ i ν 0‖ ≤ w

/-- Short samples at the actual mask. Leading filtration tests on value and
positive-order jets BEFORE probing f. Includes fluctuations, can even pay
**sample-dependent** shape `w`. Use common Fine gauges on `inspected`. -/
structure Judged (B : BudgetPoint) (o : Site n) (X : Support n) (d : ℕ) (L : Side)
    (w : ℝ) (ν : Panels l → Directions G n) : Prop where
  smooth : ContDiffAt ℝ l ν 0
  home : Short.Taper B o X (screens X) d L w (ν 0)
  jets (i : ℕ) (hi : 0 < i) : i ≤ l → ∀ v : Fin i → Panels l, (∀ j, ‖v j‖ ≤ 1) →
    Short.Taper B o X (screens X) d L w (iteratedFDeriv ℝ i ν 0 v)
  patch : ∀ i∈screens X, ‖limitAmp B o (screens X) (ν 0) i‖ ≤ 1
  segment (s : ℝ) : s ∈ Set.Icc (0:ℝ) 1 → Healthy B.threshold X (bone B o (screens X) (s • ν 0))

def Shoots (S : Sample G m n) (z : S.Z) (B : BudgetPoint) (o : Site n) (X : Support n)
    (V : Config G m) (U : Slab G m l) (w : ℝ) (d : ℕ) (L : Side) :=
  ∃ ν : Panels l → Directions G n, Judged B o X d L w ν ∧
    ∀ᶠ t in 𝓝 0, Shadows X (S.link z (journey V l U t)) (bone B o (screens X) (ν t))

def Tariff (S : Sample G m n) (z : S.Z) (V : Config G m) (U : Slab G m l) (a : ℝ) :=
  let F := S.density z ∘ journey V l U
  ContDiffAt ℝ l F 0 ∧ ∀ i ≤ l, ‖iteratedFDeriv ℝ i F 0‖ ≤ a

def Quiet (S : Sample G m n) (z : S.Z) (V : Config G m) (U : Slab G m l) :=
  S.density z ∘ journey V l U =ᶠ[𝓝 0] 0

variable {R : ℝ}
lemma tariff_bill (h : Tariff S z V U a) (hl : l ≤ k) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hp : ContDiffAt ℝ l (f ∘ S.link z ∘ journey V l U) 0)
    (hh : ∀ i ≤ l, ‖iteratedFDeriv ℝ i (f ∘ S.link z ∘ journey V l U) 0‖ ≤ R) :
    ‖iteratedFDeriv ℝ l (S.inChart f z ∘ journey V l U) 0 cart‖ ≤ 2^k * a * R := by
  have he := product_bound h.1 hp h.2 hh (le_refl l)
  have hi : S.inChart f z ∘ journey V l U = (S.density z ∘ journey V l U) * (f ∘ S.link z ∘ journey V l U) := rfl
  rw [hi]
  have hz (i : Fin l) : ‖cart i‖ ≤ 1 := by
    change ‖(LinearIsometry.single ℝ (fun _ : Fin l => ℝ) i) 1‖ ≤ 1; simp
  exact (le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le he hz)
    (by simp only [Finset.prod_const_one,mul_one]; gcongr; norm_num))

lemma coast_test (h : Coasting S z B o X V U w) {r : ℝ} (hf : B.Regular X f) (hp : B.supBounds o X f r)
    (hw : 1 ≤ w) (hl : l ≤ k) (hk : k≤B.order) : let F := f ∘ S.link z ∘ journey V l U
    ContDiffAt ℝ l F 0 ∧ ∀ i ≤ l, ‖iteratedFDeriv ℝ i F 0‖ ≤ patterns k * (diagonals k*r*w^k) := by
  intro F
  obtain ⟨g,ν,hz,hg,he,hν,hv⟩ := h
  let f' := charted f B o g
  have ht : ContDiffAt ℝ l f' (ν 0) := by
    rw [hz]; exact (smooth_charted (hf.smooth _ hg) B o).of_le (Nat.cast_le.mpr (hl.trans hk))
  have hh : F =ᶠ[𝓝 0] f' ∘ ν := he.mono fun p hp => hp.value hf
  refine ⟨(ht.comp _ hν).congr_of_eventuallyEq hh,fun i hi => ?_⟩
  have hc : 0 ≤ diagonals k*r := mul_nonneg (diagonals_nonneg _) hp.1
  have hx j (hj : j≤l) : ‖iteratedFDeriv ℝ j f' (ν 0)‖ ≤ diagonals k*r := by
    rw [hz]; exact (charted_bound hf hp hg (hj.trans (hl.trans hk))).trans (mul_le_mul_of_nonneg_right (diagonals_le (hj.trans hl)) hp.1)
  rw [(hh.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]
  apply (nest_bound hν ht hi hc hw hv hx).trans
  apply mul_le_mul (show patterns l ≤ patterns k from Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun i _ _ => Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw hl) hc)
    (mul_nonneg hc (pow_nonneg (zero_le_one.trans hw) _)) (patterns_nonneg _)

/-- Keeping explicitly the degree and pre-length factors which come *only*
from taking the regular input test under these kernels. -/
def slopeCost (G : Gauge) (k d : ℕ) := patterns k * (((k:ℝ)+1) * (baseCost G k * (((d+1:ℕ):ℝ)^k)))
lemma slopeCost_nonneg (G : Gauge) (k d : ℕ) : 0 ≤ slopeCost G k d :=
  mul_nonneg (patterns_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (baseCost_nonneg ..) (by positivity)))

theorem principal_test {L : Side} (h : Shoots S z B o X V U w d L) {r : ℝ} {A : Source.Hol G}
    (hf : B.Regular X f) (hp : B.supBounds o X f r) (ha : A.PiVanish d o f) (hx : Nonwrapping X o)
    (hn : 2 ≤ n.val) (hj : ∀ i∈screens X, weight B o i ≤ 1)
    (hw : 1 ≤ w) (hl : l ≤ k) (hk : d+1 ≤ k) (hK : k ≤ B.order) : let F := f ∘ S.link z ∘ journey V l U
    ContDiffAt ℝ l F 0 ∧ ∀ i ≤ l, ‖iteratedFDeriv ℝ i F 0‖ ≤ slopeCost G k d * (r*(w^k*((L.val:ℝ)⁻¹)^(d+1))) := by
  intro F
  obtain ⟨ν,hν,he⟩ := h
  let v := ν 0
  let f' := f ∘ bone B o (screens X)
  let W := ((d+1:ℕ):ℝ) * w
  let s := (L.val:ℝ)⁻¹
  let a := ((k:ℝ)+1)*(baseCost G k*r*(W^k*s^(d+1)))
  have hu : Healthy B.threshold X (bone B o (screens X) v) := by simpa only [one_smul] using hν.segment 1 ⟨zero_le_one,le_refl _⟩
  have ht : F =ᶠ[𝓝 0] f' ∘ ν := he.mono fun p hp => hp.value hf
  have hF : ContDiffAt ℝ l f' (ν 0) := (base_bound hf hp hK hu hν.patch hj).1.of_le (Nat.cast_le.mpr hl)
  have hC : 0 ≤ a := by unfold a W s; positivity [baseCost_nonneg G k, hp.1]
  refine ⟨(hF.comp _ hν.smooth).congr_of_eventuallyEq ht,fun i hi => ?_⟩
  rw [(ht.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]
  have hq := Short.taper_bound ha hf hp hx hn hk hK hν.segment hν.patch hj hw hν.home
  have he' x (hx' : x ≤ k) u (h : ∀ l, Short.Taper B o X (screens X) d L w (u l)) :
      ‖iteratedFDeriv ℝ x f' v u‖ ≤ a := by
    simpa only [one_smul] using! hq x hx' u h 1 ⟨zero_le_one,le_refl _⟩
  apply (slots_bound hν.smooth hF hi hC (fun q b hb => he' _ (q.length_le.trans (hi.trans hl)) _
    (fun j => hν.jets _ (q.partSize_pos _) ((q.partSize_le _).trans hi) _ (fun i => hb _)))).trans
  exact (mul_le_mul_of_nonneg_right (show patterns l ≤ patterns k from Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun i _ _ => Nat.cast_nonneg _)) hC).trans_eq (by unfold a slopeCost W s; ring)

theorem quiet_test (h : Quiet S z V U) (f : Config G n → ℂ) : iteratedFDeriv ℝ l (S.inChart f z ∘ journey V l U) 0=0 := by
  let F := f ∘ S.link z ∘ journey V l U
  have hh : S.inChart f z ∘ journey V l U =ᶠ[𝓝 0] 0 := by
    filter_upwards [h] with x hx; change (S.density z ∘ journey V l U) x * F x=0; rw [hx]; exact zero_mul _
  rw [(hh.iteratedFDeriv (𝕜:=ℝ) l).eq_of_nhds]; simp
end Sample
end YM.Planned.AtomRegular
