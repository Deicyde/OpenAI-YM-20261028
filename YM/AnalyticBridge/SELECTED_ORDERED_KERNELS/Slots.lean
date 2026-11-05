import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Frame
import YM.Push.FREE_RESOLVENT.Layout


/-!
# Equality in the actual exponential/counting coordinate convention of FREE_RESOLVENT

Mix colours *only on the link of a block*. Later this is why the costs of
converting inverse jets do not depend on any period or block size.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior FreeResolvent Affine
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {j k : ℕ}

abbrev Pins (G : Gauge) (n : Side) (j : ℕ) := Fin j → raw G n

def edge (w : raw G n) : Edge (Site n) := (w.1,axisEquiv.symm w.2.1)
def hue (e : Edge (Site n)) (i : G.ColorIndex) : raw G n := (e.1,axisEquiv e.2,i)
@[simp] lemma hue_edge (w : raw G n) : hue (edge w) (G:=G) w.2.2 = w := by simp only [edge,hue, Equiv.apply_symm_apply]
@[simp] lemma edge_hue (e : Edge (Site n)) (i : G.ColorIndex) : edge (hue e (G:=G) i)=e := by simp only [edge,hue, Equiv.symm_apply_apply]

def paint (G : Gauge) (n : Side) : Vec G n 1 ≃L[ℝ] Directions G n := LinearEquiv.toContinuousLinearEquiv ({
  toFun v := collect G (decode v)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := fun y w => y (edge w) w.2.2
  left_inv v := by
    ext w; change v (hue (edge w) (G:=G) w.2.2) = _; rw [hue_edge]
  right_inv y := by
    ext e i; change y (edge (hue e (G:=G) i)) i = _; rw [edge_hue] } : Vec G n 1 ≃ₗ[ℝ] Directions G n)

lemma paint_apply (v : Vec G n 1) (e : Edge (Site n)) (i : G.ColorIndex) : paint G n v e i = v (hue e i) := rfl
lemma unpaint_apply (A : Directions G n) (w : raw G n) : (paint G n).symm A w = A (edge w) w.2.2 := rfl

def unitDir (w : raw G n) := paint G n (ray G n w)

lemma unit_here (w : raw G n) : unitDir w (edge w) = EuclideanSpace.single w.2.2 1 := by
  ext i
  change ray G n w (hue (edge w) i) = _
  by_cases h : i=w.2.2
  · subst i; simp [ray]
  have he : hue (edge w) (G:=G) i ≠ w := fun H => h (congr_arg (fun x : raw G n => x.2.2) H)
  simp [ray,he,h]

lemma unit_off (w : raw G n) (e : Edge (Site n)) (h : e ≠ edge w) : unitDir w e=0 := by
  ext i
  have he : hue e (G:=G) i ≠ w := fun H => h (by rw [← H, edge_hue])
  change ray G n w (hue e i) = 0
  rw [ray,Pi.single_eq_of_ne he]

lemma unit_le (w : raw G n) (e : Edge (Site n)) : ‖unitDir w e‖ ≤ 1 := by
  by_cases h : e=edge w
  · rw [h, unit_here, PiLp.norm_single, norm_one]
  rw [unit_off _ _ h,norm_zero]; exact zero_le_one

lemma color_le (v : G.Color) (i : G.ColorIndex) : |v i| ≤ ‖v‖ := by
  simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul]
    using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Config G n → E}
    {V : Config G n}

/-- Ordinary log chart function for the actual kernel under test. -/
def over (F : Config G n → E) (V : Config G n) (v : Vec G n 1) := F (increment V (paint G n v))

theorem smooth_over : ContDiffAt ℝ j (over F V) 0 ↔ Germ j F V := by
  let e := paint G n
  constructor
  · intro h
    rw [show Germ j F V = ContDiffAt ℝ j (over F V ∘ (⇑e.symm : Directions G n → Vec G n 1)) 0 from by
      simp [over,comp_def,e,WardBin.Lies.Germ]]
    exact ((map_zero e.symm).symm ▸ h).comp _ e.symm.contDiff.contDiffAt
  intro h
  exact ((map_zero e).symm ▸ (show ContDiffAt ℝ j (F ∘ increment V) 0 from h)).comp _ e.contDiff.contDiffAt

theorem expand_over (A : Slab G n j) (h : ContDiffAt ℝ j (over F V) 0) :
    leftDerivs F (List.ofFn A) V = ∑ p : OrderedFinpartition j,
      iteratedFDeriv ℝ p.length (over F V) 0 ((paint G n).symm ∘ term (fun _ => frame G j) p A) := by
  rw [expand (smooth_over.mp h)]; refine Finset.sum_congr rfl fun p _ => ?_
  have hr : F ∘ increment V = over F V ∘ ⇑(paint G n).symm.toContinuousLinearMap := by
    ext a; exact congr_arg (fun z => F (increment V z)) ((paint G n).apply_symm_apply a).symm
  rw [hr,YM.Next.Foundations.jets_linear _ (h.of_le (Nat.cast_le.mpr p.length_le))]; rfl

/-- Ordered Lie derivative at prescribed *physical slots*, every occurrence
retained. (Not `jet` of the log chart.) -/
def ordered (F : Config G n → E) (V : Config G n) (z : Pins G n j) :=
  leftDerivs F (List.ofFn (unitDir ∘ z)) V

lemma ordered_sub {H : Config G n → E} (z : Pins G n j) (hf : Germ j F V) (hH : Germ j H V) :
    ordered (F-H) V z = ordered F V z - ordered H V z := hf.takes_sub hH _ (by simp)

def pivot (p : OrderedFinpartition j) (z : Pins G n j) (b : Fin p.length) := edge (z (p.emb b ⟨0,p.partSize_pos b⟩))

def repaint (p : OrderedFinpartition j) (z : Pins G n j) (b : Fin p.length) (i : G.ColorIndex) :=
    hue (G:=G) (pivot p z b) i

def coeff (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (b : Fin p.length) (i : G.ColorIndex) : ℝ := term φ p (unitDir ∘ z) b (pivot p z b) i

lemma coeff_bound (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (b : Fin p.length) (i : G.ColorIndex) :
    |coeff φ p z b i| ≤ ‖iteratedFDeriv ℝ (p.partSize b) (φ (pivot p z b)) 0‖ := by
  refine (color_le (G:=G) _ _).trans ((term_cost φ p (unitDir ∘ z) b _).trans ?_)
  exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun r _ => norm_nonneg _)
    fun r _ => unit_le ..)

lemma coeff_support (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (b : Fin p.length) (i : G.ColorIndex) (h : coeff φ p z b i ≠ 0) (r : Fin (p.partSize b)) :
    edge (z (p.emb b r)) = pivot p z b := by
  by_contra he
  apply h
  unfold coeff
  rw [term_zero φ p _ _ _ (i:=r) (show unitDir (z (p.emb b r)) _ = _ from unit_off _ _ (Ne.symm he))]; rfl

lemma term_palette (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (b : Fin p.length) : (paint G n).symm (term φ p (unitDir ∘ z) b) =
      ∑ i, coeff φ p z b i • ray G n (repaint p z b i) := by
  let e := pivot p z b
  ext w
  simp only [unpaint_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : edge w=e
  · rw [Finset.sum_eq_single w.2.2]
    · have hr : repaint p z b w.2.2=w := by change hue e (G:=G) _=w; rw [← h, hue_edge]
      simp only [hr,ray,Pi.single_eq_same,mul_one,coeff,h]; rfl
    · intro i _ hi
      rw [ray,Pi.single_eq_of_ne (show w ≠ repaint p z b i from fun H => hi (congr_arg (fun x : raw G n => x.2.2) H).symm),mul_zero]
    simp
  rw [term_zero φ p _ b (edge w) (i:=⟨0,p.partSize_pos b⟩) (unit_off _ _ h)]
  refine Eq.symm (Finset.sum_eq_zero fun i _ => ?_)
  have hh : w ≠ repaint p z b i := fun H => h (by rw [H]; exact edge_hue ..)
  rw [ray, Pi.single_eq_of_ne hh, mul_zero]

theorem palette (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (z : Pins G n j)
    (L : Vec G n 1 [×p.length]→L[ℝ] E) : L ((paint G n).symm ∘ term φ p (unitDir ∘ z)) =
      ∑ c : Fin p.length → G.ColorIndex, (∏ b, coeff φ p z b (c b)) • L (fun b => ray G n (repaint p z b (c b))) := by
  simp_rw [comp_def (f:=⇑(paint G n).symm),term_palette,L.map_sum,L.map_smul_univ]

end YM.SelectedOrderedKernels
