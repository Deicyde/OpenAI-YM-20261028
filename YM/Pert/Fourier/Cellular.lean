import YM.Pert.Fourier.Image
/-! Fundamental momentum cells. Difference between continuous and discrete (top) frequency integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Cellular
open Topology Lattice Filter Function Set Metric MeasureTheory YM.Next.Rank.Radian
open scoped BigOperators RealInnerProductSpace Classical
open Band (turn)
variable {n : Side}
def cells := {x:E4 | ∀ i, |x i| ≤ 1/2}
def dtype (v : E4) : ℝ := Full.delta (Band.turn • v)
def clock (a : Cover) (q : E4) := Real.cos (Full.corner a (Band.turn • q))
def trace (a : Cover) (q : E4) := (dtype q)⁻¹ * clock a q
lemma cells_closed : IsClosed cells := by simp only [cells,show {x : E4 | ∀ i, |x i| ≤ 1/2}= ⋂ i,{x : E4 | |x i| ≤ 1/2} by ext; simp]; exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
lemma cells_cube (x : E4) : x∈cells ↔ (Band.turn : ℝ) • x ∈ Full.cube := by
  unfold cells Full.cube; simp only [mem_setOf_eq,PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (by positivity : 0≤Band.turn)]
  apply forall_congr' fun i => ?_; rw [show Real.pi=Band.turn*(1/2) from by ring]
  have hp := Real.pi_pos
  constructor <;> (intro h; nlinarith only [h,hp])
lemma cells_bd {x:E4} (hx : x∈cells): ‖x‖ ≤ 1 := by
  obtain ⟨i,hi⟩ := Band.max_coord x
  exact hi.trans (by have hh : |x i|≤1/2 := hx i; linarith)
lemma cells_ball : cells ⊆ closedBall (0:E4) 1 := by
  intro x hx; change dist x 0≤1; rw [dist_zero_right]; exact cells_bd hx -- adjust
lemma cells_compact : IsCompact cells := (isCompact_closedBall (0:E4) 1).of_isClosed_subset cells_closed cells_ball

def visit (n : Side) (q : E4) := addr n (mark n q)
lemma visit_eps (n : Side) (q : E4) : ‖visit n q - q‖ ≤ 4*(n.val:ℝ)⁻¹ := by rw [← dist_eq_norm]; apply rock
lemma visit_floor (n : Side) (q : E4) (hq : visit n q≠0) : (n.val:ℝ)⁻¹ ≤ ‖visit n q‖ := by
  obtain ⟨i,hi⟩ : ∃ i, visit n q i ≠ 0 := by by_contra! ht; exact hq (by ext i; exact ht i)
  have hx := Band.reads_wrap n (mark n q) i
  have hv : mark n q i ≠ 0 := by
    change ((addr n (mark n q)):E4) i ≠0 at hi
    contrapose hi; simp_all
  calc _ ≤ |visit n q i| := by
          change _ ≤ |addr n (mark n q) i|; rw [hx, abs_div,abs_of_nonneg (Full.val_pos n).le,← one_div]; apply div_le_div_of_nonneg_right _ (Full.val_pos n).le
          have ht : |mark n q i| ≥ 1 := by have := abs_pos.mpr hv; omega
          rw [← Int.cast_abs]; exact_mod_cast ht
       _ ≤ _ := Band.coordinate_le ..
lemma cell_AE : ∀ᵐ q : E4,∀ s : Axis,q s ≠ -(1/2) ∧ q s ≠ 1/2 := by
  apply ae_all_iff.mpr; intro s
  have he (a : ℝ) : ∀ᵐ q : E4, q s≠a := by
     apply ae_iff.mpr; rw [show {q |¬q s≠a} = (WithLp.ofLp:E4→Axis→ℝ) ⁻¹' {u|u s=a} from by ext; simp]; rw [(PiLp.volume_preserving_ofLp Axis).measure_preimage (MeasurableSet.nullMeasurableSet (by apply measurableSet_eq_fun;fun_prop;fun_prop))]; exact Measure.pi_hyperplane (fun _ => volume) _ _
  exact (he (-(1/2:ℝ))).and (he (1/2))
lemma marked_cell (n : Side) (hn : Even n.val) {q : E4} (ht : ∀ s : Axis,q s≠ -(1/2) ∧ q s ≠ 1/2) :
    q∈cells ↔ ((mark n q)∈Set.range (Lattice.lift (n:=n))) := by
  have hp := Full.val_pos n
  obtain ⟨A,hA⟩ := hn
  let k:=mark n q
  have h1 (s : Axis) : mark n q s = ⌈n.val * q s⌉ := by unfold mark; congr 1; field_simp
  constructor
  · intro H; refine ⟨wrap n k,lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩⟩
    rw [h1]; have he : -(A:ℤ) < ⌈n.val * q i⌉ := Int.lt_ceil.mpr (by
        obtain ⟨ha,hb⟩ := abs_le.mp (H i)
        rw [hA] at hp ⊢; push_cast at hp ⊢; nlinarith only [mul_pos hp (show 0<q i + (1/2) from by linarith only [lt_of_le_of_ne ha (Ne.symm (ht i).1)])])
    have he' : ⌈n.val*q i⌉ ≤ (A:ℤ) := Int.ceil_le.mpr (by have hi := (abs_le.mp (H i)).2; have ht := mul_le_mul_of_nonneg_left hi hp.le; rw [hA] at ht ⊢; push_cast at ht ⊢; linarith only [ht])
    omega
  rintro ⟨u,hu⟩ i
  obtain ⟨ha,hb⟩ := hu ▸ lift_centers u i
  rw [h1] at ha hb; have hh : ↑(A+A:ℕ)= (A:ℤ)+A := by simp
  rw [hA,hh] at ha hb
  have hm₁ : -(A:ℤ)< ⌈(↑(A+A:ℕ):ℝ)*q i⌉ := by omega
  have hm₂ : ⌈(↑(A+A:ℕ):ℝ)*q i⌉ ≤ (A:ℤ) := by omega
  rw [Int.lt_ceil] at hm₁; rw [Int.ceil_le] at hm₂; rw [hA] at hp; push_cast at *
  exact abs_le.mpr ⟨by nlinarith only [hm₁,hp],by nlinarith only [hp,hm₂]⟩

lemma integrate_visit (n : Side) (hn : Even n.val) (g : E4→ℝ) : Integrable (cells.indicator (fun x=>g (visit n x))) ∧ (∫ x, cells.indicator (fun x=>g (visit n x)) x) = (n.val:ℝ)⁻¹^4 * ∑ k:Site n, g (addr n (Lattice.lift k)) := by
  let A (k : Site n):= ((tileP n (Lattice.lift k)).indicator fun _ => g (addr n (Lattice.lift k)))
  have he : ∀ᵐ x:E4, cells.indicator (fun x=> g (visit n x)) x = ∑ k:Site n, A k x := by
    filter_upwards [cell_AE] with x hx
    have hq:= marked_cell n hn hx
    by_cases h:x∈cells
    · rw [indicator_of_mem h]; obtain ⟨u:Site n,hu⟩ := hq.mp h
      rw [Finset.sum_eq_single u]
      · exact Eq.symm (by rw [show A u x=g (addr n (Lattice.lift u)) from indicator_of_mem (show x∈tileP n _ from hu.symm) _,hu]; rfl)
      · intro j _ hi; apply indicator_of_notMem; intro hj; exact hi (by rw [←wrap_lift u,←wrap_lift j,hu,(hj:mark n x=lift j)])
      · simp
    rw [indicator_of_notMem h]; symm
    exact Finset.sum_eq_zero fun k _=> indicator_of_notMem (by intro (hh: x∈tileP n _); exact h (hq.mpr ⟨k,(show mark n x=lift k from hh).symm⟩)) _
  have hints k : Integrable (A k) := (integrable_indicator_iff (tiles n _).1).2 (integrableOn_const (μ:=volume) (by
             intro hz
             have h:(0:ℝ)<volume.real (tileP n (Lattice.lift k)) := (tiles n _).2.symm ▸ (pow_pos (YM.Next.Rank.Radian.positive _) _)
             rw [Measure.real,hz] at h; simp at h))
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hints i)).congr (Filter.EventuallyEq.symm he),?_⟩
  simp_rw [integral_congr_ae (f:=fun x=>_) he, integral_finsetSum _ (fun i _=> hints i)]; dsimp only [A]; simp_rw [integral_indicator (tiles n _).1, setIntegral_const, (tiles n _).2,smul_eq_mul,Finset.mul_sum]
lemma visit_defensive (n : Side) (p : Site n) : Band.turn • addr n (Lattice.lift p) = Full.moment p := by ext i; simp only [PiLp.smul_apply,smul_eq_mul,Band.reads_wrap, Full.moment_apply]; unfold Full.mesh; field_simp
end YM.Pert.Cellular
