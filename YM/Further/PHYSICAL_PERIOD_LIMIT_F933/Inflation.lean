import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Polytrace
import YM.Next.FOUNDATIONS.SU2
import YM.Push.STATIONARY_UNIFORM.Paths


/-! # Offered: intensive paid absolute scale of uncovered determinant-Haar on real waves. q per-cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Inflation
open Function Gauge Filter Bid Lattice Finset Push.Uniform RG Wilson Tree Precision Bloch Exterior Jacobi
  Polytrace  
open scoped Topology ContDiff BigOperators ComplexConjugate Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {ι : Type} [Fintype ι] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_atom (i r:Site c) : ‖cell i r‖=1 := by
  let z := cell i r
  have hx : ‖z‖>0 := norm_pos_iff.mpr (cell_ne i r)
  have hr : ‖z‖=‖z⁻¹‖ := by rw [show z⁻¹=conj z from (cell_bar i r).symm,Complex.norm_conj]
  have he := congr_arg (· * ‖z‖) hr; rw [norm_inv,inv_mul_cancel₀ hx.ne'] at he
  nlinarith

lemma decomposed (K : (Positions ι →L[ℝ] Positions ι →L[ℝ] E)) (u v : Positions ι) :
    K u v = ∑ i, u i • ∑ j, v j • K (bolt i) (bolt j) := by
  conv_lhs => rw [by_row K u,_root_.sum_apply]
  exact Finset.sum_congr rfl fun i _=> congr_arg (u i •·) (by_row (K (bolt i)) v)
lemma toll {n : Side} (l : ι → Site n) {K : ℕ} {a C : ℝ} (M : Positions ι →L[ℝ] Positions ι →L[ℝ] E) (ha : 0<a)
    (hc : 0 ≤ C) (hm : Multiplicity l K) (he : ∀ i j, ‖M (bolt i) (bolt j)‖ ≤ C*Decay a (l i) (l j)) (u v : Positions ι) (hu : ‖u‖≤1) (hv : ‖v‖≤1) :
    ‖M u v‖ ≤ (Fintype.card ι:ℝ)*(C*space K a) := by
  rw [decomposed]; apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ i:ι,C*space K a := Finset.sum_le_sum fun i _=> by
      rw [norm_smul]; apply ((mul_le_mul (le_trans (norm_le_pi_norm u i) hu) (norm_sum_le Finset.univ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)).trans
      apply le_trans (Finset.sum_le_sum (fun j _ => show ‖v j • M (bolt i) (bolt j)‖ ≤ C*Decay a (l i) (l j) from by
        rw [norm_smul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) ((norm_le_pi_norm _ j).trans hv)) (he ..)))
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hm.count _ ha _) hc
    _ = _ := by simp

abbrev fiso (G : Gauge) (c : Side) := tint G (Body 1 c)
abbrev lame (i : Site c) (σ : TypeFace 1→G.ColorIndex→ℂ) := (fiso G c).symm (wave i σ)
lemma score (i : Site c) (σ : TypeFace 1→G.ColorIndex→ℂ) (ht : ∀ f j, ‖σ f j‖≤1) : ‖lame (G:=G) i σ‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro x
  change ‖(cell i x.1.1 * σ x.1.2 x.2).re‖ ≤ _
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul,norm_atom,one_mul]; exact ht ..
lemma spectrum (F : fieldDir G c 1→E) (U V : fieldDir G c 1) (h : ContDiffAt ℝ ω (F ∘ fiso G c) 0) :
    (iteratedFDeriv ℝ 2 F 0) ![U,V] = (iteratedFDeriv ℝ 2 (F ∘ fiso G c) 0) ![(fiso G c).symm U,(fiso G c).symm V] := by
  let L := (fiso G c).symm
  let K := F ∘ fiso G c
  have he0 (Z : Positions (Primary c G) → E) x W (h : ContDiffAt ℝ ω Z (L x)) : blade W (Z ∘ L) x= blade (L W) Z (L x) := by
    unfold blade; rw [fderiv_comp _ (h.differentiableAt (by simp)) L.differentiableAt, L.fderiv]; rfl
  change ContDiffAt ℝ ω K 0 at h
  have hK : ContDiffAt ℝ ω K (L 0) := map_zero L ▸ h
  have hF : F= K ∘ L := by funext; unfold L K; simp
  have he : blade V F =ᶠ[𝓝 0] blade (L V) K ∘ L := by
    filter_upwards [L.continuous.continuousAt.tendsto.eventually (hK.eventually (by simp))] with x hx; exact hF ▸ he0 K _ _ hx  
  change iteratedFDeriv ℝ 2 F _ _=iteratedFDeriv ℝ 2 K 0 _
  rw [← iter _ _ (f:=K) h, ← iter _ _ (show ContDiffAt ℝ ω F 0 from by rw [hF]; exact hK.comp (f:=L) _ L.contDiff.contDiffAt)]
  unfold mixed; rw [show blade U (blade V F) 0=blade U (blade (L V) K ∘ L) 0 from congr_arg (fun Λ : fieldDir G c 1 →L[ℝ] E=> Λ U) he.fderiv_eq, he0 _ _ _ (smooth _ hK),map_zero]

variable {B : Forest S.ratio} (t : S.Choices) {μ C Λ : ℝ} {p : Clip} {R : PathData G} {O : ChartRatio G}
  {j n : ℕ} {Q : KernelChoices}
variable (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) (h : 4≤n)
variable (A : Push.Uniform.Before G μ C j Q n) (he : LocalRatio O) {ρ : Push.In G c→AxisChart G B} (hh : Critical B p R ρ)
include t hp hK hj ht h A he hh

local notation "Y" => A.tables p S.patch
-- constant pre-p chosen only from the Stage's patch and Before. uniform for ALL paths meeting PathBounds.


end YM.Further.PhysicalPeriodLimitF933.Inflation
