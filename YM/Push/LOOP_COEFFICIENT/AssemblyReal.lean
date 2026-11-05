import YM.Push.LOOP_COEFFICIENT.Balanced
import YM.Push.LOOP_COEFFICIENT.DriftOperators
import YM.Push.LOOP_COEFFICIENT.LogKernel


/-!
# Assemble logdet and path expressions in the polarized real position convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice RG Wilson Precision Exterior Bloch Laurent Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n c f : Side} {S : StepData c f} {p : Clip} {W : PathData G} {A : Matrix (Body 1 f) (Body 1 c) ℝ}

abbrev onRef (p : Clip) (W : PathData G) (μ : ℝ) := fun b : Loops.Links G n => reference μ p W (vary 1 b)
abbrev onGhost (G : Gauge) (μ : ℝ) := fun b : Loops.Links G n => ghost μ (vary 1 b)

def enlarge {X : Type} [Zero X] [One X] (c : Side) (M : Matrix (BondKey G f) (BondKey G f) X) : Matrix (JointKey G c f) (JointKey G c f) X :=
    (Matrix.fromBlocks M 0 0 (1: Matrix (SiteKey G c) (SiteKey G c) X)).submatrix (Equiv.sumProdDistrib ..) (Equiv.sumProdDistrib ..)

def onLarge (p : Clip) (W : PathData G) (μ : ℝ) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) := enlarge c (onRef p W μ (liftMatrix G A *ᵥ b))

abbrev Shear (G : Gauge) (c f : Side) := Loops.Links G c → Matrix (JointKey G c f) (JointKey G c f) ℝ

def onAdjusted (p : Clip) (W : PathData G) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (χ : Shear G c f) (b : Loops.Links G c) :=
    (χ b).transpose * onBase p W t A b * χ b

structure Sheared (χ : Shear G c f) : Prop where
  germ : ContDiffAt ℝ ω χ 0
  det : ∀ᶠ b in 𝓝 0, (χ b).det^2=1

abbrev ld {a : Type} [Fintype a] [DecidableEq a] (M : Matrix a a ℝ) := Real.log M.det

lemma enlarge_log (M : Matrix (BondKey G f) (BondKey G f) ℝ) : ld (enlarge c M) = ld M := by rw [ld,enlarge,Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,det_one,mul_one]
lemma adjusted_log {t : S.Choices} {χ : Shear G c f} (hχ : Sheared χ) : (ld ∘ onAdjusted p W t A χ) =ᶠ[𝓝 0] (ld ∘ onBase p W t A) := hχ.det.mono fun b hb => by simp only [ld,onAdjusted, Function.comp_apply, det_mul,det_transpose,mul_right_comm _ _ (χ b).det,← pow_two,hb,one_mul]

variable {m k a d : Type} [Fintype m] [Fintype k] [Fintype a] [Fintype d] [DecidableEq m] [DecidableEq k] [DecidableEq a] [DecidableEq d]
    {g h : (m → ℝ) → ℝ}
lemma Coeff.congr (he : g =ᶠ[𝓝 0] h) : Coeff g = Coeff h := congr_arg cmat (bilinearAt_congr he)
lemma Coeff.add (hg : ContDiffAt ℝ ω g 0) (hh : ContDiffAt ℝ ω h 0) : Coeff (g+h) = Coeff g + Coeff h := (congr_arg cmat (bilinearAt_add hg hh)).trans (cmat.map_add ..)
lemma Coeff.smul (c : ℝ) (hg : ContDiffAt ℝ ω g 0) : Coeff (c • g) = (c:ℂ) • Coeff g := by
  rw [show (c:ℂ) • Coeff g = c • Coeff g from IsScalarTower.algebraMap_smul ℂ c _,Coeff,Coeff,← cmat.map_smul]; congr 1
  ext i j; simp only [Matrix.smul_apply,bilinearAt_apply,iteratedFDeriv_const_smul_apply (i:=2) (hg.of_le le_top),_root_.smul_apply]
lemma Coeff.sub (hg : ContDiffAt ℝ ω g 0) (hh : ContDiffAt ℝ ω h 0) : Coeff (g-h) = Coeff g - Coeff h := by
  rw [show g-h = g+(-1:ℝ) • h by simp [sub_eq_add_neg],Coeff.add (h:=(-1:ℝ) • h) hg (hh.const_smul (-1:ℝ)), Coeff.smul _ hh]; simp [sub_eq_add_neg]
lemma Coeff.pre (L : Matrix m k ℝ) (hg : ContDiffAt ℝ ω g 0) : Coeff (fun x => g (L *ᵥ x)) = (cmat L).transpose * Coeff g * cmat L := by
  rw [Coeff,show bilinearAt (fun x => g (L *ᵥ x)) 0 = L.transpose * bilinearAt g 0 * L by
    apply pairing_ext; intro x y; rw [bilinearAt_dotProduct,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,bilinearAt_dotProduct,← Work.F05.bend_apply,← Work.F05.bend_apply]
    exact bend_linear (clm L) hg x y,cmat_mul,cmat_mul]; rfl

lemma Synced.unit {A : Grid n m a} {B : Grid n k d} {X : (m → ℝ) → Matrix k k ℝ} {V : Vertex a d d} {η C : ℝ} (h : Synced A B B (actualMatrix X) V) (hv : LogStrip V η C) : IsUnit (X 0) := by
  have he := Routed.isUnit (fun i => h.base (mon_matches i)) (fun i => hv.unit _ (Work.F07.realStrip _ hv.width (real_frequency i)))
  have h0 : IsUnit (Complex.ofRealHom.mapMatrix (X 0)).det := (isUnit_iff_isUnit_det _).mp he
  rw [← RingHom.map_det, isUnit_iff_ne_zero] at h0
  exact (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr fun hz => h0 (by rw [hz,map_zero]))

variable {F : Forest S.ratio} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G} {μ σ C Λ : ℝ}
lemma onRef_diff (hw : W.Bounds p σ C Λ) (hμ : 0<μ) : ContDiffAt ℝ ω (onRef (n:=n) p W μ) 0 := smooth_reference hμ hw vary_diff
lemma onGhost_diff : ContDiffAt ℝ ω (onGhost (n:=n) G μ) 0 := smooth_ghost μ vary_diff
lemma onGhost_log (hμ : 0<μ) : ContDiffAt ℝ ω (ld ∘ onGhost (n:=n) G μ) 0 := by
  exact logdet_contDiff onGhost_diff ((isUnit_iff_isUnit_det _).mp (ghost_pos _ _ hμ).isUnit)

lemma onLarge_diff (hw : W.Bounds p σ C Λ) (hμ : 0<μ) : ContDiffAt ℝ ω (onLarge p W μ A) 0 := by
  have he := (show ContDiffAt ℝ ω (onRef p W μ) (clm (liftMatrix G A) 0) by rw [map_zero]; exact onRef_diff hw hμ).comp 0 (clm (liftMatrix G A)).contDiff.contDiffAt
  refine matrix_diff ?_; rintro ⟨i|i,_⟩ ⟨j|j,_⟩
  · exact matrix_component he ..
  all_goals exact contDiffAt_const
lemma onAdjusted_diff {t : S.Choices} (h : Admission F ρ p W A P) {χ : Shear G c f} (hχ : Sheared χ) : ContDiffAt ℝ ω (onAdjusted p W t A χ) 0 := by
  obtain ⟨_,_,_,hw⟩ := h.paths; exact smooth_mul (smooth_mul (smooth_transpose hχ.germ) (onBase_diff h.branches hw)) hχ.germ
lemma fee_coeff (hw : W.Bounds p σ C Λ) (hμ : 0<μ) (h : IsUnit (reference μ p W (1:Config G n))) :
    Coeff (fee (n:=n) μ p W) = (1/2:ℂ) • Coeff (ld ∘ onRef p W μ) - Coeff (ld ∘ onGhost G μ) := by
  have he : ContDiffAt ℝ ω (ld ∘ onRef (n:=n) p W μ) 0 := logdet_contDiff (onRef_diff (n:=n) hw hμ) ((isUnit_iff_isUnit_det _).mp (show IsUnit (onRef (n:=n) p W μ 0) by rw [onRef,vary_zero]; exact h))
  rw [show fee (n:=n) μ p W = ((1/2:ℝ) • (ld ∘ onRef p W μ)) - (ld ∘ onGhost G μ) from rfl,Coeff.sub (g:=(1/2:ℝ) • _) (he.const_smul (1/2:ℝ)) (onGhost_log hμ), Coeff.smul _ he]; simp
lemma large_coeff (hw : W.Bounds p σ C Λ) (hμ : 0<μ) (h : IsUnit (reference μ p W (1:Config G f))) :
    let M := cmat (liftMatrix G A); Coeff (ld ∘ onLarge p W μ A) = M.transpose * Coeff (ld ∘ onRef p W μ) * M := by
  have he : ld ∘ onLarge p W μ A = (ld ∘ onRef p W μ) ∘ clm (liftMatrix G A) := funext fun _ => enlarge_log ..
  rw [he]; exact Coeff.pre _ (logdet_contDiff (onRef_diff hw hμ) ((isUnit_iff_isUnit_det _).mp (show IsUnit (onRef (n:=f) p W μ 0) by rw [onRef,vary_zero]; exact h)))
lemma branch_coeff (t : S.Choices) (h : Admission F ρ p W A P) :
    let M := cmat (liftMatrix G A); Coeff (onBranch t p W A) = (1/2:ℂ) • Coeff (ld ∘ onVector p W t A) +
      M.transpose * (Coeff (loop W ∘ vary 1) - Coeff (ld ∘ onGhost G (mu S))) * M := by
  intro M; obtain ⟨_,_,_,hw⟩ := h.paths
  have h₁ : ContDiffAt ℝ ω (ld ∘ onVector p W t A) 0 := logdet_contDiff (onVector_diff h.branches hw) ((isUnit_iff_isUnit_det _).mp (by simpa [onVector] using h.invert_vector t))
  have h₂ := (loop_diff (n:=f) (x:=0) vary_diff hw (U:=vary 1)).sub (onGhost_log (n:=f) (G:=G) (μ:=mu S) mu_pos)
  let v : Loops.Links G f → ℝ := loop W ∘ vary 1 - ld ∘ onGhost G (mu S)
  let L := clm (liftMatrix G A)
  have hE : onBranch t p W A = (1/2:ℝ) • (ld ∘ onVector p W t A) + v ∘ L := by
    ext x; change loop W (positions (background G S A x)) + ((1/2:ℝ) * ld (onVector p W t A x) - ld (ghost (mu S) (positions (background G S A x)))) =
      (1/2:ℝ) * ld (onVector p W t A x) + (loop W (vary 1 (liftMatrix G A *ᵥ x)) - ld (ghost (mu S) _))
    rw [positions_background]; change _ = _ + (_ - ld (ghost _ (vary 1 (liftMatrix G A *ᵥ x)))); ring
  rw [hE,Coeff.add (g:=(1/2:ℝ) • _) (h₁.const_smul (1/2:ℝ)) ((show ContDiffAt ℝ ω v (L 0) by rw [map_zero]; exact h₂).comp 0 L.contDiff.contDiffAt),Coeff.smul _ h₁,show Coeff (v ∘ L) = _ from Coeff.pre (liftMatrix G A) h₂]
  unfold v; rw [Coeff.sub (loop_diff vary_diff hw) (onGhost_log mu_pos)]; simp [M]
end YM.Push.Loops
