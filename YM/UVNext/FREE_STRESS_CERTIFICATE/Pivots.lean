import YM.UVNext.FREE_STRESS_CERTIFICATE.Rest
import YM.UVNext.FREE_STRESS_CERTIFICATE.Tangent


/-!
# Rank-two witness by differentiated separated microphones

Avoid assuming kernel jets are faithful in the weight-five quotient. Camera is
same axis as sampled `D_j B_{j0}`; keep the latter differential normalized on
that hierarchy. Remove only a known nonzero common scale. This ranks *inside*
Bel. Use distinct sample without differentiating to detect the remaining
stress column. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Wick Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) (hG : G.Simple)

private def normalize : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (((loud G)⁻¹ • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ)
private lemma gain (h : G.Simple) (i : ℤ) : normalize (G:=G) (loud G * (i:ℂ)) = (i : ℝ) := by
  change ((loud G)⁻¹ * (loud G * (i:ℂ))).re = _
  rw [← mul_assoc,inv_mul_cancel₀ (loud_ne h),one_mul]; simp

-- test component 0 of divergence, against the same curvature squared label,
-- at head location unit axis 0 and spectator location 0.
def switch (a b : Axis) : Vectors H →ₗ[ℝ] ℝ := normalize (G:=G) ∘ₗ
    (((hearing F (camera 0) a b a b 5).restrictScalars ℝ).comp ((LinearMap.proj (0:Axis)).comp (Vectors H).subtype))

variable (W : DiffPlan (freeTable F)) (hW : W.Derivatives (freeTable F)) (ho : W.Orientation H)
include hG hW in
private lemma sees (a b r i j k m : Axis) :
    normalize (G:=G) (hearing F (camera 0) a b a b 5 (W.deriv 4 r (flat F i j k m))) =
    ((slide r 0 i j k m a b a b:ℤ):ℝ) := by
  rw [listens_to F W hW, gain hG]

def coilA : KernelSpace H := ⟨east F,east_on F H⟩
def coilB : KernelSpace H := ⟨west F,west_on F H⟩
def coilC : KernelSpace H := ⟨across F,across_on F H⟩

private lemma switch_read (q : KernelSpace H) (a b : Axis) : switch F H a b (currentDiv W H ho q) =
    ∑ i, normalize (G:=G) (hearing F (camera 0) a b a b 5 (W.deriv 4 i (q.val i 0))) := by
  change normalize ((hearing F (camera 0) _ _ _ _ 5) (∑ i, W.deriv 4 i _)) = _
  simp only [map_sum]; rfl

def spotlight_A (a b : Axis) := ∑ k : Axis, slide 0 0 0 k 0 k a b a b
def spotlight_B (a b : Axis) := ∑ c : Axis, ∑ k : Axis, if c=0 ∨ k=0 then 0 else slide 0 0 c k c k a b a b
def spotlight_C (a b : Axis) := ∑ r : Axis, if r=0 then 0 else ∑ k : Axis, slide r 0 r k 0 k a b a b

include hG hW in
private lemma switch_A (a b : Axis) : switch F H a b (currentDiv W H ho (coilA F H)) = (spotlight_A a b:ℝ) := by
  rw [switch_read]
  change (∑ i : Axis, normalize (G:=G) (hearing F (camera 0) a b a b 5
      (W.deriv 4 i (if i=0 then near F i else 0)))) = _
  rw [Finset.sum_eq_single (0:Axis) (by intro b _ hb; simp [hb]) (by simp)]
  simp only [near,panel,spotlight_A, if_true,map_sum, Int.cast_sum]
  simp_rw [sees F hG W hW]


include hG hW in
private lemma switch_B (a b : Axis) : switch F H a b (currentDiv W H ho (coilB F H)) = (spotlight_B a b:ℝ) := by
  rw [switch_read]
  change (∑ i : Axis, normalize (G:=G) (hearing F (camera 0) a b a b 5
      (W.deriv 4 i (if i=0 then far F i else 0)))) = _
  rw [Finset.sum_eq_single (0:Axis) (by intro b _ hb; simp [hb]) (by simp)]
  unfold far spotlight_B
  simp only [if_true,map_sum, Int.cast_sum]
  apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro k _
  split_ifs
  · simp
  exact sees F hG W hW ..

include hG hW in
private lemma switch_C (a b : Axis) : switch F H a b (currentDiv W H ho (coilC F H)) = (spotlight_C a b:ℝ) := by
  rw [switch_read]; unfold spotlight_C; rw [Int.cast_sum]
  apply Finset.sum_congr rfl; intro r _
  unfold coilC across panel
  split_ifs with H <;> simp [H,map_sum,sees F hG W hW]

-- Kernel-evaluated finite stencil arithmetic, expose sum as four explicit entries.
lemma expand_four {Y : Type*} [AddCommMonoid Y] (f : Axis→Y) : (∑ i : Axis, f i)= f 0 + (f 1 + (f 2+f 3)) := by
  change (∑ i : Fin (3+1), f i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_one]; rfl

set_option linter.unusedSimpArgs false in
private lemma table_A : spotlight_A 0 1 = -256 ∧ spotlight_A 1 2 = 0 := by
  unfold spotlight_A; simp only [expand_four]; decide
set_option linter.unusedSimpArgs false in
private lemma table_B : spotlight_B 0 1 = 0 ∧ spotlight_B 1 2 = -512 := by
  unfold spotlight_B; simp only [expand_four]; decide
set_option linter.unusedSimpArgs false in
private lemma table_C : spotlight_C 0 1 = 128 ∧ spotlight_C 1 2 = -128 := by
  unfold spotlight_C; simp only [expand_four]; decide

def both : KernelSpace H →ₗ[ℝ] ℝ × ℝ := ((switch F H 0 1).prod (switch F H 1 2)).comp (currentDiv W H ho)

include hG hW in
theorem east_column : both F H W ho (coilA F H) = (-256,0) := by
  change (switch F H 0 1 _,switch F H 1 2 _) = _
  simp_rw [switch_A F H hG W hW,table_A.1,table_A.2]; norm_num
include hG hW in
theorem west_column : both F H W ho (coilB F H) = (0,-512) := by
  change (switch F H 0 1 _,switch F H 1 2 _) = _
  simp_rw [switch_B F H hG W hW,table_B.1,table_B.2]; norm_num
include hG hW in
theorem cross_column : both F H W ho (coilC F H) = (128,-128) := by
  change (switch F H 0 1 _,switch F H 1 2 _) = _
  simp_rw [switch_C F H hG W hW,table_C.1,table_C.2]; norm_num

def sightLine : KernelSpace H →ₗ[ℝ] ℝ := normalize (G:=G) ∘ₗ
    (((hearing F (camera 0) 0 2 1 2 4).restrictScalars ℝ).comp ((LinearMap.proj (1:Axis)).comp ((LinearMap.proj (0:Axis)).comp (KernelSpace H).subtype)))

include hG in
set_option linter.unusedSimpArgs false in
theorem last_pivot : sightLine F H (coilC F H) = -16 := by
  change normalize (G:=G) (hearing F (camera 0) 0 2 1 2 4 (panel F 0 1)) = _
  simp only [panel,map_sum,still_listens F,gain hG]
  rw [← Int.cast_sum]; have hh : (∑ k : Axis, look 0 0 k 1 k 0 2 1 2) = -16 := by rw [expand_four]; decide
  rw [hh]; norm_num
theorem first_pivots : sightLine F H (coilA F H) = 0 ∧ sightLine F H (coilB F H) = 0 := by
  change normalize (G:=G) (hearing _ _ _ _ _ _ _ 0) = _ ∧ normalize (G:=G) (hearing _ _ _ _ _ _ _ 0) = _
  simp

end YM.UVNext.FreeStress
