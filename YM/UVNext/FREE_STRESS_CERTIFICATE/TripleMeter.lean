import YM.UVNext.FREE_STRESS_CERTIFICATE.Certificate
import YM.UVNext.FREE_STRESS_CERTIFICATE.LocalCross
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle



/-! Tensor–square–square signal on the actual quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Table Climb Next.UVStress Work.A01 Wick Function Set Filter Analysis
variable {G : Gauge} (F : Frames G)


private abbrev doubleToken (a b c d : Axis) : (freeTable F).Tag := ⟨4,flat F a b c d⟩

def tripod (x : Points 3) (i j a c : Axis) : FourFields F →ₗ[ℂ] ℂ := frontRead
    (readings (doubleToken F i j i j) (doubleToken F a c a c)) x 4

theorem trek {x : Points 3} (hx : x∈conf 3) (i j b c a d k t : Axis) :
    tripod F x i j b c (flat F a d k t) = triplet G x (observable G 4 (ff G 4 le_rfl a d k t))
      (observable G 4 (ff G 4 le_rfl i j i j)) (observable G 4 (ff G 4 le_rfl b c b c)) := by
  let f a b c d : (standard F).Token := token F 4 (ff G 4 le_rfl a b c d)
  let g := triangle (f a d k t) (f i j i j) (f b c b c)
  have he (m n s t : Axis) : observable G 4 ((F.level _).coords.symm ((F.level _).coords (ff G 4 le_rfl m n s t))) =
      observable G 4 (ff G 4 le_rfl m n s t) := congr_arg _ ((F.level 4).coords.symm_apply_apply _)
  rw [tripod,front_eval,show Fin.cons (α:=fun _ : Fin 3 => (freeTable F).Tag) ⟨4,flat F a d k t⟩ (readings (doubleToken F i j i j) (doubleToken F b c b c)) =
      (freeTable F).classTokens ∘ g from by
        funext i
        rcases (show i=(0:Fin 3)∨i=1∨i=2 by fin_cases i <;> decide) with rfl|rfl|rfl
        all_goals simp only [g,Function.comp_apply,triangle_zero,triangle_one]
        all_goals rfl, (freeTable F).at_project (freeTable F) (table_sym F) (fun _ => le_rfl) hx,decodes]
  apply congr_arg (fun u : Fin 3 → WickPol G => moment G x u); funext i
  rcases (show i=(0:Fin 3)∨i=1∨i=2 by fin_cases i <;> decide) with rfl|rfl|rfl <;> simp only [g,triangle_zero,triangle_one,triangle_two]
  all_goals exact he _ _ _ _

private lemma phys_leg {x y : E4} (hx : x≠y) (i j a b : Axis) (u v : G.ColorIndex) :
    ((legKernel (curlProbe (initialPlace i j) u) (curlProbe (initialPlace a b) v) (x-y):ℝ):ℂ)=
      if u=v then (bareCurl i j a b (x-y):ℂ) else 0 := shellLink hx ..

private def glow (x : Points 3) (i j b c a d k t : Axis) :=
    bareCurl a d i j (x 0-x 1)*bareCurl k t b c (x 0-x 2)+bareCurl k t i j (x 0-x 1)*bareCurl a d b c (x 0-x 2)

def charge (x : Points 3) (i j b c : Axis) := 4 * (G.lieDim : ℝ) * bareCurl i j b c (x 1-x 2)

private lemma wired {x : Points 3} (hx : x∈conf 3) (i j b c a d k t : Axis) :
    tripod F x i j b c (flat F a d k t) = ((charge (G:=G) x i j b c*glow x i j b c a d k t:ℝ):ℂ) := by
  rw [trek F hx]
  simp only [ff,shell_bond,map_sum,LinearMap.sum_apply,triangle_test hx]
  have hi : x 0≠x 1 := (show Injective x.ofLp from hx).ne (by decide)
  have hj : x 0≠x 2 := (show Injective x.ofLp from hx).ne (by decide)
  have hd : x 1≠x 2 := (show Injective x.ofLp from hx).ne (by decide)
  simp_rw [phys_leg hi,phys_leg hj,phys_leg hd]
  push_cast [charge,glow]
  classical
  have hS (u v w : G.ColorIndex) (x y z f g : ℂ) :
      4*(if u=v then x else (0:ℂ))* ((if w=u then y else 0)*(if w=v then z else 0)+ (if w=u then f else 0)*(if w=v then g else 0)) =
        if w=v then if u=v then 4*x*(y*z+f*g) else (0:ℂ) else 0 := by split_ifs <;> simp_all
  -- u=second label, v=third, sum order likely third then second then first
  simp only [hS]; simp; ring

/-- The only three-point sector needed for the forced flux coefficient. -/
theorem battery (τ : ℝ) {x : Points 3} (hx : x∈conf 3) (i j b c a d : Axis) :
    tripod F x i j b c (torch F τ a d) =
      ((τ * charge (G:=G) x i j b c * crossing (fun m n => bareCurl m n i j (x 0-x 1))
        (fun m n => bareCurl m n b c (x 0-x 2)) a d:ℝ):ℂ) := by
  unfold torch; change tripod F x i j b c (τ • _) = _
  rw [show τ • canonicalStress F a d = (↑τ:ℂ) • canonicalStress F a d from RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _, map_smul,
    canonicalStress,panel,total,map_sub]; unfold crossing; split_ifs with he
  · simp only [map_sum,map_smul,wired F hx,glow,smul_eq_mul]; push_cast
    let u := (charge (G:=G) x i j b c : ℂ)
    have hv (f : Axis → ℂ) : ∑ i, u*f i=u * ∑ i, f i := (Finset.mul_sum ..).symm
    simp_rw [← Finset.mul_sum]
    have hg (f : Axis→Axis→ℂ) : (∑ i, ∑ j, (f i j+f i j))= 2 * ∑ i, ∑ j, f i j := by simp [Finset.sum_add_distrib,two_mul]
    rw [hg]
    ring
  · simp only [map_zero,map_sum,wired F hx,glow,smul_eq_mul]; push_cast
    let u := (charge (G:=G) x i j b c : ℂ); rw [show (∑ k : Axis,u*((↑(bareCurl a k i j (x 0-x 1)):ℂ)*(bareCurl d k b c (x 0-x 2):ℂ)+
      (bareCurl d k i j (x 0-x 1):ℂ)*(bareCurl a k b c (x 0-x 2):ℂ)))= _ from (Finset.mul_sum ..).symm]
    ring

end YM.UVNext.FreeStress
