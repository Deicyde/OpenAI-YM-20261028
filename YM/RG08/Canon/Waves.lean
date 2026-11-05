import YM.RG08.Canon.Pictures
import YM.Next.STATIONARY.Loops.Curvature
/-! # Reading FiniteBound real test as compatible factorial wave on
 both ℝ and ℂ. No limit on period label count hidden. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p q : Clip} {R T : PathData G} {ρ : fieldDir G c 1 → AxisChart G F} {D : ChartRatio G}
local notation "W" => TypeFace 1 → G.ColorIndex→ℂ

private def uno (a : Loc G 1) (k : ℂ) : TypeFace 1→G.ColorIndex→ℂ := fun x i=> if a=(x,i) then k else 0
lemma rel_piece (a:Loc G 1) (s:Site c) : relay s a= axes (pew s (uno a 1))+Complex.I • axes (pew s (uno a (-Complex.I))) := by
  funext ⟨b,d,i⟩; by_cases h:a=(d,i)
  · change cell s b * (Pi.single a (1:ℂ): Loc G 1 → ℂ) (d,i)=(↑((cell _ _* _).re):ℂ)+Complex.I*(↑((cell _ _* _).re):ℂ)
    subst a; rw [Pi.single_eq_same]; simp [uno, Complex.ext_iff]
  change cell s b * (Pi.single a (1:ℂ): Loc G 1 → ℂ) (d,i)=(↑((cell _ _* _).re):ℂ)+Complex.I*(↑((cell _ _* _).re):ℂ); simp only [Pi.single_eq_of_ne (Ne.symm h),uno,if_neg h,mul_zero, Complex.zero_re, Complex.ofReal_zero, add_zero]
private lemma uno_charge (a:Loc G 1) (b:ℂ)(h:‖b‖≤1) (i j):‖uno a b i j‖≤1:= by unfold uno; split <;> first|exact h|simp

lemma priced_wave {A B : Link G c→ℝ} {ε:ℝ} (hε:0≤ε) (h:∀ (p q: Site c)(u v:TypeFace 1 → G.ColorIndex→ℂ),(∀ i j, ‖u i j‖ ≤ 1) → (∀ i j, ‖v i j‖≤1) →
  ‖iteratedFDeriv ℝ 2 A 0 ![pew p u,pew q v]-iteratedFDeriv ℝ 2 B 0 ![pew p u,pew q v]‖ ≤ ε) : aperture (4*ε) B A 1 := by
  let K:=noteAt A 2 - noteAt B 2
  have hi p q (u v: W)(hu : ∀ i j, ‖u i j‖≤1) (hv : ∀ i j, ‖v i j‖≤1) : ‖K ![axes (pew p u),axes (pew q v)]‖≤ε := by
    let x:=pew (G:=G) p u; let y:=pew q v
    have hs (Q : Link G c→ℝ) : noteAt Q 2 ![axes x,axes y] = (1/2:ℂ)* (↑(iteratedFDeriv ℝ 2 Q 0 ![x,y]):ℂ) := by
      rw [show ![axes x,axes y]=axes ∘ ![x,y] from funext (fun i=>by fin_cases i <;> rfl),note_real, Tensor.coeff]; norm_num [Nat.factorial]
    rw [show K _=noteAt A 2 ![axes x,axes y]-noteAt B 2 ![axes x,axes y] from rfl, hs,hs,← mul_sub,norm_mul, ← Complex.ofReal_sub,Complex.norm_real]; apply (mul_le_mul_of_nonneg_left (h p q u v hu hv) (norm_nonneg _)).trans; nlinarith [show ‖(1/2:ℂ)‖≤1 by norm_num]
  intro p i b g; let x:Loc G 1:= (b 0,i 0); let y:Loc G 1:= (b 1,i 1); let a:=p 0; let z:=p 1
  let u (w:Site c) (a:Loc G 1) := axes (pew (G:=G) w (uno a 1)); let v (w:Site c) (a:Loc G 1):=Complex.I • axes (pew w (uno a (-Complex.I)))
  rw [norm_sub_rev]; change ‖K g‖ ≤ _
  have hL : g=![relay a x,relay z y] := funext fun i=>by fin_cases i <;> rfl
  rw [hL,rel_piece,rel_piece]; let r:=u a x; let s:=u z y; let t:=v a x; let w:=v z y
  change ‖K ![r+t,s+w]‖≤_
  have he (r s : Phase (Lines G c 1)): K ![r,s]= K.curryLeft r ![s] := by rw [MultilinearMap.curryLeft_apply]; rfl
  simp_rw [he,map_add];
  have hT (f:Phase (Lines G c 1))(s t) : K.curryLeft f ![s+t]=K.curryLeft f ![s]+K.curryLeft f ![t] := by
    have h0 (z:Phase (Lines G c 1)) : Function.update (fun _ : Fin 1=>s) 0 z=![z] := by funext j; fin_cases j; simp
    simpa only [h0] using (K.curryLeft f).map_update_add (i:=0) (m:=fun _=>s) s t
  rw [_root_.add_apply,hT,hT];
  have h₁ := fun b : Loc G 1=>uno_charge b 1 (by norm_num)
  have h₂ := fun b : Loc G 1=>uno_charge b (-Complex.I) (by simp)
  have hm : ‖K.curryLeft r ![s]‖ ≤ ε := he r s ▸ hi _ _ _ _ (h₁ x) (h₁ y)
  have ht (f : Phase (Lines G c 1)) (s) : ‖K.curryLeft f ![Complex.I • s]‖= ‖K.curryLeft f ![s]‖ := by
    rw [show ![Complex.I • s]=fun i:Fin 1=>Complex.I • ![s] i from funext fun i=>by fin_cases i ; rfl, (K.curryLeft f).map_smul_univ (fun _=>Complex.I),norm_smul]; simp
  have hp f : ‖K.curryLeft t f‖=‖K.curryLeft (axes (pew a (uno x (-Complex.I)))) f‖ := by
    unfold t v; rw [map_smul, _root_.smul_apply, norm_smul]; simp
  let a':= axes (pew a (uno x (-Complex.I))); let z':= axes (pew z (uno y (-Complex.I)))
  have hr' : ‖K.curryLeft t ![s]‖≤ ε := (hp _).trans_le ( (he a' s) ▸ hi _ _ _ _ (h₂ x) (h₁ y))
  have hw' : ‖K.curryLeft r ![w]‖≤ ε := (ht r z').trans_le ((he r z') ▸ hi _ _ _ _ (h₁ x) (h₂ y))
  have hD: ‖K.curryLeft t ![w]‖ ≤ ε := (hp _).trans_le ((ht a' z').trans_le ((he a' z') ▸ hi _ _ _ _ (h₂ x) (h₂ y)))
  apply (norm_add_le ..).trans ((add_le_add (norm_add_le ..) (norm_add_le ..)).trans ((add_le_add (add_le_add hm hw') (add_le_add hr' hD)).trans_eq ?_)); ring
end YM.RG08.Canon
