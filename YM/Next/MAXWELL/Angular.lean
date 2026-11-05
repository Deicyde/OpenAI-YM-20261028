import YM.Next.MAXWELL.Affine
import YM.Work.A13


/-!
# Angular action of the same stress on shell jets

Use the one-parameter group in `Ortho`. The Lie row on polynomials will
read this operator on each leg.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
-- protect from extra imports name collisions
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Gauge} {j : ℕ}

lemma D_axes (f : E4 → F) (x u : E4) :
    (∑ i : Axis, u i • grad i f x) = D u f x := by
  unfold grad D; simp_rw [← map_smul (fderiv ℝ f x),← map_sum]
  congr 1
  ext1 i; simp

/-- Acting on the jet by inverse rotation, as used when reading the
transformed *field label*. -/
lemma rot_point (u : Ortho.Skew) (A : Solution F j) (a b : Axis) (x : E4) :
    HasDerivAt (fun t => asWave (solutionTurn (Ortho.oneParameter u t)⁻¹ A) a b x)
      (variation (fromCenter u.val 0) (asWave A) a b x) 0 := by
  let U : ℝ → Ortho := Ortho.oneParameter u
  let f := asWave A
  have hz : U 0 = 1 := YM.Work.A13.oneParameter_zero _
  have he (x : E4) : HasDerivAt (fun t => Ortho.move (U t) x) (M4.move u.val x) 0 := by
    have h := YM.Work.A13.hasDerivAt_move u x 0
    change HasDerivAt _ (M4.move u.val (Ortho.move (U 0) x)) _ at h
    rw [hz, Ortho.move_one] at h; exact h
  have hv : Ortho.move (U 0) x = x := by rw [hz,Ortho.move_one]
  have hk (a b : Axis) : HasDerivAt (fun t => (U t).val a b) (u.val a b) (0:ℝ) := by
    have ht := (EuclideanSpace.proj (𝕜:=ℝ) a).hasFDerivAt.comp_hasDerivAt 0 (he (basis b))
    simpa [Function.comp_def, Ortho.move] using ht
  let L := M4.move u.val x
  let C (i l : Axis) (t : ℝ) := (U t).val i a * (U t).val l b
  have hs (i l : Axis) : HasDerivAt (fun t => f i l (Ortho.move (U t) x)) (D L (f i l) x) (0:ℝ) := by
    have H := ((((wavePoly A).smooth i l (Ortho.move (U 0) x) (mem_univ _)).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 (he x)
    simp only [hv] at H; exact H
  have hd (i l : Axis) : HasDerivAt (fun t => C i l t • f i l (Ortho.move (U t) x))
      (((1:M4) i a * (1:M4) l b) • D L (f i l) x + (u.val i a * (1:M4) l b +
        (1:M4) i a * u.val l b) • f i l x) (0 : ℝ) := by
    have h := ((hk i a).fun_mul (hk l b)).smul (hs i l)
    simp only [hz, Ortho.move_one] at h
    exact h
  simp_rw [rot_wave, fieldTurn,inv_entry,inv_inv];
  refine (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ) fun l _ => hd i l)).congr_deriv ?_
  rw [variation_value (skew_K _ _) (wave_closed (wavePoly A)) isOpen_univ (mem_univ _)]
  simp only [center_grad,Finset.sum_add_distrib, add_smul]
  rw [show (∑ i : Axis, fromCenter u.val 0 i x • grad i (asWave A a b) x)=D L (f a b) x from ?_]
  · simp [Matrix.one_apply, ite_mul, mul_ite, ite_smul, add_assoc,f]
  simpa only [fromCenter,sub_zero] using D_axes (f a b) x L

def asWaveL (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (a b : Axis) (x : E4) :
    Solution F j →ₗ[ℝ] F where
  toFun A := asWave A a b x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Lie
variable [FiniteDimensional ℝ F]

lemma turn_derivable (u : Ortho.Skew) (A : Solution F j) (L : Module.Dual ℝ (Solution F j)) :
    DifferentiableAt ℝ (fun t => L (solutionTurn (Ortho.oneParameter u t)⁻¹ A)) 0 := by
  let Φ := fun t => solutionTurn (Ortho.oneParameter u t)⁻¹ A
  let s := {L : Module.Dual ℝ (Solution F j) | DifferentiableAt ℝ (L ∘ Φ) 0}
  let V : Submodule ℝ (Module.Dual ℝ (Solution F j)) :=
    { carrier := s, zero_mem' := by
        change DifferentiableAt ℝ (fun _ => (0:ℝ)) _; exact differentiableAt_const _
      add_mem' := by intro x y (hx : DifferentiableAt ℝ _ _) (hy : DifferentiableAt ℝ _ _); exact hx.add hy
      smul_mem' := by intro a x (hx : DifferentiableAt ℝ _ _); exact hx.const_mul a }
  have ht (a b : Axis) (x : E4) (L : Module.Dual ℝ F) : L.comp (asWaveL F j a b x) ∈ V := by
    have he := L.toContinuousLinearMap.differentiableAt (x := asWave (Φ 0) a b x) |>.comp (0:ℝ)
      (rot_point u A a b x).differentiableAt
    exact he
  let B := Module.finBasis ℝ F
  have he : V.dualCoannihilator=⊥ := by
    apply le_antisymm _ bot_le; intro y hy
    apply (Submodule.mem_bot ..).mpr; apply asWave_inj; funext a b x
    change asWave y a b x=0
    apply B.equivFun.injective; rw [map_zero]; exact funext fun i =>
      (Submodule.mem_dualCoannihilator _).1 hy _ (ht a b x (B.coord i))
  have hp : V=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq V
    rw [he, finrank_bot,add_zero] at h
    rw [h, Subspace.dual_finrank_eq]
  exact (show L ∈ V from hp ▸ Submodule.mem_top)

def derivativeTurn (u : Ortho.Skew) (A : Solution F j) :=
  let B := Module.finBasis ℝ (Solution F j)
  ∑ i, deriv (fun t => B.coord i (solutionTurn (Ortho.oneParameter u t)⁻¹ A)) 0 • B i

lemma turn_has (u : Ortho.Skew) (A : Solution F j) (L : Module.Dual ℝ (Solution F j)) :
    HasDerivAt (fun t => L (solutionTurn (Ortho.oneParameter u t)⁻¹ A)) (L (derivativeTurn u A)) 0 := by
  let B := Module.finBasis ℝ (Solution F j)
  let a := fun t => solutionTurn (Ortho.oneParameter u t)⁻¹ A
  have ht : (fun t => L (a t)) = fun t => ∑ i, (B.coord i (a t)) • L (B i) := funext fun t => by
    simp_rw [← map_smul L, ← map_sum]; exact congr_arg L (B.sum_repr (a t)).symm
  change HasDerivAt (fun t => L (a t)) (L (∑ i, deriv (fun t => B.coord i (a t)) 0 • B i)) 0
  rw [ht,map_sum]; simp_rw [map_smul]
  apply HasDerivAt.fun_sum; intro i _
  exact ((turn_derivable u A (B.coord i)).hasDerivAt).mul_const _

lemma differential_rigid (u : Ortho.Skew) (A : Solution F j) :
    asWave (derivativeTurn u A) = variation (fromCenter u.val 0) (asWave A) := by
  funext a b x
  let B := Module.finBasis ℝ F
  apply B.equivFun.injective; funext i
  let L := (B.coord i).toContinuousLinearMap
  have ht : HasDerivAt (fun t => L (asWave (solutionTurn (Ortho.oneParameter u t)⁻¹ A) a b x))
      (L (variation (fromCenter u.val 0) (asWave A) a b x)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (rot_point u A a b x)
  exact (turn_has u A ((B.coord i).comp (asWaveL F j a b x))).unique ht

def infJet (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (j : ℕ) :
    Ortho.Skew →ₗ[ℝ] (Solution F j →ₗ[ℝ] Solution F j) where
  toFun u :=
    { toFun := derivativeTurn u
      map_add' A B := by
        apply (Module.finBasis ℝ (Solution F j)).equivFun.injective; funext i
        let L := (Module.finBasis ℝ (Solution F j)).coord i
        change L (derivativeTurn u (A+B))=L (derivativeTurn u A+derivativeTurn u B)
        rw [map_add]
        refine (turn_has u (A+B) L).unique ?_
        simp_rw [map_add]; exact (turn_has u A L).add (turn_has u B L)
      map_smul' a A := by
        apply (Module.finBasis ℝ (Solution F j)).equivFun.injective; funext i
        let L := (Module.finBasis ℝ (Solution F j)).coord i
        change L (derivativeTurn u (a • A))=L (a • derivativeTurn u A)
        rw [map_smul]
        refine (turn_has u (a • A) L).unique ?_
        simp_rw [map_smul]; exact (turn_has u A L).const_mul _ }
  map_add' u w := by
    ext1 A
    change derivativeTurn (u+w) A = derivativeTurn u A + derivativeTurn w A
    apply asWave_inj; funext a b x
    rw [show asWave (derivativeTurn u A + derivativeTurn w A) a b x=_ from (asWaveL F j a b x).map_add _ _]
    change asWave (derivativeTurn (u+w) A) a b x = asWave (derivativeTurn u A) a b x + asWave (derivativeTurn w A) a b x
    simp only [differential_rigid]
    simp_rw [variation_value (skew_K _ _) (wave_closed (wavePoly A)) isOpen_univ (mem_univ _), center_grad,fromCenter,
      M4.at_coord]; simp [add_mul, Finset.sum_add_distrib,add_smul]; abel
  map_smul' t u := by
    ext1 A
    change derivativeTurn (t • u) A = t • derivativeTurn u A
    apply asWave_inj; funext a b x
    change asWave (derivativeTurn (t • u) A) a b x = t • asWave (derivativeTurn u A) a b x
    simp only [differential_rigid];
    simp_rw [variation_value (skew_K _ _) (wave_closed (wavePoly A)) isOpen_univ (mem_univ _), center_grad,fromCenter,M4.at_coord]
    simp only [SetLike.val_smul,Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, Finset.smul_sum,smul_add,mul_smul]
end Lie

/-- Infinitesimal of actual rotated probe. -/
def angularLeg (G : Gauge) (j : ℕ) : Ortho.Skew →ₗ[ℝ] Module.End ℝ (Probe G j) where
  toFun u :=
    { toFun p := p.comp (infJet G.Color j u)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_add' u w := by
    ext1 p; ext x
    change p (infJet G.Color j (u+w) x)=p (infJet G.Color j u x)+p (infJet G.Color j w x)
    rw [map_add,LinearMap.add_apply,map_add]
  map_smul' t u := by
    ext1 p; ext x
    change p (infJet G.Color j (t • u) x)=t • p (infJet G.Color j u x)
    rw [map_smul, LinearMap.smul_apply,map_smul]

lemma rotate_test (u : Ortho.Skew) (p : Probe G j) (A : Shell G j) :
    HasDerivAt (fun t => probeTurn (Ortho.oneParameter u t) p A) (angularLeg G j u p A) 0 :=
  turn_has u A p

lemma angular_flux {x : E4} {U} {f : Field G.Color} (hU : IsOpen U) (H : WaveOn U f) (p : Probe G j)
    (u : Ortho.Skew) {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (hx : χ =ᶠ[𝓝 x] fun _ => 1) :
    singleFlux (fromCenter u.val x) χ (pulse p x) f = -sample (angularLeg G j u p) f x := by
  let v := fromCenter u.val x
  have he := affine_wave (skew_K u x) u.val (center_grad u.val x) hU H
  have hw := hs (enclosed _ hx)
  rw [jet_force hU H (skew_K u x) hχ Hχ hs hx he p]
  rw [sample_eval _ he hU hw,sample_eval _ H hU hw]
  congr 1
  apply congr_arg p; apply Subtype.ext
  let B : Shell G j := ⟨nth f j x,H.jets hU hw⟩
  change nth (variation v f) j x = (derivativeTurn u B).val
  exact (variation_center _ _ (skew_K u x) (skew_K u 0) H hU hw (j:=j)).trans
    (show nth (variation (fromCenter u.val 0) (asWave B)) j 0 = _ from differential_rigid u B ▸ asWave_jet _)

end YM.Maxwell.Free
