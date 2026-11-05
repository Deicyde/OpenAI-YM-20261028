import YM.Analysis.SmoothJets
import YM.Bid.Source

/-!
# Splitting the finite sampler linearization (G04)

Use the invariant inner product already available on colours. We temporarily transport
**linear algebra** on GaugePanel to PiLp 2; all analytic statements and differentiation
of `bring` use the original spaces. No Haar averaging/continuity of an action in the
*group variable* is needed for this method.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.G04
open Labels Source Drops Bid RG
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {d m : ℕ}

/-- Split an injective equivariant linear map using the inner product on the target.
    For equivariance of the splitting we use the isometries and invariance of the range
    (in both directions). The action on the source need not be given by isometries. -/
private theorem splitRange {I X Y : Type*} [Group I] [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (T : X →ₗ[ℝ] Y) (S : I → X → X) (R : I → Y →ₗᵢ[ℝ] Y)
    (hr : ∀ u y, R u (R u⁻¹ y) = y) (ht : ∀ u x, T (S u x) = R u (T x))
    (hi : Function.Injective T) :
    ∃ C : Y →ₗ[ℝ] X, (∀ x, C (T x) = x) ∧ ∀ u y, C (R u y) = S u (C y) := by
  let M := LinearMap.range T
  let e : X ≃ₗ[ℝ] M := LinearEquiv.ofInjective T hi
  have hm (u : I) (y : Y) (hy : y ∈ M) : R u y ∈ M := by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨S u x, ht u x⟩
  have stable (u : I) : M.map (R u).toLinearMap = M := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      exact hm u x hx
    · intro y hy
      exact Submodule.mem_map.mpr ⟨R u⁻¹ y, hm u⁻¹ y hy, hr u y⟩
  have comm (u : I) (y : Y) : R u (M.starProjection y) = M.starProjection (R u y) := by
    have h := (R u).map_starProjection M y
    exact h.trans (congrArg (fun N : Submodule ℝ Y => N.starProjection (R u y)) (stable u))
  let C := e.symm.toLinearMap.comp M.orthogonalProjectionOnto.toLinearMap
  have hc (y : Y) : T (C y) = M.starProjection y := by
    have he (x : X) : (e x).val = T x := LinearEquiv.ofInjective_apply T x
    rw [← he]
    change ((e (e.symm _)).val : Y) = _
    rw [e.apply_symm_apply]; rfl
  refine ⟨C, ?_, ?_⟩
  · intro x
    apply hi
    rw [hc]
    exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  · intro u y
    apply hi
    rw [ht, hc, hc, comm]

private def castL (u : G.El) : Snap G d →L[ℝ] Snap G d where
  toFun := Cast u
  map_add' := fun _ _ => funext fun _ => map_add _ _ _
  map_smul' := fun c x => funext fun i => map_smul (Taylor.paint u) c (x i)
  cont := Cast_cont

private def rotatesL (u : G.El) : GaugePanel G m →L[ℝ] GaugePanel G m where
  toFun := rotates u
  map_add' := fun _ _ => funext fun _ => map_add _ _ _
  map_smul' := fun c x => funext fun i => map_smul (G.adjoint u) c (x i)
  cont := rotates_cont

private abbrev PanelL2 (G : Gauge) (m : ℕ) := PiLp 2 (fun _ : Fin m => G.Color)

private def transport : GaugePanel G m ≃ₗ[ℝ] PanelL2 G m :=
  (WithLp.linearEquiv 2 ℝ (GaugePanel G m)).symm

private def rotateIso (u : G.El) : PanelL2 G m →ₗᵢ[ℝ] PanelL2 G m where
  toLinearMap := transport.toLinearMap.comp ((rotatesL u).toLinearMap.comp transport.symm.toLinearMap)
  norm_map' y := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    change Real.sqrt (∑ i, ‖G.adjoint u (y i)‖ ^ 2) = Real.sqrt (∑ i, ‖y i‖ ^ 2)
    simp only [G.norm_adjoint]

private lemma rotateIso_inv (u : G.El) (y : PanelL2 G m) :
    rotateIso u (rotateIso u⁻¹ y) = y := by
  apply PiLp.ext
  intro i
  change G.adjoint u (G.adjoint u⁻¹ (y i)) = y i
  rw [← G.adjoint_mul, mul_inv_cancel, G.adjoint_one]

private lemma deriv_comm (H : Hol G) (B : Fin m → Slot) (hp : Peg H d)
    (hd : DifferentiableAt ℝ (bring H d B) 0) (u : G.El) (x : Snap G d) :
    fderiv ℝ (bring H d B) 0 (Cast u x) = rotates u (fderiv ℝ (bring H d B) 0 x) := by
  let F := bring H d B
  let D := fderiv ℝ F 0
  let P : Snap G d →L[ℝ] Snap G d := castL u
  let Q : GaugePanel G m →L[ℝ] GaugePanel G m := rotatesL u
  have ha : HasFDerivAt F D (P 0) := by rw [map_zero]; exact hd.hasFDerivAt
  have ha' : HasFDerivAt (F ∘ P) (D.comp P) 0 := ha.comp 0 P.hasFDerivAt
  have hb : HasFDerivAt (Q ∘ F) (Q.comp D) 0 := Q.hasFDerivAt.comp 0 hd.hasFDerivAt
  have eqn : F ∘ P = Q ∘ F := funext fun a => funext fun i => hp.observes (B i) u a
  rw [eqn] at ha'
  change D.comp P x = Q.comp D x
  rw [ha'.unique hb]

private lemma deriv_inj (H : Hol G) (B : Fin m → Slot) (hl : lifts H d m B)
    (hd : DifferentiableAt ℝ (bring H d B) 0) :
    Function.Injective (fderiv ℝ (bring H d B) 0) := by
  intro x y hxy
  let D := fderiv ℝ (bring H d B) 0
  change D x = D y at hxy
  have h : D (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  apply hl
  intro i
  change fderiv ℝ (fun a => bring H d B a i) 0 (x-y) = _
  rw [fderiv_apply hd i]
  change D (x-y) i = 0
  rw [h]; rfl

theorem answer : YM.Bid.G04 := by
  intro G H d m B hp hl
  have ha : AnalyticAt ℝ (bring H d B) 0 := AnalyticAt.pi fun i => hp.shot (B i)
  have hd := ha.differentiableAt
  refine ⟨ha, ?_⟩
  let D := fderiv ℝ (bring H d B) 0
  let L : GaugePanel G m ≃ₗ[ℝ] PanelL2 G m := transport
  let T := L.toLinearMap.comp D.toLinearMap
  have commute (u : G.El) (y : GaugePanel G m) : L (rotates u y) = rotateIso u (L y) := rfl
  have ht (u : G.El) (x : Snap G d) : T (Cast u x) = rotateIso u (T x) := by
    change L (fderiv ℝ (bring H d B) 0 (Cast u x)) = rotateIso u (L (D x))
    rw [deriv_comm H B hp hd u x]
    exact commute u (D x)
  have hi : Function.Injective T := L.injective.comp (deriv_inj H B hl hd)
  obtain ⟨C, hc, he⟩ := splitRange T (Cast (G:=G)) rotateIso rotateIso_inv ht hi
  refine ⟨C.comp L.toLinearMap, fun x => hc x, ?_⟩
  intro u y
  change C (L (rotates u y)) = Cast u (C (L y))
  rw [commute, he]

end YM.Work.G04
