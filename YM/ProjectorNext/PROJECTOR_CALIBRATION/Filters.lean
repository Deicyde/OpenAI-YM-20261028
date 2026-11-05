import YM.Next.FOUNDATIONS.SU2
import YM.Next.SCHEDULE.Batch
import YM.Next.SCHEDULE.Markets
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Force

/-!
# Fixed finite filters for radial and off-shell response

Recover each equation leg (normal to shell) up to higher-weight
contributions. Split finite color read panels equivariantly. Everything over
the real Lie geometry here; complexify only the cylinder with the
coefficients. Don't ask that a fixed number of samples work simultaneously
for unbounded d. No Woke, thresholds or schedules enter the choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Maxwell Work Function Filter Tensor Analysis
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge}

section Panel
variable {I : Type*} [Fintype I]

private abbrev Panel (G : Gauge) (I : Type*) [Fintype I] := PiLp 2 fun _ : I => G.Color
private def toPanel : (I → G.Color) ≃ₗ[ℝ] Panel G I := (WithLp.linearEquiv 2 ℝ (I → G.Color)).symm

def colorAction (u : G.El) : Module.End ℝ (I → G.Color) := LinearMap.pi fun i => (G.adjoint u).comp (LinearMap.proj i)
private def panelAct (u : G.El) : Panel G I →ₗᵢ[ℝ] Panel G I where
  toLinearMap := toPanel.toLinearMap.comp ((colorAction u).comp toPanel.symm.toLinearMap)
  norm_map' y := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    change Real.sqrt (∑ i, ‖G.adjoint u (y i)‖^2) = Real.sqrt (∑ i, ‖y i‖^2)
    simp only [G.norm_adjoint]

private lemma panelInv (u : G.El) (y : Panel G I) : panelAct u (panelAct u⁻¹ y)=y := by
  apply PiLp.ext; intro i; change G.adjoint u (G.adjoint u⁻¹ (y i))=y i
  rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]

private lemma naturalProjection (U : Submodule ℝ (Panel G I))
    (h : ∀ (u : G.El) (y : Panel G I), y ∈ U → panelAct u y ∈ U) (u : G.El) (y : Panel G I) :
    panelAct u (U.starProjection y) = U.starProjection (panelAct u y) := by
  have hv : U.map (panelAct u).toLinearMap = U := by
    apply le_antisymm
    · rintro z h'
      obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp h'; exact h u x hx
    intro z h'
    exact Submodule.mem_map.mpr ⟨panelAct u⁻¹ z,h u⁻¹ z h',panelInv u z⟩
  exact ((panelAct u).map_starProjection U y).trans (congrArg (fun V : Submodule ℝ (Panel G I) => V.starProjection (panelAct u y)) hv)

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Transport a stable-space projection on X from an equivariant embedding
into finitely many colors. -/
lemma panelProjection (T : X →ₗ[ℝ] I → G.Color) (S : G.El → Module.End ℝ X) (V : Submodule ℝ X)
    (hV : ∀ u (x : X), x∈V → S u x∈V) (ht : ∀ u x, T (S u x)=colorAction u (T x)) (hi : Injective T) :
    ∃ Q : Module.End ℝ X, (∀ x, Q x∈V) ∧ (∀ x∈V, Q x=x) ∧ ∀ u x, Q (S u x)=S u (Q x) := by
  let L : X →ₗ[ℝ] Panel G I := toPanel.toLinearMap.comp T
  have he : Injective L := toPanel.injective.comp hi
  have ha (u x) : L (S u x) = panelAct u (L x) := congrArg (toPanel (I:=I)) (ht u x)
  let U := V.map L
  have hu : U ≤ LinearMap.range L := fun x hx => by obtain ⟨a,-,rfl⟩ := Submodule.mem_map.mp hx; exact LinearMap.mem_range.mpr ⟨_,rfl⟩
  have hcov (u : G.El) (y) (hy : y∈U) : panelAct u y∈U := by
    obtain ⟨a,hx,rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨S u a,hV u a hx,ha u a⟩
  let e := LinearEquiv.ofInjective L he
  let Q := e.symm.toLinearMap.comp ((Submodule.inclusion hu).comp (U.orthogonalProjectionOnto.toLinearMap.comp L))
  have h (x) : L (Q x) = U.starProjection (L x) := by
    change L (e.symm _) = _; rw [← LinearEquiv.ofInjective_apply L (h:=he)]; exact congr_arg Subtype.val (e.apply_symm_apply _)
  refine ⟨Q,fun x => ?_,fun x hx => he ?_,fun u x => he ?_⟩
  · have hp : L (Q x) ∈ U := by rw [h,← U.coe_orthogonalProjectionOnto_apply]; exact Subtype.prop _
    obtain ⟨a,hx,hz⟩ := Submodule.mem_map.mp hp; exact he hz ▸ hx
  · rw [h]; exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_map_of_mem hx)
  rw [ha, h,h,ha,naturalProjection U hcov]

/-- Reconstruct equivariant Y values that factor through color samples on X,
even when X-to-samples hasn't full rank. -/
lemma panelFilter (T : X →ₗ[ℝ] I → G.Color) (N : X →ₗ[ℝ] Y) (hN : LinearMap.ker T ≤ LinearMap.ker N)
    (S : G.El → Module.End ℝ X) (R : G.El → Module.End ℝ Y)
    (ht : ∀ u x, T (S u x)=colorAction u (T x)) (hr : ∀ u x, N (S u x)=R u (N x)) :
    ∃ C : (I → G.Color) →ₗ[ℝ] Y, (∀ x, C (T x)=N x) ∧ ∀ u x, C (colorAction u x)= R u (C x) := by
  let L : X →ₗ[ℝ] Panel G I := toPanel.toLinearMap.comp T
  have hL : LinearMap.ker L ≤ LinearMap.ker N := fun x hx => hN (show T x = 0 from toPanel.injective ((show toPanel (T x) = 0 from hx).trans (toPanel.map_zero).symm))
  have ha (u x) : L (S u x) = panelAct u (L x) := congrArg (toPanel (I:=I)) (ht u x)
  let U := LinearMap.range L
  have hcov (u : G.El) (y) (hy : y∈U) : panelAct u y∈U := by
    obtain ⟨a,rfl⟩ := LinearMap.mem_range.mp hy; exact LinearMap.mem_range.mpr ⟨S u a,ha u a⟩
  let M := ((LinearMap.ker L).liftQ N hL).comp L.quotKerEquivRange.symm.toLinearMap
  let C := M.comp (U.orthogonalProjectionOnto.toLinearMap.comp toPanel.toLinearMap)
  have he (x : I → G.Color) (y : X) (hy : L y=U.starProjection (toPanel x)) : C x = N y := by
    let z := U.orthogonalProjectionOnto (toPanel x)
    have hf : L y ∈ U := LinearMap.mem_range_self _ _
    have hz : z = ⟨L y,hf⟩ := Subtype.ext hy.symm
    change (L.ker.liftQ N hL) (L.quotKerEquivRange.symm z) = _
    rw [hz, L.quotKerEquivRange_symm_apply_image]; exact Submodule.liftQ_apply ..
  refine ⟨C,fun x => he _ _ ?_,fun u x => ?_⟩
  · exact Eq.symm (Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self L x))
  have hp : U.starProjection (toPanel x) ∈ U := by rw [← U.coe_orthogonalProjectionOnto_apply]; exact Subtype.prop _
  obtain ⟨y,hy⟩ := LinearMap.mem_range.mp hp
  rw [he x y hy, he _ (S u y), hr]
  change L _=U.starProjection (panelAct u (toPanel x)); rw [ha,hy,naturalProjection U hcov]
end Panel

variable {d : ℕ}

def castAction (u : G.El) : Module.End ℝ (Snap G d) := LinearMap.pi fun i => (Taylor.paint u).comp (LinearMap.proj i)

private def castC (u : G.El) : Snap G d →L[ℝ] Snap G d := LinearMap.toContinuousLinearMap (castAction u)

lemma linearSample_natural (H : Hol G) (x : Position) (u : G.El) (A : Snap G d) :
    linearSample H d x (Cast u A) = G.adjoint u (linearSample H d x A) := by
  let F (A : Snap G d) := sample (native H d A) x
  have hf : DifferentiableAt ℝ F 0 := (sample_smooth H x (d:=d)).differentiableAt (by simp)
  let L := G.adjoint u |>.toContinuousLinearMap
  let P := castC u (d:=d)
  have he : F ∘ P = L ∘ F := by
    funext J
    have hx : expand d (Cast u J) = colored u (expand d J) := by
      funext i; unfold expand colored; split <;> rename_i h <;> simp [h]; rfl
    change sample (native H d (Cast u J)) x = _
    unfold native; rw [hx,G01.links_colored,sample_gauge]; rfl
  have hD := L.hasFDerivAt.comp (0:Snap G d) hf.hasFDerivAt
  rw [← he] at hD
  have hP : HasFDerivAt F (fderiv ℝ F 0) (P 0) := by rw [map_zero]; exact hf.hasFDerivAt
  have hh := (hP.comp (0:Snap G d) P.hasFDerivAt).unique hD
  exact DFunLike.congr_fun hh A

/-- Curvature panel already paid for the section in G03/04. -/
structure Windows (H : Hol G) (d : ℕ) where
  m : ℕ
  loops : Fin m → RG.Slot
  smooth : AnalyticAt ℝ (bring H d loops) 0
  recover : GaugePanel G m →ₗ[ℝ] Snap G d
  lift_radial (A : Snap G d) : recover (fderiv ℝ (bring H d loops) 0 A) = A
  intertwine (u : G.El) (A : GaugePanel G m) : recover (colorAction u A) = Cast u (recover A)

def windows (H : Hol G) (d : ℕ) : Windows H d := by
  let hp := G02.answer G01.answer G H d
  let hh := G03.answer G H d hp
  let h := hh.choose_spec
  let B := h.choose
  let E := G04.answer G H d _ B hp h.choose_spec
  exact ⟨_,B,E.smooth,E.detects.choose,E.detects.choose_spec.1,E.detects.choose_spec.2⟩

namespace Windows
variable {H : Hol G} (W : Windows H d)

def seed := fderiv ℝ (bring H d W.loops) 0

set_option maxHeartbeats 400000 in
lemma seed_natural (u : G.El) (A : Snap G d) : W.seed (Cast u A) = colorAction u (W.seed A) := by
  let P := castC u (d:=d)
  let F := bring H d W.loops
  let Q := LinearMap.toContinuousLinearMap (colorAction u (I:=Fin W.m))
  have he : F ∘ P = Q ∘ F := by
    funext J i
    exact (G01.answer G H).2 _ _ u _
  have hf : HasFDerivAt F W.seed (P 0) := by rw [map_zero]; exact W.smooth.differentiableAt.hasFDerivAt
  have hw := hf.comp (0:Snap G d) P.hasFDerivAt
  rw [he] at hw
  exact DFunLike.congr_fun (hw.unique (Q.hasFDerivAt.comp _ W.smooth.differentiableAt.hasFDerivAt)) A
end Windows

abbrev Level (d : ℕ) := Fin (d-1)

def firing (k : Level d) : Taylor G k.val →ₗ[ℝ] Snap G d := LinearMap.single ℝ (fun l : Fin (d-1) => Taylor G l.val) k

lemma firing_natural (k : Level d) (u : G.El) (x : Taylor G k.val) :
    firing k (Taylor.paint u x) = Cast u (firing k x) := by
  funext i; by_cases hi : i=k
  · subst i; simp [firing,Cast]
  simp [firing,Cast,Pi.single_eq_of_ne hi]

/-- Pull back the shell degree by degree. -/
def shellPart (G : Gauge) (j : ℕ) : Submodule ℝ (Taylor G j) :=
    (onShell G.Color j).comap ((Maxwell.formSpace j G.Color).subtype.comp Maxwell.potential.toLinearMap)

theorem shell_iff {k : ℕ} (A : Taylor G k) : A∈shellPart G k ↔ takeCurl A ∈ onShell G.Color k := Iff.rfl

lemma shell_natural (k : ℕ) (u : G.El) (x : Taylor G k) (hx : x∈shellPart G k) :
    Taylor.paint u x ∈ shellPart G k := by
  change takeCurl (Taylor.paint u x) ∈ onShell G.Color k
  change takeCurl x ∈ onShell G.Color k at hx
  refine ⟨closedCurl _,fun b y => ?_⟩
  let L := (G.adjoint u).toContinuousLinearMap
  have he (a : Axis) : Tensor.diagonal (takeCurl (Taylor.paint u x) a b) = L ∘ Tensor.diagonal (takeCurl x a b) := by
    funext z
    simp only [Tensor.diagonal,takeCurl,smul_apply,sub_apply]
    symm; change G.adjoint u (((k+1:ℕ) : ℝ) • (_ - _)) = _
    rw [map_smul,map_sub]; rfl
  simp_rw [he, Maxwell.grad_linear L (diag_smooth _ ∞).contDiffAt, ← _root_.map_sum, hx.2 b y, map_zero]

structure Split (G : Gauge) (d : ℕ) where
  Q (k : Level d) : Module.End ℝ (Taylor G k.val)
  hits (k : Level d) (x) : Q k x ∈ shellPart G k.val
  fixes (k : Level d) (x) : x∈shellPart G k.val → Q k x=x
  natural (k : Level d) (u : G.El) (x) : Q k (Taylor.paint u x)=Taylor.paint u (Q k x)

def splitOf {H : Hol G} (W : Windows H d) : Split G d := by
  let T (i : Level d) := W.seed.toLinearMap.comp (firing (G:=G) i)
  have h (i : Level d) (u : G.El) (x : Taylor G i.val) : T i (Taylor.paint u x)=colorAction u (T i x) := by
    change W.seed (firing i (Taylor.paint u x))=_; rw [firing_natural,W.seed_natural]; rfl
  have he (i : Level d) : Injective (T i) := by
    intro a b hab
    have hu : W.seed (firing i a)= W.seed (firing i b) := hab
    have hs : firing i a=firing i b := by rw [← W.lift_radial (firing i a), ← W.lift_radial (firing i b)]; exact congr_arg _ hu
    simpa [firing] using! congr_fun hs i
  let P (i : Level d) := panelProjection (T i) (Taylor.paint (G:=G)) (shellPart G i.val) (shell_natural i.val) (h i) (he i)
  exact ⟨fun i => (P i).choose,fun i => (P i).choose_spec.1,fun i => (P i).choose_spec.2.1,fun i => (P i).choose_spec.2.2⟩
