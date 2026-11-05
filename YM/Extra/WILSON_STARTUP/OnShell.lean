import YM.Extra.WILSON_STARTUP.Comparable
import YM.Work.F04.Calculus
import YM.Work.F05.Calculus

/-!
# Stationary analytic jet transport across input changes

Use the genuinely nondegenerate vertical form. Matching actions on pairs
through degree k+1 gives implicit critical graphs through degree k, and via
the horizontal derivative still gives on-shell VALUE jets through k+1. These
are all germ assertions only, at analytic/canonical inputs as in `Critical`.
Each solve still needs the actual branch and stationary price gap at its
particular lattice arguments.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Function Filter Precision Work
open scoped ContDiff Topology
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F G : X × Y → ℝ} {u v : X → Y}

def graph (u : X → Y) (x : X) := (x,u x)
def arrow (F : X × Y → ℝ) (q : X × Y) := (q.1,vert F q)
abbrev horz (F : X × Y → ℝ) := fun q => fderiv ℝ F q ∘L ContinuousLinearMap.inl ℝ X Y

structure Station (F : X × Y → ℝ) (u : X → Y) : Prop where
  regular : ContDiffAt ℝ ω u 0
  starts : u 0=0
  law : vert F ∘ graph u =ᶠ[𝓝 0] 0

lemma Station.at0 (h : Station F u) : graph u 0 = 0 := Prod.ext rfl h.starts
lemma Station.home (h : Station F u) : Tendsto (graph u) (𝓝 0) (𝓝 0) :=
  tendsto_id.prodMk_nhds (h.starts ▸ h.regular.continuousAt.tendsto)
lemma Station.chart (h : Station F u) : ContDiffAt ℝ ω (graph u) 0 := contDiffAt_id.prodMk h.regular

lemma Station.horizontal (h : Station F u) (hf : ContDiffAt ℝ ω F 0) :
    fderiv ℝ (F ∘ graph u) =ᶠ[𝓝 0] horz F ∘ graph u := by
  filter_upwards [h.law,h.regular.eventually (by simp),h.home.eventually (hf.eventually (by simp))] with x hl hx hf
  have hxy : fderiv ℝ F (x,u x) ∘L ContinuousLinearMap.inr ℝ X Y = 0 :=
    (F04.hasFDerivAt_slice F x (u x) (hf.differentiableAt (by simp))).fderiv.symm.trans hl
  rw [((hf.differentiableAt (by simp)).hasFDerivAt.comp x (show HasFDerivAt (graph u) _ x from
    (hasFDerivAt_id x).prodMk (hx.differentiableAt (by simp)).hasFDerivAt)).fderiv]
  ext1 w
  change fderiv ℝ F (x,u x) (w,fderiv ℝ u x w) = fderiv ℝ F (x,u x) (w,(0:Y))
  rw [show (w,fderiv ℝ u x w)=(w,(0:Y))+(0,fderiv ℝ u x w) from by simp, map_add]
  exact add_eq_left.mpr (DFunLike.congr_fun hxy (fderiv ℝ u x w))

structure Definite (F : X × Y → ℝ) : Prop where
  smooth : ContDiffAt ℝ ω F 0
  pos : ∀ y : Y, F05.bend (fun y : Y => F (0,y)) 0 y y = 0 → y=0

lemma Definite.rate (h : Definite F) (y : Y) : fderiv ℝ (vert F) 0 (0,y) y = F05.bend (fun y => F ((0:X),y)) 0 y y := by
  let P := ContinuousLinearMap.inr ℝ X Y
  have hA := ((matches_self 1 h.smooth).diff_vert.left.differentiableAt (by simp)).hasFDerivAt
  have he : HasFDerivAt (vert F) (fderiv ℝ (vert F) 0) (P 0) := by rw [map_zero]; exact hA
  have hf : HasFDerivAt (fderiv ℝ fun y : Y => F ((0:X),y)) (_ ∘L P) 0 := he.comp (0:Y) P.hasFDerivAt
  simp only [F05.bend, ContinuousLinearMap.toLinearMap₁₂_apply,hf.fderiv]; rfl

lemma Definite.forms [FiniteDimensional ℝ Y] (h : Definite F) :
    (fderiv ℝ (vert F) 0 ∘L ContinuousLinearMap.inr ℝ X Y).IsInvertible := F04.form_invertible _ <|
  (injective_iff_map_eq_zero _).mpr fun x hx => h.pos x ((h.rate x).symm.trans (DFunLike.congr_fun hx x))

lemma Definite.equiv [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (h : Definite F) :
    ∃ U : (X × Y) ≃L[ℝ] X × (Y →L[ℝ] ℝ), HasFDerivAt (arrow F) (U : _ →L[ℝ] _) 0 := by
  let T := (ContinuousLinearMap.fst ℝ X Y).prod (fderiv ℝ (vert F) 0)
  have he : HasFDerivAt (arrow F) T 0 := hasFDerivAt_fst.prodMk
    ((matches_self 1 h.smooth).diff_vert.left.differentiableAt (by simp)).hasFDerivAt
  have hi : Injective T := (injective_iff_map_eq_zero _).mpr (fun ⟨x,y⟩ ht => by
    have he : x = 0 := congr_arg Prod.fst ht
    subst x
    rw [h.pos y ((h.rate y).symm.trans (DFunLike.congr_fun (congr_arg Prod.snd ht) y))]; rfl)
  have hn : Module.finrank ℝ (X × Y) = Module.finrank ℝ (X × (Y →L[ℝ] ℝ)) := by
    have he := (LinearMap.toContinuousLinearMap : (Y →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Y →L[ℝ] ℝ)).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, ← he, Module.finrank_linearMap_self]
  let U := (LinearEquiv.ofBijective T.toLinearMap ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hn).mp hi⟩).toContinuousLinearEquiv
  exact ⟨U,he⟩

theorem compare [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] {k : ℕ}
    (H : Matches (k+1) F G 0) (hF : Station F u) (hG : Station G v) (hQ : Definite F) : Matches k (graph u) (graph v) 0 ∧
    Matches (k+1) (F ∘ graph u) (G ∘ graph v) 0 := by
  haveI : CompleteSpace (X × Y) := FiniteDimensional.complete ℝ _
  let W := arrow F
  obtain ⟨U,hw⟩ := hQ.equiv
  have hj : Matches k W (arrow G) 0 := (matches_self k contDiffAt_fst).prod H.diff_vert
  let O := hj.left.toOpenPartialHomeomorph W hw (by simp)
  have hO : (0:X × Y) ∈ O.source := ContDiffAt.mem_toOpenPartialHomeomorph_source ..
  have hV : W ∘ graph u =ᶠ[𝓝 0] arrow G ∘ graph v := hF.law.trans hG.law.symm |>.mono fun _ hx => Prod.ext rfl hx
  have h : Matches k (W ∘ graph v) (arrow G ∘ graph v) 0 :=
    (show Matches k W (arrow G) (graph v 0) by rw [hG.at0]; exact hj).comp_refl hG.chart
  have hs : Matches k (W ∘ graph u) (W ∘ graph v) 0 := h.symm.unchanged hV.symm EventuallyEq.rfl
  have hb : ContDiffAt ℝ ω O.symm ((W ∘ graph u) 0) := by rw [comp_apply,hF.at0]; exact hj.left.to_localInverse hw (by simp)
  have hi {e : X → Y} (h : Tendsto (graph e) (𝓝 0) (𝓝 0)) : O.symm ∘ (W ∘ graph e) =ᶠ[𝓝 0] graph e :=
    (h.eventually <| O.open_source.mem_nhds hO).mono fun _ hq => O.left_inv hq
  have hg := (hs.refl_comp hb).unchanged (hi hF.home) (hi hG.home)
  refine ⟨hg, ?_⟩
  have hh : Matches k (horz F ∘ graph u) (horz G ∘ graph v) 0 := (show Matches k (horz F) (horz G) (graph u 0) by
    rw [hF.at0]; exact H.pre_fderiv (ContinuousLinearMap.inl ℝ X Y)).comp hg
  have hz := hh.unchanged (hF.horizontal H.left).symm (hG.horizontal H.right).symm
  rw [← hF.at0] at H
  exact hz.behind (H.left.comp _ hF.chart) ((hg.value ▸ H.right : ContDiffAt ℝ ω G (graph v 0)).comp _ hG.chart)
    (H.value.trans (congr_arg G hg.value))
end YM.WilsonStartup.Change
