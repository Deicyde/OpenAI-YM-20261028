import YM.AnalyticNext.QUARTIC_MATCH.Agreement
import YM.AnalyticNext.QUARTIC_MATCH.Invoice
import YM.Progress.STATIONARY_SCENES.Frames



/-!
# Neighboring fallow meshes for unmasked invoices only

Need no spare funding built by rerolling. Instantiate here on the ACTUAL
patch, attaching every probe's exact same kinetic paths. All laws are on larger sides
including not necessarily Schedule-admitted sizes; thus coefficients can be unfolded; not a
change of Schedule. Not comparing any quantum jets by this extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

namespace Analyzers
open BoxChain Sheets Tree

def allowanceSide (P : Patch) := 100 * (P.J+3+4)
lemma threshold (P : Patch) (K : KernelChoices) (h : P.Branches K G) (c : Side) :
    allowanceSide P ≤ c.val ↔ Larger (G:=G) (stepAt P K c) := by
  have he : 100 * Pressure.macroR P=allowanceSide P * P.L.val := by
    unfold allowanceSide Pressure.macroR Patch.radius; ring
  rw [Larger]; change _ ↔ _ ∧ 100*Pressure.macroR P ≤ c.val*P.L.val ∧ _
  constructor
  · intro hc; rw [he]; exact ⟨h,Nat.mul_le_mul_right _ hc, by unfold allowanceSide at hc; omega⟩
  intro ⟨_,hb,_⟩; rw [he] at hb; exact Nat.le_of_mul_le_mul_right hb P.L.property

/-- All extensions on true inputs; use even if other retained funding already
carrying stronger generation hypotheses. η here is *post*-L. -/
structure Series (P : Patch) (K : KernelChoices) (G : Gauge) (M : Bed) (p : Clip)
    (W : PathData G) (r : ℝ) where
  society : P.Branches K G
  choice (c : Side) : (stepAt P K c).Choices
  tree (c : Side) : Forest (stepAt P K c).ratio
  ρ (c : Side) : Dir G c → AxisChart G (tree c)
  controller c : allowanceSide P ≤ c.val → Comptroller (tree c) M p W
  cheap : 0 < r
  gap c : allowanceSide P ≤ c.val → PriceGap (tree c) p W r
  solved c : allowanceSide P ≤ c.val → Critical (tree c) p W (ρ c)

variable {M : Bed} {p : Clip} {W : PathData G} {P : Patch} {K : KernelChoices}

open Progress.StationaryScenes

/-- before N/W/p. -/
theorem serves (P : Patch) (K : KernelChoices) (m : ℝ) (hm : 0<m) (h : P.Branches K G) :
    ∃ r : ℝ, 0<r ∧ ∀ M : Bed, ∀ (p : Clip) (W : PathData G) (σ C Λ A : ℝ),
      W.Bounds p σ C Λ → Attached M W → (∀ c, Sworn M c G) →
        (∀ c, Floor M p c m A) → Nonempty (Series P K G M p W r) := by
  obtain ⟨r,hr,hR⟩ := Work.F01.answer Work.E02.answer G P.L P.J K m hm
  refine ⟨r,hr, fun M p W σ C Λ A hW hb hs hf => ?_⟩
  let T (c : Side) := exampleTree (stepAt P K c)
  let t (c : Side) : (stepAt P K c).Choices := Classical.arbitrary _
  have ht (c : Side) (he : allowanceSide P≤ c.val) := (threshold P K h c).1 he
  have he (c : Side) (hg : allowanceSide P ≤ c.val) := Work.F03.answer G _ _ _ (ht c hg) (T c) M _ _ _ _ _ _ _
    (hf _) hW hb (hs _) (Work.F02.answer _ _ _ _ _ _ hW)
  have hL (c : Side) (hy : allowanceSide P ≤ c.val) : PriceGap (T c) p W r := hR c _ _ rfl rfl rfl (ht c hy) (T c)
    M p W A (hf _) (he c hy).1 (he c hy).2
  have hh (c : Side) (hy : allowanceSide P ≤ c.val) := Work.F04.exists_branch (T c) p W r hr (t c) h (he c hy).1
    (hL c hy) ((he c hy).2 (t c)).2.1
  let ρ (c : Side) : Dir G c → AxisChart G (T c) := if H : allowanceSide P ≤ c.val then (hh c H).choose else 0
  refine ⟨⟨h,t,T,ρ,fun c hy => (he c hy).2,hr,hL,fun c hy => ?_⟩⟩
  unfold ρ; rw [dif_pos hy]; exact (hh c hy).choose_spec

variable {r A : ℝ} {σ C Λ τ T Ξ : ℝ}
namespace Series

def canonical (S : Series P K G M p W r) (c : Side) : Dir G c → ℝ :=
    Joint.value (S.tree c) (S.choice c) p W (S.ρ c)

-- No need compare `Guessed`. Drive the joint reductions on the actual choices.
lemma canonical_value (S : Series P K G M p W r) (hW : W.Bounds p σ C Λ)
    (c : Side) {f : Side} (S' : StepData c f) (he : S'.patch=P) (hh : S'.kernel=K)
    (T' : Forest S'.ratio) (t' : S'.Choices) (b : Dir G c → AxisChart G T') (hb : Critical T' p W b)
    (hL : Larger (G:=G) S') : S.canonical c =ᶠ[𝓝 0] Joint.value T' t' p W b := by
  have hv : f=c*P.L := PNat.eq (by rw [S'.sizes,he]; rfl)
  subst f
  obtain rfl : S'=stepAt P K c := by cases S'; congr
  let s := stepAt P K c
  have hx := (threshold P K S.society c).2 hL
  -- use joint recognizes; lift other critical graph.
  obtain ⟨ha,hj,hH⟩ := Joint.joints S.society hW hb t'
  let T := S.tree c
  let t := S.choice c
  let F := arc (plant T' ∘ arc b)
  have hz : F 0=0 := Prod.ext rfl ha
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hz] using (show Tendsto F (𝓝 0) (𝓝 (F 0)) from hj.arc_smooth.continuousAt.tendsto)
  filter_upwards [hH, ht.eventually (Joint.recognizes S.society hW (S.solved c hx) t' M (S.controller c hx)
    S.cheap (S.gap c hx)), hj.station, (Work.F05.crit_home (S.solved c hx)).eventually (Work.F04.tested_germ S.society T _ _ t t')]
    with z hz hu hi hh
  exact hh.trans ((hu hi).symm.trans hz)

lemma leg_value (S : Series P K G M p W r) (c : Side) (hc : allowanceSide P ≤ c.val) : ContDiffAt ℝ ω (S.canonical c) 0 := by
  have ht := SliceExchange.on_shell (S.choice c) (S.solved c hc)
  exact ht.action.comp _ ht.arc_smooth

def residual (S : Series P K G M p W r) (R : PathData G) (q : Clip) (j : ℕ) (c : Side) : Dom G j c :=
    Tensor.coeff (S.canonical c-Residual.baseAt q R) j 0

lemma debt (S : Series P K G M p W r) {R : PathData G} {q : Clip}
    (hp : W.Bounds p σ C Λ) (he : R.Bounds q τ T Ξ) (j : ℕ) :
    Mail.Law (allowanceSide P) (S.residual R q j) := by
  have ht (c : Side) (hk : allowanceSide P ≤ c.val) : ContDiffAt ℝ j (S.canonical c-Residual.baseAt q R) 0 :=
    (((S.leg_value c hk).sub (Residual.base_smooth he)).of_le le_top)
  have hh (c : Side) (L : Dir G c →L[ℝ] Dir G c) (hk : allowanceSide P ≤ c.val)
      (h : S.canonical c ∘ L =ᶠ[𝓝 0] S.canonical c) (H : Residual.baseAt q R ∘ L = Residual.baseAt q R) (X) :
      S.residual R q j c (fun i => L (X i))=S.residual R q j c X := by
    let f := S.canonical c-Residual.baseAt q R
    have hx : f ∘ L =ᶠ[𝓝 0] f := h.mono fun i hi => congr_arg₂ (·-·) hi (congr_fun H i)
    have hf := (hx.iteratedFDeriv ℝ j).eq_of_nhds
    change iteratedFDeriv ℝ j ((S.canonical c-Residual.baseAt q R) ∘ L) 0=_ at hf
    rw [Next.Foundations.jets_linear L (ht _ hk)] at hf
    exact congr_arg ((Nat.factorial j : ℝ)⁻¹ • ·) (DFunLike.congr_fun hf X)
  constructor
  · intro c hk t X; exact hh _ (colors t) hk (color_value S.society hp (S.solved c hk) (S.controller c hk) S.cheap
      (S.gap c hk) (S.choice c) t) (Residual.base_colors he t) X
  · intro c hk t X; exact hh _ (shifts 1 t) hk (oriented S.society hp (S.solved c hk) (S.controller c hk) S.cheap
      (S.gap c hk) 1 t (S.choice c)) (Residual.base_orient ..) X
  intro c d hc hd h u
  let f c := S.canonical c-Residual.baseAt q R
  let a : Dir G c →L[ℝ] Dir G d := Sheets.reuses h
  have hx : (f d ∘ a) =ᶠ[𝓝 0] (Sheets.mult h:ℝ) • f c := by
    filter_upwards [covers_value P K h S.society hp (S.solved c hc) (S.solved d hd) (S.controller d hd) S.cheap
      (S.gap d hd) (S.choice c) (S.choice d)] with x hx
    change S.canonical d (a x)=(Sheets.mult h:ℝ) • S.canonical c x at hx
    have hz : Residual.baseAt q R (a x) = Sheets.mult h • Residual.baseAt q R x := main_copy h q R (represent x)
    change S.canonical d (a x)-Residual.baseAt q R (a x)= (mult h:ℝ) • (S.canonical c x-Residual.baseAt q R x)
    rw [hx,hz,smul_sub,Nat.cast_smul_eq_nsmul,Nat.cast_smul_eq_nsmul]
  have hm := (hx.iteratedFDeriv ℝ j).eq_of_nhds
  rw [iteratedFDeriv_const_smul_apply (ht c hc),Next.Foundations.jets_linear a (ht d hd)] at hm
  unfold residual Tensor.coeff; simp only [_root_.smul_apply,smul_eq_mul]
  rw [show iteratedFDeriv ℝ j (S.canonical d-Residual.baseAt q R) 0 (fun i => reuses h (u i)) = (mult h:ℝ)*iteratedFDeriv ℝ j (S.canonical c-Residual.baseAt q R) 0 u from
    DFunLike.congr_fun hm u]; ring
end Series
end Analyzers
end YM.AnalyticNext.QuarticMatch
