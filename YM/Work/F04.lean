import YM.Work.F04.Calculus
import YM.Work.F04.Choices
import YM.Work.F04.Pairing




/-!
# Fixed-period critical branch and tree-slice quadratic value

Everything here is conditional, in the actual tree coordinates. No uniform
control of the neighborhood, determinant result or independence from tree.
The equation is solved for one tag array; THAT solution works for every tag
array by equality on germs. `test_pair` checks the stationary response using
both parts of `stationed`, not just stationary value comparison. No need
to use even output Floor in this proof: the bilinear output that comes out
of the computation is already a Hessian of a smooth germ.
-/

set_option autoImplicit false
noncomputable section

open Filter Function Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

namespace YM.Work.F04

open Lattice RG Wilson Precision Exterior Bid Tree Bloch Laurent

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma invertible (H : Forest S.ratio) (p : Clip) (W : PathData G) (a : ℝ)
    (ha : 0 < a) (t : S.Choices) (hg : PriceGap H p W a)
    (hh : ContDiffAt ℝ ω (uncurry (tested H t p W)) 0)
    (hz : fderiv ℝ (uncurry (tested H t p W)) 0 = 0) :
    (fderiv ℝ (vert (uncurry (tested H t p W))) 0 ∘L
      ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H)).IsInvertible := by
  let F := uncurry (tested H t p W)
  let E := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H)
  apply form_invertible
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  change fderiv ℝ (vert F) 0 (0, v) = 0 at hv
  have he : iteratedFDeriv ℝ 2 (tested H t p W 0) 0 ![v,v] = 0 := by
    rw [iteratedFDeriv_two_apply]
    have hF : ContDiffAt ℝ ω F (E 0) := by rw [map_zero]; exact hh
    have hD : fderiv ℝ F (E 0) = 0 := by rw [map_zero]; exact hz
    have hchain := stationary_chain F E 0 hF E.contDiff.contDiffAt hD v v
    rw [map_zero, E.fderiv] at hchain
    change fderiv ℝ (fderiv ℝ (F ∘ E)) 0 v v = _
    change _ = iteratedFDeriv ℝ 2 F 0 ![(0,v), (0,v)] at hchain
    rw [hchain, ← vert_rate F 0 hh (0,v) v, hv]
    rfl
  have Hs := hg t v
  rw [he] at Hs
  funext i
  by_contra Hi
  have hi : 0 < ‖v i‖^2 := sq_pos_of_pos (norm_pos_iff.mpr Hi)
  have HZ : 0 < a * ∑ j : H.Free, ‖v j‖^2 := mul_pos ha
    (Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, hi⟩)
  exact HZ.not_ge Hs

lemma exists_branch (H : Forest S.ratio) (p : Clip) (W : PathData G) (a : ℝ) (ha : 0 < a)
    (t : S.Choices) (ht : S.patch.Branches S.kernel G) (hp : Prismatic H p W)
    (hg : PriceGap H p W a) (hz : fderiv ℝ (uncurry (tested H t p W)) 0 = 0) :
    ∃ ρ, Critical H p W ρ := by
  let F := uncurry (tested H t p W)
  have hF := vert_smooth F 0 (hp t)
  have hV : vert F 0 = 0 := by simp [F, vert, hz]
  have hi := invertible H p W a ha t hg (hp t) hz
  let ρ := hF.implicitFunction (by simp) hi
  have he : ρ 0 = 0 := hF.implicitFunction_apply_self (by simp) hi
  have hc : ContDiffAt ℝ ω ρ 0 := hF.contDiffAt_implicitFunction (by simp) hi
  refine ⟨ρ, he, hc, fun s => ⟨hp s, ?_⟩⟩
  let J := uncurry (tested H s p W)
  have Hx : Tendsto (fun x => (x, ρ x)) (𝓝 0) (𝓝 0) := by
    have hh := (continuousAt_id.prodMk hc.continuousAt).tendsto
    simpa only [id_eq, he] using! hh
  have hcrit : ∀ᶠ x in 𝓝 0, vert F (x, ρ x) = vert F 0 :=
    hF.eventually_apply_implicitFunction (by simp) hi
  have Heq : fderiv ℝ J =ᶠ[𝓝 0] fderiv ℝ F := (tested_germ ht H p W s t).fderiv
  filter_upwards [hcrit, Hx.eventually Heq, Hx.eventually ((hp s).eventually (by simp))] with x h₁ h₂ h₃
  have hy : vert J (x, ρ x) = 0 := calc
    _ = vert F (x, ρ x) := congr_arg (· ∘L ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H)) h₂
    _ = 0 := h₁.trans hV
  rw [← hy]
  exact hasFDerivAt_slice J x (ρ x) (h₃.differentiableAt (by simp))

lemma tangent (H : Forest S.ratio) (p : Clip) (W : PathData G) (a : ℝ) (ha : 0 < a)
    (hg : PriceGap H p W a) (B C : Bed) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (hd : Inputs S U (B.metric.acts f) (C.metric.acts c))
    (hq : Comptroller H B p W) (ρ) (h : Critical H p W ρ) (t : S.Choices) (x : Dir G c) :
    fderiv ℝ ρ 0 x = relative H U x := by
  let F := uncurry (tested H t p W)
  let b := fun y => (y, ρ y)
  have h0 : b 0 = 0 := by simp [b, h.1]
  obtain ⟨hh,he⟩ := h.2.2 t
  have hρ : HasFDerivAt b ((ContinuousLinearMap.id ℝ (Dir G c)).prod (fderiv ℝ ρ 0)) 0 :=
    (hasFDerivAt_id 0).prodMk (h.2.1.differentiableAt (by simp)).hasFDerivAt
  have ht := hρ.continuousAt.tendsto
  rw [h0] at ht
  have hV : vert F ∘ b =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [he, ht.eventually (hh.eventually (by simp))] with i hi hj
    exact (hasFDerivAt_slice F i (ρ i) (hj.differentiableAt (by simp))).unique hi
  have h1 : fderiv ℝ (vert F) 0 (x, fderiv ℝ ρ 0 x) = 0 := by
    have hy : DifferentiableAt ℝ (vert F) (b 0) := by
      rw [h0]; exact (vert_smooth F 0 hh).differentiableAt (by simp)
    have hy' := hV.fderiv_eq (𝕜 := ℝ)
    rw [(hy.hasFDerivAt.comp 0 hρ).fderiv, fderiv_const_apply, h0] at hy'
    exact DFunLike.congr_fun hy' x
  have h2 : fderiv ℝ (vert F) 0 (x, relative H U x) = 0 := by
    ext v
    rw [vert_rate F 0 hh]
    have hf : iteratedFDeriv ℝ 2 F 0 ![(x, relative H U x), (0,v)] =
        iteratedFDeriv ℝ 2 F 0 ![(0,v), (x, relative H U x)] := by
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      exact hh.isSymmSndFDerivAt (by simp) _ _
    rw [hf, show iteratedFDeriv ℝ 2 F 0 _ = _ from test_pair H p W B C U hd hq (0, v) x t]
    simp [gaugeFiscal, parts, dotProduct]
  have Hi := invertible H p W a ha t hg hh (hq t).2.1
  apply Hi.injective
  have heq (y : AxisChart G H) : (fderiv ℝ (vert F) 0) (x, y) =
      fderiv ℝ (vert F) 0 (x, 0) + fderiv ℝ (vert F) 0 (0, y) := by
    rw [← map_add]; simp
  change fderiv ℝ (vert F) 0 (0, fderiv ℝ ρ 0 x) = fderiv ℝ (vert F) 0 (0, relative H U x)
  rw [heq] at h1 h2
  exact add_left_cancel (h1.trans h2.symm)

lemma stationary_value (H : Forest S.ratio) (p : Clip) (W : PathData G) (B C : Bed)
    (U : Matrix (Body 1 f) (Body 1 c) ℝ) (hd : Inputs S U (B.metric.acts f) (C.metric.acts c))
    (hq : Comptroller H B p W) (ρ) (h : Critical H p W ρ)
    (hh : ∀ x, fderiv ℝ ρ 0 x = relative H U x) : HeatG H p W ρ C := by
  intro t
  let F := uncurry (tested H t p W)
  let b := fun y => (y, ρ y)
  have h0 : b 0 = 0 := by simp [b, h.1]
  have hg : ContDiffAt ℝ ω b 0 := contDiffAt_id.prodMk h.2.1
  have hf : ContDiffAt ℝ ω F (b 0) := by rw [h0]; exact (h.2.2 t).1
  have he : fderiv ℝ F (b 0) = 0 := by rw [h0]; exact (hq t).2.1
  have hw : HasFDerivAt b ((ContinuousLinearMap.id ℝ (Dir G c)).prod (fderiv ℝ ρ 0)) 0 :=
    (hasFDerivAt_id 0).prodMk (h.2.1.differentiableAt (by simp)).hasFDerivAt
  have ht (x) : fderiv ℝ b 0 x = (x, relative H U x) := by rw [hw.fderiv]; simp [hh]
  have hm (x y : Dir G c) : fderiv ℝ (fderiv ℝ (F ∘ b)) 0 x y = gaugeFiscal C x y := by
    rw [stationary_chain F b 0 hf hg he, ht, ht, h0]
    exact test_pair H p W B C U hd hq _ _ _
  have hc := half_pairing (F ∘ b) (hf.comp 0 hg)
  simp_rw [hm] at hc
  exact hc

theorem answer : YM.Bid.F04 := by
  intro G c f S hs H B C p W T a ha hd hp hq hg _hfloor
  let t : S.Choices := Classical.arbitrary _
  obtain ⟨ρ,h⟩ := exists_branch H p W a ha t hs.1 hp hg (hq t).2.1
  let U := installed S.ratio T.A0
  have HH := tangent H p W a ha hg B C U hd.trial hq ρ h t
  refine ⟨ρ, h, ?_, stationary_value H p W B C U hd.trial hq ρ h HH⟩
  intro x
  change HasDerivAt _ (relative H U x) 0
  rw [← HH]
  exact Push.side _ (h.2.1.differentiableAt (by simp)) _

end YM.Work.F04
