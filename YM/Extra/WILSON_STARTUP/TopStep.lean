import YM.Bid.Craft
import YM.Extra.WILSON_STARTUP.OnShell
import YM.Work.B04
import YM.Work.F03.Flat
import YM.Work.F04.Choices
import YM.Work.F05.Graphs

/-!
# Replace top input paths on a `Kin` step

Retains the *same* PriceGap, α, coarse PathData (including loop paths), finite
period determinant wave tolerance, all tag branches, and stationary jets and
guess data. Uses implicit equation for the actual new analytic branch, NOT
identification of full analytic series by agreement at finitely many orders.
Requires the old Planned-type conditions explicitly; makes no appeal to an
old Oust, RG advancement theorem or supposed solution of the unsliced map
with arbitrary other paths. Compare E:, binit/bstat, before vstart. Does
not preserve any widths/radii not specified in the current Kin.Planned API.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Function Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work 
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n m : Side} {S : StepData m n} {p q : Clip} {W Q V : PathData G} {B : Forest S.ratio}
    {σ C Λ a : ℝ}

abbrev VChart (G : Gauge) {r : Ratio m n} (B : Forest r) := Dir G m × AxisChart G B

section
variable (B : Forest S.ratio) (r : S.Choices)

def readFine (z : VChart G B) := lifting B (represent z.1) z.2

def onSlice (p : Clip) (W : PathData G) := uncurry (tested B r p W)

@[simp] theorem readFine_one : readFine B (0 : VChart G B) = 1 := by simp [readFine]

theorem readFine_diff (i : Edge (Site n)) : ContDiffAt ℝ ω (fun z : VChart G B => G.mat (readFine B z i)) 0 := by
  unfold readFine lifting
  by_cases he : i ∈ B.trunks
  · simp_rw [show ∀ U : B.Slice G,B.drape U i = 1 from fun U => B.on_tree U ⟨i,he⟩]; exact contDiffAt_const
  simp_rw [show ∀ U : B.Slice G, B.drape U i = U ⟨i,he⟩ from fun U => B.off_tree U ⟨i,he⟩, G.mat_mul]
  refine (((G.exp_jet.comp (contDiff_apply ..)).comp contDiff_snd).contDiffAt).mul ?_
  unfold replica
  split <;> first | exact contDiffAt_const | exact ((F03.represent_smooth ..).comp contDiff_fst).contDiffAt
end

variable {k : ℕ} {x y : Dir G m → AxisChart G B} (H : Matches k
    (mainTerm p W ∘ (represent (n:=n))) (mainTerm p V ∘ represent) 0)

include H in
theorem lift_match {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : E → Config G n) (h : U 0=1)
    (he : ∀ i, ContDiffAt ℝ ω (fun v => G.mat (U v i)) 0) : Matches k (mainTerm p W ∘ U) (mainTerm p V ∘ U) 0 := by
  let Δ (v : E) : Dir G n := fun i => G.plog (G.mat (U v (i.1,axisEquiv.symm i.2)))
  have hΔ : ContDiffAt ℝ ω Δ 0 := contDiffAt_pi.mpr fun i =>
    (show ContDiffAt ℝ ω G.plog (G.mat (U 0 (i.1,axisEquiv.symm i.2))) by rw [h]; exact G.plog_diff).comp (f:=fun v => G.mat (U v (i.1,axisEquiv.symm i.2))) 0 (he _)
  have hz : Δ 0=0 := by ext1 i; simp [Δ,h]
  have hi : represent ∘ Δ =ᶠ[𝓝 0] U := by
    have hb (i) : Tendsto (fun v => U v i) (𝓝 0) (𝓝 1) := by
      have ht : ContinuousAt (fun v => U v i) 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr (he i).continuousAt
      simpa only [h,Pi.one_apply] using ht.tendsto
    filter_upwards [eventually_all.mpr (fun i => (hb i).eventually G.plog_right)] with v hv
    ext1 i
    simpa only [comp_apply,Δ,represent,increment,collect,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _, Pi.one_apply, mul_one] using! hv i
  rw [← hz] at H
  exact (H.comp_refl hΔ).unchanged (hi.fun_comp (mainTerm p W)) (hi.fun_comp (mainTerm p V))

include H in
theorem tested_match (h : Critical B p W x) (r : S.Choices) : Matches k (onSlice B r p W) (onSlice B r p V) 0 := by
  have hb := lift_match H (readFine B) (readFine_one _) (readFine_diff _)
  let f := fun z : VChart G B => noiseTaylor S (represent z.1) (readFine B z) r
  have hf : ContDiffAt ℝ ω f 0 := by
    rw [show f = uncurry (tested B r p W) - mainTerm p W ∘ readFine B from funext fun i => (add_sub_cancel_left ..).symm]
    exact (h.2.2 r).1.sub hb.left
  exact hb.add (matches_self _ hf)

lemma station_of {u : Dir G m → AxisChart G B} (h : Critical B p V u) (r : S.Choices) :
    Station (onSlice B r p V) u := ⟨h.2.1,h.1,((h.2.2 r).2.mono fun _ he => he.fderiv)⟩

lemma definite_of (ht : PriceGap B p V a) (ha : 0 < a) (r : S.Choices)
    (h : ContDiffAt ℝ ω (onSlice B r p V) 0) : Definite (onSlice B r p V) := by
  refine ⟨h,fun y hy => ?_⟩
  by_contra hn
  exact (F05.tested_diag ha ht r y hn).ne' hy

lemma new_crit (hs : S.patch.Branches S.kernel G) (hV : Prismatic B p V) (ht : PriceGap B p V a) (ha : 0 < a)
    (hz : ∀ r : S.Choices,vert (onSlice B r p V) (0 : VChart G B) = 0) : ∃ u,Critical B p V u := by
  let r := Classical.arbitrary S.Choices
  let F := onSlice B r p V
  have hF := definite_of ht ha r (hV r)
  let H := (matches_self 1 hF.smooth).diff_vert.left
  let u := H.implicitFunction (by simp) hF.forms
  have he : u 0 = 0 := H.implicitFunction_apply_self (by simp) hF.forms
  have hc : ContDiffAt ℝ ω u 0 := H.contDiffAt_implicitFunction (by simp) hF.forms
  refine ⟨u, he, hc, fun s => ⟨hV s, ?_⟩⟩
  let F' := onSlice B s p V
  have ht : Tendsto (graph u) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds (he ▸ hc.continuousAt.tendsto)
  have hcrit : ∀ᶠ x in 𝓝 0, vert F (graph u x) = vert F 0 := H.eventually_apply_implicitFunction (by simp) hF.forms
  have Heq : fderiv ℝ F' =ᶠ[𝓝 0] fderiv ℝ F := (F04.tested_germ hs B p V s r).fderiv
  filter_upwards [hcrit, ht.eventually Heq, ht.eventually ((hV s).eventually (by simp)),
    ht.eventually ((hV r).eventually (by simp))] with x h₁ h₂ h₃ h₄
  have hv : F04.vert F' (graph u x) = 0 := by
    rw [F04.vert,h₂,← F04.vert, show F04.vert F (graph u x) = _ from
      (F04.hasFDerivAt_slice F x (u x) (h₄.differentiableAt (by simp))).fderiv.symm.trans (h₁.trans (hz r))]
  rw [← hv]; exact F04.hasFDerivAt_slice F' x (u x) (h₃.differentiableAt (by simp))

lemma guessed_match {A : Matrix (Body 1 n) (Body 1 m) ℝ} (h : Matches 1 x y 0) (ht : Guessed B A x) : Guessed B A y := by
  intro v
  have hv := (show Matches 1 x y ((0:ℝ) • v) from by simpa using h).comp_refl (f:=fun t : ℝ => t • v) (by fun_prop)
  have he := congr_arg (fun T => Tensor.diagonal T 1) (hv.jets 1 le_rfl)
  simp only [Tensor.diagonal,iteratedFDeriv_one_apply,comp_def] at he
  exact (hv.right.differentiableAt (by simp)).hasDerivAt.congr_deriv (he.symm.trans (ht v).deriv)

lemma compare_det {u : S.Choices} (h : Matches 4 (onSlice B u p W) (onSlice B u p V) 0) : Matches 2
    (fun z : VChart G B => (hessian B u p W z.1 z.2).det)
    (fun z : VChart G B => (hessian B u p V z.1 z.2).det) 0 := by
  let E := Precision.Key B G
  let D := VChart G B
  let f (P : PathData G) (s : Equiv.Perm E) (i : E) (z : D) := hessian B u p P z.1 z.2 (s i) i
  have he s i : Matches 2 (f W s i) (f V s i) 0 := by
    unfold f hessian; simp only [Matrix.of_apply,iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    let A := frame B (s i); let C := frame B i
    change Matches 2 (fun z => vert (vert (onSlice B u p W)) z A C) (fun z => vert (vert (onSlice B u p V)) z A C) 0
    exact h.diff_vert.diff_vert.refl_comp (u:=fun L : AxisChart G B →L[ℝ] AxisChart G B →L[ℝ] ℝ => L A C)
      ((contDiffAt_id.clm_apply contDiffAt_const).clm_apply contDiffAt_const)
  haveI : Fintype (Equiv.Perm E) := Equiv.instFintype
  let J (P : PathData G) := ∑ s : Equiv.Perm E, Equiv.Perm.sign s • ∏ i, f P s i
  have ht : Matches 2 (J W) (J V) 0 := matches_sum _ fun s _ => (matches_prod _ (fun i _ => he s i)).refl_comp
    (u:=fun y => Equiv.Perm.sign s • y) (by simp only [Units.smul_def]; exact contDiffAt_id.const_smul _)
  convert! ht using 1 <;> (ext z; simp only [Matrix.det_apply,J,f,Finset.sum_apply,Finset.prod_apply,Pi.smul_apply]; congr! 2)

private lemma loop_zero {P : PathData G} (h : ∀ b,(P.loop b).coeff=0) (U : Config G n) : Precision.loop P U=0 := by
  simp [Precision.loop,Patch.average,uncut, Atom.unmasked, Atom.poly,h]

lemma thermal_match {O : ChartRatio G} (hO : LocalRatio O) (hw : ∀ b,(W.loop b).coeff=0) (hv : ∀ b,(V.loop b).coeff=0)
    (hF : Critical B p W x) (hG : Critical B p V y) (r : S.Choices) (hQ : Definite (onSlice B r p V))
    (h : Matches 4 (onSlice B r p W) (onSlice B r p V) 0) (h₁ : 0 < (hessian B r p W 0 (x 0)).det) :
    Matches 2 (thermal B r p W x O) (thermal B r p V y O) 0 := by
  let g := graph x
  let g' := graph y
  have he : Matches 2 g g' 0 := ((compare h.symm (station_of hG r) (station_of hF r) hQ).1.lower (by decide)).symm
  have hx := (station_of hF r).at0
  let f (P : PathData G) := fun z : VChart G B => (hessian B r p P z.1 z.2).det
  have hdet : Matches 2 (f W) (f V) (g 0) := Eq.mpr (congr_arg (Matches 2 (f W) (f V)) hx) (compare_det h)
  have hd : Matches 2 (f W ∘ g) (f V ∘ g') 0 :=
    hdet.comp he
  let j (w : Dir G m → AxisChart G B) (v : Dir G m) := ∏ i, O.J (w v i)
  have hj : Matches 2 (j x) (j y) 0 := by
    have hi : Matches 2 x y 0 := he.refl_comp contDiffAt_snd
    convert matches_prod (k:=2) (x:=(0:Dir G m)) Finset.univ (f:=fun i v => O.J (x v i)) (g:=fun i v => O.J (y v i)) (fun i _ =>
      (hi.apply_pi i).refl_comp (hO.germ (x 0 i) (by rw [hF.1]; simpa using hO.patch))) using 1 <;> ext v <;> simp only [j,Finset.prod_apply]
  unfold thermal; simp only [loop_zero (n:=n) hw,loop_zero (n:=n) hv, zero_add]
  exact hd.together hj (H:=fun a b => (1/2)*Real.log a - Real.log b) (((contDiffAt_fst.log h₁.ne').const_smul (1/2 : ℝ)).sub
    (contDiffAt_snd.log (by simp only [j,hF.1,Pi.zero_apply,hO.anchored,Finset.prod_const_one]; exact one_ne_zero)))

section
variable {A : Matrix (Body 1 n) (Body 1 m) ℝ} {O : ChartRatio G} {α Θ γ Λ : ℝ}

theorem top_step (H : Matches 4 (mainTerm p W ∘ (represent (n:=n))) (mainTerm p V ∘ represent) 0) (ha : 0 < a) (hs : S.patch.Branches S.kernel G) (hF : Critical B p W x) (hG : Guessed B A x)
    (ht : PriceGap B p W a) (hP : ClassicalMatch B p q W Q x)
    (h : FiniteBound B W Q p q α O x Θ γ Λ) (hO : LocalRatio O) (hw : ∀ b,(W.loop b).coeff=0) (hv : ∀ b,(V.loop b).coeff=0) :
    PriceGap B p V a ∧ ∃ u, Critical B p V u ∧ Guessed B A u ∧ ClassicalMatch B p q V Q u ∧ FiniteBound B V Q p q α O u Θ γ Λ := by
  have hj (r : S.Choices) := tested_match H hF r
  have hV : PriceGap B p V a := by
    intro r v
    have hh : Matches 4 (tested B r p W 0) (tested B r p V 0) 0 := (hj r).comp_refl
      (f:=fun v : AxisChart G B => ((0:Dir G m),v)) (contDiffAt_const.prodMk contDiffAt_id)
    rw [← hh.jets 2 (by decide)]; exact ht r v
  obtain ⟨u,hu⟩ := new_crit hs (fun r => (hj r).right) hV ha (fun r =>
    ((hj r).diff_vert.value.symm.trans (by change fderiv ℝ (tested B r p W 0) 0=0; simpa only [hF.1] using (hF.2.2 r).2.self_of_nhds.fderiv)))
  let s := Classical.arbitrary S.Choices
  have hD (r : S.Choices) := definite_of hV ha r ((hj r).right)
  have hc (r : S.Choices) := compare (hj r).symm (station_of hu r) (station_of hF r) (hD r)
  refine ⟨hV,u,hu,guessed_match (((hc s).1.symm.lower (m:=1) (by decide)).refl_comp (u:=Prod.snd) contDiffAt_snd) hG,fun j hk r => ?_,?_⟩
  · obtain ⟨hf,hs,h⟩ := hP j hk r; have hd := (hc r).2
    exact ⟨hd.left,hs,(hd.jets j hk).trans h⟩
  have hM (r : S.Choices) := thermal_match hO hw hv hF hu r (hD r) (hj r) (h.branch r |>.self_of_nhds)
  refine ⟨fun r => F05.hessian_pos ha hV hu r, fun r => (hM r).right, h.classicalResult, fun r i j b c h1 h2 => ?_⟩
  dsimp; rw [← (hM r).jets 2 le_rfl]; exact h.wave_price r i j b c h1 h2
end
end YM.WilsonStartup.Change
