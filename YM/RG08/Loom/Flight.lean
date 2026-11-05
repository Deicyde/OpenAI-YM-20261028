import YM.RG08.Loom.Foot
/-!
# One triangular chart with mark tested for Ward, θ-independent

Unmasked finite dimensional periods, estimates auxiliary around flat to
establish identities within same formal convention. Doesn't estimate real
physical masks.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent PertExtension.Chart
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {p c f : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (M : Matrix (Body 1 f) (Body 1 c) ℝ) (v : ℝ→Link G c) (n h : ℕ) (K B : FreeResolvent.FaceRow) (σ : ChartRatio G)
variable (F : Air G) (V : ℕ→Config G f→ℝ) (W : Site S.ratio.count → ℕ→Config G f→ℝ) {D : ℕ}{R : ℝ} (τ : ℕ) (o : Site c) (U : BoardU D R G)(φ : Exam D) (κ : S.Choices) (i : G.ColorIndex)
local notation "A" => FreeResolvent.Active G T→ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
local notation "⌂" => tangent G T.Free
local notation "Ξ" => treeMatrix G S T K
local notation "Σ'" => surge S G F i σ
local notation "E₀" => expEra Σ'
local notation "P_K" => (quad G (YM.RG08.hessian K))
local notation "P_B" => (quad G (YM.RG08.hessian B))
local notation "Ω" => regal S G T M v κ n V P_B
local notation "☉" => nibble S G T M v σ
local notation "Χ" => heated S G T M v
local notation "B'" => valve G U S φ h τ o
local notation "Γ" => chapel G S n W τ h
local notation "Υ" => hatsScale S T σ * Real.exp (-1)
local notation "W_" j => (fun k l=> plug (Scores.Pages.roll (spinner j) (S.ratio.count.val:ℝ)⁻¹ φ) R ∘ U k l)
local notation "z_" j => (S.ratio.assemble (o,j))
local notation "σ'" => papyrus S G T M v n h σ W τ
local notation "β" => beam S G T M v n h σ F τ o U φ i
local notation "Z₀" => discPay S G T v κ n V
def chargeDensity (t : ℝ) (u : T.Slice G) := Γ t (T.drape u) * Z₀ t u
local notation "Z₁" => chargeDensity S G T v n h V W τ κ
local notation "ω'" => (fun t:ℝ=> Real.exp (-(1-stanza P_B c (v t))))
lemma profiled (t : ℝ) (ht : 0<t)(x : T.Free→G.Color) :
    PertExtension.Series.Radial.projection σ' Ω t (plates G T.Free x)= ω' t*(jacobian σ (t • x + shifting S G T M v t)* Z₁ t (expLinks G _ (t • x + shifting S G T M v t))) := by
  let z: Z:= t • plates G T.Free x
  have ht' : z.2=t := mul_one t
  let P := shifting S G T M v t
  have hz : z.1=t • x := rfl
  have hv := @drape_sprig c f S G T ((maplit G T).symm (t•x+P))
  have hh : FreeResolvent.profile T ((maplit G T).symm (t•x+P))=t•x+P := rfl; rw [hh] at hv
  have h : fineL G S.ratio (chic S G T M v z) = sprig S T G *ᵥ ((maplit G T).symm (t • x + P)) := by unfold chic; rw [lodge_f,hz,ht']
  let Ll:= Γ t (T.drape (expLinks G _ (t•x+P)))
  rw [show PertExtension.Series.Radial.projection σ' Ω t (plates G T.Free x)=Ll * PertExtension.Series.Radial.projection ☉ Ω t (plates G T.Free x) from ?_, formulate S G T M v κ n V B σ t ht x]; swap
  · simp_rw [projection_eq]; change (Γ _ _ * ☉ z)* _= Ll*(☉ z*_); rw [mul_assoc]; congr 1; unfold Ll; rw [ht',h,← hv]
  unfold Ll P chargeDensity; ring
local notation "hT" => Fits τ U
set_option maxHeartbeats 500000 in
lemma upwards (ha:LocalRatio σ)(he: ContDiffAt ℝ ω v 0) (hp:S.patch.Branches S.kernel G) (hf : Measurable v)
    (hg:∀ i',Caper P_K F n i' (V i')) (hF : Gets F)(hA:Halt F)(hk: Whole K) (hB : Whole B)
    (hK : ∀ m,(K.acts m).IsSymm)(hBz : ∀ m,(B.acts m).IsSymm)(hM : Inputs S M (K.acts f) (B.acts c))(hΔ : (Ξ).PosDef)
    (hW : ∀ p j,Cargo (z_ p) τ j (n+τ) (W_ p) (W p j)) (hu : ∀ i j,Pens (U i j)) (hz:1/2≤R) :
    let C:=∫ x,(crownM hΔ).kern x ∂snow G T
    ∃ s ∈ 𝓝 (1:T.Slice G), ∀ a : ℝ→Set (T.Slice G), (∀ᶠ t in 𝓝[>]0, MeasurableSet (a t) ∧ a t ⊆ s)→ (∃ y∈𝓝 1,∀ᶠ t in 𝓝[>]0, y ⊆ a t) →
      Fit (n+1) (fun t=> ω' t*((t^Module.finrank ℝ (L))⁻¹ * (∫ x in a t, Z₁ t x ∂T.order G)))
         (fun t=> Υ*C*t^τ * year (fun j t=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M*ᵥ v t) (v t)) (billow B' E₀ j)) n t) := by
  intro C
  let P:= papyrus S G T M v n h σ W τ
  obtain ⟨hs,hc⟩:= day_station S G T M v κ n V F K B i he hp hg hF.1 hA hk hB hK hBz hM hΔ
  have hS : ContDiffAt ℝ ∞ P 0 := (paper_lamp S G T M v n h σ W τ (fun p j=> hW p j|>.toShell) he ha).of_le le_top
  have hm t : Measurable (Z₁ t) := by
    apply (charter S G n h W τ (fun p j=> hW p j|>.measure) _ (measurable_const (a:=t)) ((Forest.continuous_drape T (G:=G)).measurable)).mul
    exact Real.continuous_exp.measurable.comp ((labs_meas S (fun i=> (hg i).stamp) κ hp _ (w:=fun _=> input G c (t•v t)) measurable_const (T.continuous_drape.measurable) measurable_const n).neg.div_const _)
  let Y (t : ℝ) := Υ • (t^τ • β t)
  have he' : Meadow Y := Meadow.times (Meadow.single (Grass.const (_:ℝ))) (Meadow.times (Meadow.work (fun t:ℝ=>t^τ) (contDiffAt_id.pow τ)) (beam_event S G T M v n h σ F τ o U φ i he)) -- defeq?
  obtain ⟨s,hL,H⟩:=shift_hall G T.Free ha (shifting S G T M v) (shift_zero S G T M v ▸ ((living_mean S G T M v he).continuousAt.mono_left nhdsWithin_le_nhds)) Z₁ ω' (Eventually.of_forall hm) Ω P (regal_meas S G T M v κ n V P_B hf hp (fun i=> (hg i).stamp)) (paper_bills S G T M v n h σ W τ (fun p j=> hW p j|>.toShell) hf ha) hs hS hc ⟨1,one_pos,eventually_pos.mono fun t ht x _=> profiled S G T M v n h B σ V W τ κ t ht x⟩ n
  have hp' : ∀ x:A, Fit (n+1) (fun t=>PertExtension.Series.Radial.projection P Ω t (plates G T.Free (maplit G T x))) (fun t=> Y t x*(crownM hΔ).kern x) := by
    intro x
    apply Fit.join (foot_fit S G T M v n h K B σ F V W τ o U φ κ i ha he hp hg hF hA hk hB hK hBz hM hΔ hW hu hz x) (Fit.supply (Eventually.of_forall fun t=>?_) _)
    unfold Y; simp [mul_assoc,Pi.smul_apply]
  have hx:=moment_reels G T hΔ Ω P hs hS Y he' n hp'
  refine ⟨s,hL,fun a hP hQ=> Fit.join (H _ hP hQ) (hx.turn.join (Fit.supply (Eventually.of_forall fun t=> ?_) _))⟩
  let f j (x:A):= (billow B' E₀ j) (Χ t x); have hv j : Grass (f j) := grass_settler (chargeS S T G) _ (wheat B' E₀ (fun i=>dryL o _ _) (priorigrass (F:=Σ') (fun j=>Grass.list (s:=range (j+2+1)) fun r _=>Grass.base (Hemi.pos (recital _ _)))) _) -- fix
  unfold Y
  simp_rw [sun_stem, show β t=∑ i∈Finset.range (n+1), t^i • f i from funext fun x=>by simp [beam,year, f, Finset.sum_apply], sun_list hΔ _ (fun i _=> (hv i).scale _), sun_stem]; unfold year; change (_ * (_* ∑ j∈_,_))*C= Υ*C*t^τ * (∑ j∈Finset.range (n+1), t^j * (crownM hΔ).average (snow G T) (f j)); ring
end YM.RG08.Loom
