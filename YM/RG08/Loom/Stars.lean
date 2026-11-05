import YM.RG08.Loom.Flight
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
local notation "Z₀" => discPay S G T v κ n V
local notation "Z₁" => chargeDensity S G T v n h V W τ κ
local notation "ω'" => (fun t:ℝ=> Real.exp (-(1-stanza P_B c (v t))))

section extract
variable {g w t a b : ℝ→ℝ}
lemma alive (hp : Fit (n+1) g w) (h : Tendsto w (𝓝[>]0) (𝓝 (w 0))) : Tendsto g (𝓝[>]0) (𝓝 (w 0)) := by
  simpa using! ((bill_goes (p:=g-w) (hp.lower (k:=1) (by omega))).add h)
lemma shaved {g w f l : ℝ→ℝ} (hf : Fit (n+1) f (g*w)) (h : Fit (n+1) l w) (hz : Tendsto w (𝓝[>]0) (𝓝 (w 0))) (hr : w 0≠0) (hg : Bill 0 g) : Fit (n+1) (f/l) g := by
  have ht := alive n h hz
  have hw : Tendsto l⁻¹ (𝓝[>]0) (𝓝 (w 0)⁻¹) := ht.inv₀ hr
  have hP : Fit (n+1) (g*w) (g*l) := by simpa using h.turn.right hg
  rw [div_eq_mul_inv]; refine Fit.join ((hf.join hP).left (life_price hw)) (Fit.supply ?_ _)
  filter_upwards [ht.eventually (eventually_ne_nhds hr)] with i hi
  dsimp only [Pi.mul_apply,Pi.inv_apply]; exact mul_inv_cancel_right₀ hi _
end extract

private def lev (hΔ : (Ξ).PosDef) (j : ℕ) (t : ℝ) := leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M*ᵥ v t) (v t)) (E₀ j)
local notation "p'" => lev S G T M v K σ F i
set_option maxHeartbeats 400000 in
lemma evoked (ha:LocalRatio σ)(he: ContDiffAt ℝ ω v 0) (hp:S.patch.Branches S.kernel G) (hf : Measurable v)
    (hg:∀ i',Caper P_K F n i' (V i')) (hF : Gets F)(hA:Halt F)(hk: Whole K) (hB : Whole B)
    (hK : ∀ m,(K.acts m).IsSymm)(hBz : ∀ m,(B.acts m).IsSymm)(hM : Inputs S M (K.acts f) (B.acts c))(hΔ : (Ξ).PosDef)
    (F' : Air G)(hY : ∀ w : Link G c, Aura (fun j=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M *ᵥ w) w) (E₀ j)) (fun j=> -grand (j+2) (F' j) c w))
    (hW : ∀ p j,Cargo (z_ p) τ j (n+τ) (W_ p) (W p j)) (hu : ∀ i j,Pens (U i j)) (hz:1/2≤R)
    (U' : BoardU D R G)
    (hm : ∀ w : Link G c, let P := leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M *ᵥ w) w); ∀ j,P (billow B' E₀ j)=∑ b∈wheel j, large o (τ+b.1) (fun r=>plug φ R ∘ U' b.1 r) w*P (E₀ b.2)) :
    ∃ s ∈ 𝓝 (1:T.Slice G), ∀ a : ℝ→Set (T.Slice G), (∀ᶠ t in 𝓝[>]0, MeasurableSet (a t) ∧ a t ⊆ s)→ (∃ y∈𝓝 1,∀ᶠ t in 𝓝[>]0, y ⊆ a t) →
      Fit (n+1) (fun t=> (∫ x in a t, Z₁ t x ∂T.order G)/(∫ x in a t,Z₀ t x ∂T.order G))
         (fun t=> t^τ * arco c (fun j=>large o (τ+j) (fun r=>plug φ R ∘ U' j r)) v n t) := by
  obtain ⟨s,hs,hfwd⟩:= upwards S G T M v n h K B σ F V W τ o U φ κ i ha he hp hf hg hF hA hk hB hK hBz hM hΔ hW hu hz -- h shadow
  obtain ⟨g,hg',H⟩ := unbless S G T M v κ n V F F' K B i σ ha he hf hp hg hF hA hk hB hK hBz hM hΔ hY
  refine ⟨s∩g,inter_mem hs hg',fun a hP hQ=>?_⟩
  have h₀ := H a (hP.mono fun t hv=> ⟨hv.1,hv.2.trans Set.inter_subset_right⟩) hQ
  have h₁ := hfwd a (hP.mono fun t hv=> ⟨hv.1,hv.2.trans Set.inter_subset_left⟩) hQ
  let C:=∫ x,(crownM hΔ).kern x ∂snow G T
  have hC:0<Υ*C := mul_pos (mul_pos (pow_pos ha.scale _) (Real.exp_pos _)) (normSun hΔ (snow G T))
  let p := p' hΔ; let X i t := -grand (i+2) (F' i) c (v t); let Y i t := large o (τ+i) (fun r=>plug φ R∘U' i r) (v t)
  have hx t : Aura (fun i=>p i t) (fun i=>X i t):=hY (v t)
  have hv : ∀ j,Bill 0 (X j) := fun j=> life_price ((((opus_whole (F' j) _ _).smooth.continuous.continuousAt.comp he.continuousAt).neg).mono_left nhdsWithin_le_nhds)
  have hy : ∀ j,Bill 0 (Y j) := fun j=> life_price ((((large_smooth o _).continuous.continuousAt).comp he.continuousAt).mono_left nhdsWithin_le_nhds)
  have hw : Fit (n+1) (Real.exp ∘ year X n) (year p n) := year_aura hx hv n
  let Tx t := Real.exp (year X n t)
  have htX: ContinuousAt Tx 0 := Real.continuous_exp.continuousAt.comp ((ContDiffAt.sum (n:=ω) (s:=Finset.range (n+1)) (f:=fun i t=> t^i * X i t) (fun j _=> (contDiffAt_id.pow j).mul (((opus_whole (F' j) _ _).smooth.contDiffAt.comp _ he).neg))).continuousAt)
  let Q₁ : ℝ → ℝ := fun t=> (t ^ Module.finrank ℝ (L))⁻¹ * (∫ x in a t,Z₁ t x ∂ T.order G)
  let Q₀ : ℝ → ℝ := fun t=> (t ^ Module.finrank ℝ (L))⁻¹ * (∫ x in a t,Z₀ t x ∂ T.order G)
  have hpZ t : ω' t*(C*hatsScale S T σ * Real.exp (-oblige P_B F' n t (v t)))= Υ*C*Tx t := by
    have hh : oblige P_B F' n t (v t)= stanza P_B c (v t)-year X n t := by unfold oblige X year; simp only [smul_eq_mul,mul_neg,Finset.sum_neg_distrib,sub_neg_eq_add]
    unfold Tx; rw [hh]; dsimp only
    rw [mul_left_comm (Real.exp ..),← Real.exp_add,show -(1-stanza P_B c (v t)) + -(stanza P_B c (v t)-year X n t)= -1+year X n t by ring,Real.exp_add]; ring
  have hz' : Fit (n+1) (ω'*Q₀) ((Υ*C) • Tx) := by
    have hb : Bill 0 ω' := life_price ((Real.continuous_exp.continuousAt.comp ((continuousAt_const.sub ((stanza_smooth P_B c).continuous.continuousAt.comp he.continuousAt)).neg)).mono_left nhdsWithin_le_nhds)
    exact ((show Fit (n+1) _ _ from ((by simpa only [zero_add] using h₀.right hb) : Fit (n+1) (ω'*Q₀) (ω'*(fun t=>C*hatsScale S T σ * Real.exp (-oblige P_B F' n t (v t)))))).join (Fit.supply (Eventually.of_forall hpZ) _)) -- parens
  let Pw:= fun t:ℝ=> t^τ
  have hp': ∀ j,Bill 0 (p j) := by
    intro j; induction j using Nat.caseStrongRecOn with
    | zero=> rw [show p 0=(fun t:ℝ=> (1:ℝ)) from funext fun t=> (hx t).2.1]; exact bill_const 1
    | ind j ih=>
      let m (a : ℕ×ℕ) := fun t => a.1 • X a.1 t * p a.2 t
      have Hb : p (j+1)=(↑(j+1:ℕ):ℝ)⁻¹ • ∑ i∈wheel (j+1), m i := by
        funext t; rw [Pi.smul_apply, Finset.sum_apply,show (∑ i∈wheel (j+1),m i t)=_ from ((hx t).2.2 _).symm, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity)]
      rw [Hb]; refine bill_mul (j:=0) (k:=0) (bill_const ((↑(j+1:ℕ):ℝ)⁻¹)) (bill_sum (wheel (j+1)) m (fun i hi=>?_)) -- fix
      by_cases he:i.1=0
      · rw [show m i=(fun _=>0) from funext fun t=>by unfold m; rw [he]; simp]; exact bill_const _
      simpa only [zero_add,m,nsmul_eq_mul] using! bill_mul (bill_mul (bill_const (i.1:ℝ)) (hv i.1)) (ih i.2 (by have hp:= mem_antidiagonal.mp hi; omega))
  have hX : Fit (n+1) (ω'*Q₁) ((Pw*year Y n)*((Υ*C) • Tx)) := by
    have he : (fun j t=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M*ᵥ v t) (v t)) (billow B' E₀ j))= Zone.mul Y p := funext fun j=>funext fun t=> hm (v t) j
    rw [he] at h₁
    have ht:=year_mult hy hp' n
    have hF' : Fit (n+1) (year (Zone.mul Y p) n) (year Y n*Tx) := Fit.join ht.turn (by simpa only [Tx,comp_def,zero_add] using! hw.turn.right (year_bills hy n))
    have H : Fit (n+1) (Pw * year (Zone.mul Y p) n) (Pw*(year Y n*Tx)) := by simpa only [zero_add] using hF'.right (ruler 0 τ (by omega))
    apply h₁.join; apply Fit.join (Fit.supply (g:= (Υ*C) • (Pw*year (Zone.mul Y p) n)) (Eventually.of_forall fun t=> ?_) _); apply Fit.join (H.scale _) (Fit.supply (Eventually.of_forall fun t=> ?_) _)
    all_goals simp only [Pi.smul_apply, Pi.mul_apply,Pw,smul_eq_mul]; ring
  apply Fit.join (Fit.supply (g:= (ω'*Q₁)/(ω'*Q₀)) (eventually_pos.mono fun t ht=> ?_) _)
  swap
  · dsimp only [Pi.div_apply,Pi.mul_apply,Q₀,Q₁]; rw [← mul_assoc,← mul_assoc,mul_div_mul_left _ _ (show _≠0 by positivity)]
  exact shaved n hX hz' (((continuousAt_const.mul htX).tendsto).mono_left nhdsWithin_le_nhds) (by exact (mul_pos hC (Real.exp_pos ..)).ne') (bill_mul (ruler 0 τ (by omega)) (year_bills hy n))
end YM.RG08.Loom
