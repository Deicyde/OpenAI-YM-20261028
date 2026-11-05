import YM.RemainderComparison.Auxiliary.Paper
/-!
 # AUX analytic theorem with real Taylor re-expression (not assembly).

 Real positive coupling (level IN lane); actual polynomial denominator at
 zero source, includes every tag, noise Jacobian and mask of the synchronized
 seed-free input. `Queue` normalization retained for RG02 composition algebra
 on this exact common kernel (cumulants follow Taylor precision under the same
 finite polynomial quotient/log). In particular not a vacuum-pressure Taylor
 assertion. Exact separate field-independent scalar readout; no uniform
 infinite-volume global denominator estimate claimed. All costs uniform in
 the Setup; see §Warranty consumers for required calendar budgets on epochs.
 Before seam/support transport. `v` not poly-volume slack for arbitrary torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open YM.RemainderComparison.Exchange
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n : ℕ}
variable {c f : Side} {S : StepData c f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k : S.Choices) (ρ : Bid.Dir G c→AxisChart G F)
variable (B : BudgetPoint) (β : ℝ)
local notation "Q₀" => Lapis.gram F T.up T.high ρ k
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "g₁" => gStep β
local notation "₾" => weight T F Θ k ρ β
local notation "Ω" => faceUp T F Θ k ρ β
local notation "ϕ" => coverLog F T Θ k ρ β
variable (H:Config G f→ℝ) (U:ℝ × Positions (Uniform.Primary c G) → Poll.Body (Precision.Key F G)→ℝ)
local notation "V" => (fun i:Xs=> represent (tint G _ i))

def tower := Real.log (solar F Θ β) - coverLog F T Θ k ρ β 0
def reserve_l (x:Xs) := (Real.log (powder T B β (V (g₁ • x)) H)) - tower T F Θ k ρ β
def trial (r:ℕ): ℝ × Xs → ℝ:= Real.log ∘ model T F Θ k ρ U r - drafting T F Θ k ρ

-- local conditional kernel probability*value operation (normalization in same slot);
-- project on rescaled x variables, arbitrary bounded H before positivity

def divideAux (H':Config G f → E) (x:Xs) :=
    (powder T B β (V (g₁ • x)) H)⁻¹ • powder T B β (V (g₁ • x)) H'
def merchant (r : ℕ) (W:ℝ × Xs→ Y → E) (x:ℝ × Xs):=
    (model T F Θ k ρ U r x)⁻¹ • model T F Θ k ρ W r x

local notation "P₀" => scaled_l T F Θ k ρ B β H
local notation "ζ" => model T F Θ k ρ U
section contract
variable (v u D y C : ℝ) (x:Positions (Uniform.Primary c G))
/-- Local analytic budget. λ model functions fixed and their chart
 estimates before projections; no normalization by the vacuum at
 another torus. Keep Weather and Playing for the DOMAIN and
 exact point-to-clock synchronization. -/
structure Council (r j n l : ℕ) (S₀ C' : ℝ) : Prop where
  room : P₀ x ∈ Set.Icc (1/4:ℝ) 3
  full : 0<powder T B β (V (g₁ • x)) H -- includes boundaries in legal Weather
  scopeC : ∀ w∈Germ.patch Xs v u, ζ r w ∈ Set.Icc (1/2:ℝ) 2
  plain : Queue (model T F Θ k ρ U r) (P₀) g₁ x v u j r C
  inside : Queue (fun w=> (ζ r w)⁻¹) (fun y=> (P₀ y)⁻¹) g₁ x v u j r C
  balance : Queue (trial T F Θ k ρ U r) (reserve_l T F Θ k ρ B β H) g₁ x v u j r C
  nearby (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
     (P:Config G f → E) (W:ℝ × Xs→ Y → E) :
       Playing F ρ β W P x D y u v S₀ C' n l →
       Queue (merchant T F Θ k ρ U r W) (divideAux T B β H P) g₁ x v u j r C
end contract

section split_form
lemma ratio_balance (hβ:0<β) (hO:LocalRatio Θ) (y:Xs) (hp:powder T B β (V (g₁•y)) H≠0) :
    reserve_l T F Θ k ρ B β H y= Real.log (P₀ y) - Ω y := by
  let x:=g₁•y; let q:=₾ x
  have ht := wear_pos T F Θ k ρ β hβ hO x; have h : Real.log q = Real.log (solar F Θ β)-coverLog F T Θ k ρ β x := by
    unfold q weight; rw [Real.log_mul (Fare.sun F Θ β hβ hO).ne' (Real.exp_pos _).ne',Real.log_exp]; ring
  unfold reserve_l scaled_l; rw [smul_eq_mul,Real.log_mul (inv_pos.mpr ht).ne' hp,Real.log_inv,h]; unfold tower faceUp x; ring
lemma ratio_normal (hβ:0<β) (hO:LocalRatio Θ) (H':Config G f → E) (y:Xs) :
    divideAux T B β H H' y = (P₀ y)⁻¹ • scaled_l T F Θ k ρ B β H' y := by
  unfold divideAux scaled_l; let P':= V (g₁ • y)
  let q:= ₾ (g₁ • y); let p:= powder T B β P' H
  have hz : 0<q:= wear_pos T F Θ k ρ β hβ hO _
  rw [show q⁻¹ • p = q⁻¹*p from rfl, _root_.mul_inv_rev,smul_smul,inv_inv,mul_assoc,mul_inv_cancel₀ hz.ne',mul_one] -- rw syntax
end split_form

set_option maxHeartbeats 500000 in
theorem horizon (G : Gauge) (L : Side) (K : KernelChoices) {a d α:ℝ} (ha:0<a) (hd:0<d) (w q p f s: ℝ→ℝ) (hw:Bolt G L w) (hq:Reserve G L q) (hp:Reserve G L p) (hf:Reserve G L f)
    (hr:Rate G L α s) (hj : j+(r+1)+r+2 ≤ n) (l : ℕ) :
    ∃ H: ℝ→ℝ, Reserve G L H ∧ ∀ᶠ t in atTop, let v:= Access.apron G L t; let u:= p t; let D:= wick G L d t
      ∀ (c f':Side) (S:StepData c f') (T: Tube G S) (F: Forest S.ratio) (Θ: ChartRatio G) (k:S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ) (x:Positions (Uniform.Primary c G)) (O:Teller G), Weather T F Θ k ρ B β d t a (w t) u (q t) K O n x L →
      ∀ (P:Config G f'→ℝ) (U:ℝ×Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G)→ℝ),
        Playing F ρ β U P x D (furl G L t) u v (f t) (s t) n l →
        (∀ y:Positions (Uniform.Primary c G), ‖y‖ < u → ∀ z, U (0,y) z=1) →
        Council T F Θ k ρ B β P U v u D (furl G L t) (H t) x r j n l (f t) (s t) := by
  obtain ⟨b,hb,hP⟩:= paying G L K ha hd w q p f s hw hq hp hf hr (show j+(r+1)+r ≤ n by omega) l
  obtain ⟨d',hx,hX⟩:= Exchange.plant j r hb
  let f₁ t:= relay (j+(r+1)) (wick G L d t) (q t) (p t); let f₂ t:= Queue.productPrice j r (d' t) (b t)
  have ht:Reserve G L f₁:= relay_growth _ (Reserve.wig _) hq hp
  let g t:= b t + d' t + (d' t+f₁ t)+f₂ t
  refine ⟨g, (((hb.add hx).add (hx.add ht)).add (product_allow j r hx hb)),?_⟩
  filter_upwards [hP,hX,Access.wide hp.rate,Delay.shift_pos G L] with t hp' he hx hh v u D c f' S T F Θ k ρ B β x O W P U hP h0
  let b':=gStep β; let U':=model T F Θ k ρ U r; let P':= scaled_l T F Θ k ρ B β P
  have ha := hp' _ _ S T F Θ k ρ B β _ _ W
  have h : Queue U' P' b' x v u j r (b t):= ha _ P U hP|>.1
  obtain ⟨hθ,hf,hΨ,hη⟩:= he _ u U' P' x b' h (fun x hx=> model_anchor T F Θ k ρ U r x (h0 x hx))
  have hp: 0<u:= (norm_nonneg _).trans_lt (((patch_test ..).1 h.site).2)
  have hG: b' ≤ 1:= W.paint.distance.le.trans W.paint.core.small
  let q':=weight T F Θ k ρ β (b' • x); let φ y:= powder T B β (represent (tint G _ (b' • y))) P
  have hO := W.chartH; have hβ:0 < β:= W.feed.positive
  have hs: P' x≠0:=ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hθ.1)
  have hg:0 < φ x := by
    have hξ:= lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hθ.1
    change 0 < q'⁻¹ * φ x at hξ; exact pos_of_mul_pos_right hξ (inv_pos.mpr (wear_pos T F Θ k ρ β hβ hO _)).le -- edit
  have hZ:v*u ≤ Sienna.eaves G L t:= by change 0<p t at hp; rw [abs_of_pos hp] at hx; exact hx.1.2.2.2.le
  have ht' := reflection T F Θ k ρ B β W.paint hx.1.2.1.le hZ hx.1.1 hp (show j+(r+1)+2≤ n by omega) hβ h.site
  have hv : 0 ≤ d' t := hΨ.cost; have hy:0 ≤ b t:= h.cost; have hm : 0≤f₁ t:= ht'.cost; have hh:0 ≤ f₂ t := (hη.productQ h hG).cost
  refine ⟨hθ,hg,hf,h.grows ?_,hη.grows ?_,?_,?_⟩
  · change b t ≤ b t+d' t+(d' t+f₁ t)+f₂ t; linarith only [hm,hv,hh]
  · unfold g; linarith only [hm,hv,hy,hh]
  · refine ((hΨ.sub_fit ht').grows ?_).transfer_err ?_
    · change d' t+f₁ t ≤ _; unfold g; linarith only [hm,hv,hy,hh]
    filter_upwards [(h.rough hG).smooth.continuousAt.eventually_ne hs] with y hy
    apply ratio_balance T F Θ k ρ B β P hβ hO y (fun hD=> hy (by change _ * φ y = _; change φ y=0 at hD; rw [hD,mul_zero]))
  intro E _ _ _ _ P₁ W₁ hp
  have H:= hη.productQ (ha _ P₁ W₁ hp|>.1) hG
  apply Queue.transfer_err (P:=fun i=> (P' i)⁻¹ • scaled_l T F Θ k ρ B β P₁ i) (H.grows _) (Eventually.of_forall fun y=> ratio_normal T F Θ k ρ B β P hβ hO _ y)
  change f₂ t ≤ g t; unfold g; linarith only [hm,hv,hy,hh]
end YM.RemainderComparison.Aux
