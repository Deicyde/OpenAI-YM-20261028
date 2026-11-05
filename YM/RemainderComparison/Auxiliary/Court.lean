import YM.RemainderComparison.Auxiliary.Gross

/-!
 # Assemble complement charge with normalization in held test brushes.

 Real aperture parameters exposed (p polygon, R radius, d wick). All finite
 joint orders n ≤ j−1 etc. Constants for same common charts and coupling
 interval (no dependence on V, U, H, or remaining copy, period,
 β through the lane). Complements EXPORT same estimate after interpolation,
 not declaring that hard profile itself has derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {q : Teller G} {c f : Side} {x u s D d a A α : ℝ} {j k l n : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f₁ w p e : ℝ→ℝ}
section pilot
variable {S : StepData c f} (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G)
    (k : S.Choices) (ρ : Bid.Dir G c → AxisChart G F) (B : BudgetPoint) (β : ℝ)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun i:Xs=> represent (tint G _ i))
local notation "Q" => Lapis.gram F T.up T.high ρ k
local notation "g" => gStep β
local notation "R₀" => Pane.virgin T B β
local notation "₾" => weight T F Θ k ρ β

def unperilous (x: Xs) (d C : ℝ) := ‖x‖+d<C
/-- All data on the same requested window. `d` wick multiplier from `opening`.
    hC and stage preparation at point `m` (coarse) verify X etc. Uses clock OP.G. -/
structure Weather (d t gap P U Z : ℝ) (K : KernelChoices) (O : Teller G) (j : ℕ) (x : Xs) (L : Side) : Prop where
  canvas : Quilt T F P
  chartH : LocalRatio Θ
  feed : Intake O T t R₀
  patch : S.patch.L=L
  knobs : S.kernel=K
  cabin : unperilous x (furl G L t) U
  paint : Pilot T F Θ k ρ B β (wick G L d t) (eaves G L t) (furl G L t) gap Z j (gStep β • x)

lemma lane {t β:ℝ} (hp : Intake q T t (Pane.virgin T B β)) (h : S.patch.L=L) : inBand (betaF G t L) β := by
  rw [← h]; have hβ:=hp.height; obtain ⟨ht,hx⟩:=hp.window
  change _ ≤ β at ht; change β≤ _ at hx; constructor <;> linarith

def disburse (H : Config G f→E) (U:ℝ×Xs → Y→E) (D:ℝ) (x:Xs) := scaled_l T F Θ k ρ B β H x - coupon ((Q) 0)⁻¹ (Aux.combo T F Θ k ρ U) D (g,x)
lemma stamp_range {t:ℝ} {x:Xs} {u:ℝ} (h:unperilous x d u) (_ : 0<d) (ha:0<g) (hg:g ≤ 1) (he:g*u ≤ eaves G L t) (y:Xs) (hy:y∈closedBall x d) :
    ‖y‖<u ∧ ‖g•y‖< eaves G L t ∧ ‖g • y-g • x‖≤d := by
  have hh : ‖y-x‖ ≤ d:= mem_closedBall_iff_norm.mp hy
  have hp : ‖y‖<u:= (norm_le_norm_add_norm_sub' ..).trans_lt ((add_le_add_right hh _).trans_lt h)
  rw [← smul_sub, norm_smul,norm_smul,Real.norm_of_nonneg ha.le]; exact ⟨hp,(mul_lt_mul_of_pos_left hp ha).trans_le he,(mul_le_of_le_one_left (norm_nonneg _) hg).trans hh⟩
-- include authorized agreement on halo of this center only (pointwise).
structure Playing (U : ℝ×Xs→Y→E) (H : Config G f → E) (x:Xs) (D d U₀ v p kH : ℝ) (j n : ℕ) : Prop where
  tagGerm : Cloud U D v U₀ j n p
  group : Actual H kH
  speak : ∀ y∈closedBall x d, synced F ρ β H U D y
end pilot

section rates
lemma remains (hA : 0<a) (hd : 0<d) (α : ℝ): Rate G L α fun t=> remain a (wick G L d t) := by
  let r:=a*d^2/8; have hr:0<r:=by unfold r; positivity
  have he := Rate.monitor_cutoff (G:=G) (L:=L) (a:=α) hr (by norm_num : 0<(2:ℝ)); rw [show (fun t=> Real.exp (-r* Delay.fineMonitor G L t ^ (2:ℝ)))=(fun t=> remain a (wick G L d t)) from funext fun i=>by unfold r remain wick; rw [Real.rpow_two]; congr 1; ring] at he; exact he
variable (G) (L) (K : KernelChoices)
set_option maxHeartbeats 500000 in
/-- Complement opacity at ALL normalized probe derivatives used in AUX tests. Width
    U input in rescaled X. Aperture v exact, χ not differentiated in ν; uses one
    order higher on matching chart and actual support. Permit polynomial absolute
    test cap H globally on fine group (for e.g. positive curvature leading marks,
    can alternatively provide with mask multiplied already). `S.kernel` fixed even in
    the filter. Neither chart nor coupling geodesic continued through the masks. -/
theorem curtain {a d φ α:ℝ} (ha:0<a) (hd:0<d) (w q p f r: ℝ→ℝ) (hw:Bolt G L w) (hq:Reserve G L q) (hp:Reserve G L p) (hf:Reserve G L f)
    (hr:Rate G L α r) (hj : j+1 ≤ n) (l : ℕ) :
    ∀ᶠ t in atTop, let v:= Access.apron G L t; let u:= p t; let D:= wick G L d t; let y:= betaF G t L
      ∀ (c f':Side) (S:StepData c f') (T: Tube G S) (F: Forest S.ratio) (Θ: ChartRatio G) (k:S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ) (x:Positions (Uniform.Primary c G)) (O:Teller G), Weather T F Θ k ρ B β d t a (w t) u (q t) K O n x L →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (H:Config G f'→E) (U:ℝ×Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G)→E),
        Playing F ρ β U H x D (furl G L t) (p t) v (f t) (r t) n l →
        Brush j (y^φ) 1 (disburse T F Θ k ρ B β H U D) x := by
  let Z t:= betaF G t L; let v₀:= Access.apron G L; let d₀:= wick G L d
  obtain ⟨fH,hF,Hf⟩:= inside G L n (by omega) q (wick G L d) p hq (Reserve.wig d) hp
  let i:=j+1; obtain ⟨W,hW⟩:= paint_supply G i; obtain ⟨C,hC,hΘ⟩:= Brush.compact (s:=({0}:Set ℝ)) (k:=i) (f:=Real.exp) isCompact_singleton fun t _=> Real.contDiff_exp.contDiffAt
  let N t:= w t*(Fintype.card Axis:ℝ)
  have hN : Rate G L 0 N := hw.uses.mul_right _
  let A t:= oat i (q t) (2*Z t)+oat i (q t) (2*Z t)
  let I t:= clump i (A t) C; let κ t:= prime G K i W C (2*Z t) (N t)
  have hs:Rate G L (1 * i) I:= climbF (oatr i hq.rate) (by norm_num) _ _
  let f' t:= I t * (r t * 3^i * κ t * (fH t+1))*3^i; let P t:= fH t*f t*3^n; let g₁ t:= f' t+P t
  have hP : Reserve G L P:= Reserve.mul (hF.mul hf) (Reserve.const _)
  let a':= 1 * (i:ℝ)+(α + 1*i+ 0)
  have hg:Rate G L (max a' 0) g₁ := (((hs.mul ((((hr.mul_right _).mul (primeR (G:=G) (n:=i) (a:=C) (Z:=W) N K hN))).mul (hF.rate.add (Rate.const 1)))).mul_right _).weaken (le_max_left ..)).add (hP.rate.weaken (le_max_right ..))
  let y:= max a' 0 +1; obtain ⟨B,hB⟩:= Lantern.iteration G L j (a:=1) (by norm_num) (m:=φ) (d:=y)
  have he := (remains ha hd (B-α-1)).mul hr
  filter_upwards [hB,hg y (lt_add_one _),Hf,Access.wide hp.rate,he _ (show B-α-1+α < B by linarith),Delay.shift_pos G L] with t hx hg hm hp' he hz v u D y₀ c f'' S T F Θ k ρ B' β x O h E _ _ _ H U hU
  let g:= gStep β; have hβ:0<β:=h.feed.positive; have hV:β ≤ 2*betaF G t L:=h.patch ▸ h.feed.window.2
  have hθ:=hp'.2 β (lane T B' h.feed h.patch); have hh:‖g‖ < v:= by rw [Real.norm_of_nonneg hθ.1.le]; exact hθ.2
  let Q:= (Lapis.gram F T.up T.high ρ k 0)⁻¹; let f₁:= Germ.primary (Lapis.table F k T.up T.high) (Lapis.mist F Θ T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k)
  have hv: 0< furl G L t:= Real.rpow_pos_of_pos hz _; have hu: 0<u:= lt_trans (add_pos_of_nonneg_of_pos (norm_nonneg x) hv) h.cabin
  have hX : Cloud f₁ D v u n ((n+2)*n) (fH t):= hm _ _ _ _ _ _ hu h.paint.core
  have hL : Cloud (combo T F Θ k ρ U) D v u n ((n+2)*n+l) (P t):= hX.mix hU.tagGerm
  have hY: (Fintype.card (Bond c):ℝ) ≤ N t:= by rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right h.canvas.primary (Nat.cast_nonneg _)
  have hr := hU.group.price; let S':=closedBall x (furl G L t)
  let V:=disburse T F Θ k ρ B' β H U D; let hi:0<g:=hθ.1
  have hh' : g*u ≤ eaves G L t:= by
    have h : v*u ≤ eaves G L t:= by rw [abs_of_pos hu] at hp'; exact hp'.1.2.2.2.le
    exact (mul_le_mul_of_nonneg_right hθ.2.le hu.le).trans h
  have ht w (hx:w∈S'): Brush (j+1) (g₁ t) 1 V w ∧ ‖V w‖ ≤ remain a D*r t := by
    obtain ⟨hp,hf,hX'⟩:= stamp_range (G:=G) β h.cabin hv hi (h.paint.distance.le.trans h.paint.core.small) hh' w hx
    have hh : (g,w)∈Germ.patch (Positions (Uniform.Primary c G)) v u:= (patch_test ..).2 ⟨hh,hp⟩
    have hhK:= temper T F Θ k ρ B' β h.feed h.chartH h.paint hf hX' (holder Q hX.toPicture _ hh)
    let vQ:= scaled_l T F Θ k ρ B' β H; have hv' := hΘ 0 (mem_singleton 0)
    have hn:0≤N t:= (Nat.cast_nonneg _).trans hY
    have hh : Brush (j+1) (f' t) 1 vQ w:= by
      have ht := drenched T F Θ k ρ B' β h.feed hU.group hW hY hv' h.chartH h.paint hf hj hhK
      have hC:= (h.paint.core.curve _ hf).nonneg; have hv := (rung (j:=i) hβ.le hC hV)
      have hs: 0 ≤ clump i (oat i (q t) β + oat i (q t) β) C:= by unfold oat clump; dsimp only; positivity
      have hy:0 ≤ oat i (q t) β:= by unfold oat clump; dsimp only; positivity
      have ht' := primeN (n:=i) (G:=G) S.kernel hβ hV hv'.nonneg hW.1.le hn
      have hs' : 0 ≤ I t:= hs.trans (rising i (add_nonneg hy hy) (add_le_add hv hv) hv'.nonneg)
      have hc:= hX.expense
      apply ht.climb _ le_rfl
      unfold f'
      have H : prime G S.kernel i W C β (N t) ≤ κ t:= by unfold κ; rw [← h.knobs]; exact ht'.2
      have ht'₀:= ht'.1; apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine mul_le_mul (rising i (add_nonneg hy hy) (add_le_add hv hv) hv'.nonneg) ?_ ?_ hs'
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H (by positivity)) (by positivity)
      positivity
    refine ⟨hh.separating ((Trace.trace_arc (holder Q hL.toPicture (g,w) (show (g,w)∈ Germ.patch _ _ _ from (by assumption)))).smaller hj), logarithmic_purse T F Θ k ρ B' β h.chartH h.feed hU.group h.paint hf hX' (hU.speak w hx)⟩
  apply hx _ _ V x (fun i hi=> (ht i hi|>.1).climb ((le_abs_self _).trans hg) le_rfl)
  intro i hi; exact ((ht i hi).2).trans ((le_abs_self _).trans he)
end rates
end YM.RemainderComparison.Aux
