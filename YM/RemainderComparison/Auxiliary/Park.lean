import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Canvas
import YM.RemainderComparison.Gaussian.Cargo

/-!
 # Augment baseline Sienna Canvas receipt. Compact registration window.

 At all x in halo of good x0; x here *unscaled* Lie chart. Factor evaluations
 of z in paid aperture at ACTUAL g. Also charge every dropped profile from
 AUX Laplace chart using stay-complement certificate BEFORE comparing any
 Taylor series. This statement is about the ERASED seed input on AUX for
 synchronized comparison, not the claim that the actual input lacks flagged
 regions. All assertions refer to the same period and ancestor ticket with Cash,
 not replacing the clock trajectory by that of an AUX torus. Use later with
 source weights and aligned flag estimators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {q : Teller G} {c f : Side} {x W y s σ C t v σ' C' : ℝ} {n : ℕ}
section localP
variable {S : StepData c f} (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G)
    (k : S.Choices) (ρ : Bid.Dir G c → AxisChart G F) (B : BudgetPoint) (β : ℝ)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun i:Xs=> represent (tint G _ i))
local notation "p" => Lapis.orbit F ρ
local notation "g" => gStep β
local notation "ϕ" => Lapis.table F k T.up T.high
local notation "ψ" => Lapis.mist F Θ T.up
local notation "₥" => Lapis.gram F T.up T.high ρ k

def piece (x : Xs) (z : Y) : F.Slice G := Fare.draw F (V x) (p x+g • z)
def park (D : ℝ) (x : Xs) := Fare.staying F (p x) g D (V x)
def weight (x:Xs) := Fare.solar F Θ β * Real.exp (-Fare.coverLog F T Θ k ρ β x)
def remain (gap D:ℝ) := Real.exp (-(gap*D^2/4) / 2)
structure Stamp (D a : ℝ) (x : Xs) : Prop where
  basis : ∀ i : S.Choices, ∀ z:Y, ‖z‖ ≤ D → Lapis.table F i T.up T.high (x,p x+g • z)=ϕ (x,p x+g • z)
  inside : ∀ z:Y, ‖z‖ ≤ D → Fare.windmill F (p x+g • z)∈ mouth Θ
  healthy : ∀ z:Y, ‖z‖ ≤ D → flags B.threshold (F.drape (piece F ρ β x z)) = ∅
  exterior : ∫ y in (park F ρ β D x)ᶜ, Fare.overall F T B β (V x) y ∂F.order G ≤ weight T F Θ k ρ β x * remain a D

lemma wear_pos (hβ:0 < β) (hp:LocalRatio Θ) (x:Xs) : 0 < weight T F Θ k ρ β x := mul_pos (Fare.sun F Θ β hβ hp) (Real.exp_pos _)

-- parameter field of core model determined before exponent evaluation
structure Pilot (D u v a C : ℝ) (j : ℕ) (x : Xs) : Prop where
  distance : g < u
  origin : p 0=0
  gap : 0<a
  shore : Germ.cleared ϕ 2 0
  core : Golf ϕ ψ p ₥ j D u u C
  inverse : Germ.Contract (
    (Lapis.gram F T.up T.high ρ k 0)⁻¹) (a/2)⁻¹
  signed : ∀ y, ‖y‖<u → ‖y-x‖≤ v → Stamp T F Θ k ρ B β D a y

lemma origin_ink {s C Λ:ℝ} (hp : T.up.Bounds T.high s C Λ) (h : S.patch.Branches S.kernel G) : Germ.cleared ϕ 2 0 := by
  obtain ⟨hA,hx,hL,-⟩:= Uniform.price_identity F k hp h
  let X := uncurry (tested F k T.high T.up)
  let q:= Uniform.paint F G
  have he : Germ.cleared X 2 0:= by
    intro i hi; interval_cases i <;> ext1 y
    · change X 0=0; exact hx
    rw [iteratedFDeriv_one_apply,show fderiv ℝ X 0=0 from hL]; rfl
  let Z:= combineH (G:=G) F
  have hr: (q ∘ Z) 0=(0,0):= by rw [Function.comp_apply,map_zero]; exact map_zero q -- edit
  exact Germ.chart_cleared X he (hA.of_le le_top) _ 0 hr (q.contDiff.contDiffAt.comp (f:=Z) _ Z.contDiff.contDiffAt) -- types of paint
end localP

/-! Extra provenance extracted at the same proof nodes as `Sienna.reaches`.
    Don't infer `Stamp` (support/choice) from approximation accuracy in
    `receiptS` alone! -/
section buys
variable (Q : ConnectedActivityE6.Target G q) (o : Target.Order G W) {K : KernelChoices}
    (P : Patch) (A : Before G σ C P.J K (n+3)) (p'p p : Clip) (w : ℝ→ℝ) (hk : Bolt G P.L w) (E : FiberFee Q.table ((n+3)+1)) (J : BareRates.pre G σ' C' (n+3)) (e : ℝ) (he : 0<e) (hn : 5 ≤ n+3)
local notation "V₀" => A.tables p P
include hk
lemma rents : Reserve G P.L (fun t=> pam n Q.table p P A (w t) (w t) E (ConnectedActivityE6.loopBill G P.L t)):= by
  -- posts second decomposition
  obtain ⟨_,v,w',h₁,h₂,h⟩:= posts P.L P Q.table p A E hk
  exact Reserve.compare ((Reserve.covers h₁).add ((Reserve.covers h₂).mul Reserve.monitoring)) (Eventually.of_forall fun i=> Eq.le (congr_arg abs (h i)))
include J he hn hk
set_option maxHeartbeats 600000 in
lemma opening : ∃ d:ℝ, 0<d ∧ ∀ᶠ t in atTop, ∀ (c f: Side) (S:StepData c f) (T : Tube G S) (F:Forest S.ratio) (h:S.patch=P) (ht:S.kernel=K), Quilt T F (w t) → T.high=p → T.low=p'p → T.up.Bounds p σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ', T.down.Bounds p'p σ' C' Λ' →
    ∀ ρ: Bid.Dir G c→ AxisChart G F,(warm A h ht).Service F T.high T.up ρ→ ClassicalMatch F T.high T.low T.up T.down ρ →
    ∀ k:S.Choices, ∀ (X : Coat T F), X.x=t → X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m β:ℝ), Cash W t e P.L Q o m T (Pane.virgin T B β)→ B'.threshold=Pressure.temp t →
    flags (Pressure.temp t) X.V=∅ → ∀ x: Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖ < eaves G P.L t → Pilot T F Q.table k ρ B β (wick G P.L d t) (eaves G P.L t) (furl G P.L t) (V₀).gap
      (pam n Q.table p P A (w t) (w t) E (ConnectedActivityE6.loopBill G P.L t)) n x := by
  by_cases h' : 0 < (V₀).gap ∧ 0 < (V₀).horizon ∧ 0 < (V₀).initial ∧ 0 < (V₀).safety
  swap
  · refine ⟨1,zero_lt_one,Eventually.of_forall ?_⟩
    intro t c f S T F h hp hq hk hK hr m' hm' ρ H ha k; subst K; subst P; subst p
    have hS := A.receipt F k hr hq.large rfl rfl|>.1; exact False.elim (h' ⟨hS.pos_m,(show A.Service F T.high T.up ρ from H).x_pos,hS.pos_r,hS.reserveH_pos⟩)
  obtain ⟨l,hl,hL⟩:= Fare.wall G P K (V₀).safety h'.2.2.2; obtain ⟨U,hU,Hu⟩:= Fare.faceM G
  let V:= V₀; let Z:= P.L; let D':= pence U; have hd: 0 < D':= inv_pos.mpr (by positivity)
  have he' := compass P.L Q.table Q.table_exists P p A E hk D' o.ample h'.1 hd (stocksK G n σ' C' J p'p V) C'
  refine ⟨D',hd,?_⟩; filter_upwards [he',pencils (G:=G) (L:=P.L) (n:=n) U V Q.table Q.table_exists hU h'.2.1 h'.2.2.1,
    pressures Z P p A hk D' (K.penalty*l^2/2) (by have h:= K.penalty_pos; positivity), Rate.flame (G:=G) (L:=Z) |>.below (by norm_num) _ hl, Pane.wealthy Q Z he w hk.uses] with t hx hY hh hg hM c f S T F h ht hQ hv hV H h₀ H₀ ρ Hρ hθ k X hX hw hm B B' m β R hT hF x hD hu
  subst K; subst P; subst p; subst p'p; subst t
  have hv : A.Service F T.high T.up ρ:= Hρ
  let t:=X.x; let D:= wick G Z D' t; let w':=w t; let g:=gStep β
  let Y:=eaves G Z t; have hR:=R.laws.intake; have hB : B.threshold=Pressure.fiery G t S.patch.L:= hR.received.temp; have hvx:0<β:=hR.positive
  obtain ⟨hp,hvβ⟩:=hR.window
  have hP:Pigment n V Q.table D (gStep β) U Y t B.threshold (furl G Z t):= by rw [hB]; exact hY β hp
  have hH i (V: Config G c) (Z:F.Slice G):= hL S rfl rfl hQ.large F V Z i
  have hW := hh β hvx hp hQ.one; have hb':B.threshold≤l:= hB ▸ (le_abs_self _).trans hg
  let eB := let a:= stocksK G n σ' C' J T.low (A.tables T.high S.patch);β*(w'*a*‖x‖^5+w'*(C'*B'.threshold^3+C'*B'.threshold^4))+
      (pam n Q.table T.high S.patch A w' w' E (ConnectedActivityE6.loopBill G Z t)+tapir (A.tables T.high S.patch) w'+w'*o.ample/2)
  have hc:= hx eB β hQ.one hvx hvβ _ (Nat.cast_nonneg _) hQ.lever B hB B' (hT ▸ R.laws.data.room.temperatures) ‖x‖ (norm_nonneg _) hu.le rfl
  have hA:= cooler Q o F T k A ρ B B' β E J hv hQ.large H H₀ hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW X R rfl hw hm hT hQ.primary hQ.sizes (hT ▸ hF) (by assumption) hu hθ hn (hM _ hQ.step) hc.1
  have hℓ := mul_le_mul_of_nonneg_right hP.lease.le hP.positive
  let τ:=Before.Service.trailCost V (n+3)
  have hs : (1+τ)*Y+gStep β*D ≤ 1:= le_trans (add_le_add le_rfl hℓ) hP.one.le
  have hΓ := courtyard Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP
  refine ⟨hP.lease, Lapis.zeroO F T.up T.high ρ _ _ A hv,h'.1,origin_ink T F k H hQ.large.1,hΓ,Lapis.wakes F k T.up T.high ρ _ _ _ A hQ.large H hv _ ((show ‖(0: Positions (Uniform.Primary c G))‖ < Y from norm_zero.trans_lt hΓ.pos).trans_le hP.horizon) |>.2.2.1, fun z hy hw'=>?_⟩
  have hh := slack F T k A ρ hv hQ.large H hP.horizon B β (x:=x) (D:=D) hu hvx hs hA hU (Hu F) hP.sermon z hy hw'
  have hX:= rule_it Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW hR hy hh hc.2
  -- shrink and track whole alive region (no interpolation here)
  have heo: Uniform.shade G*(τ*Y + g *D) < Q.table.radius := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add le_rfl hℓ) (Uniform.shade_pos G).le) (hP.count.trans_lt (half_lt_self Q.table_exists.patch))
  have hV:= mouthF F T k A ρ hv hQ.large H hP.horizon Q.table heo hP.booth hy
  have hM := Fare.gamma F T k A ρ hv hQ.large H hP.horizon hP.booth hy (lt_of_le_of_lt (add_le_add le_rfl hℓ) hP.initial)
  let V':= represent (tint G _ z); let p:= park F ρ β D z; have ha':=hX.2; let G':= overall F T B β V'
  have ht := amt F T B β _ q hR V'; have hy := pricing F T Q.table k ρ B β D hΓ hvx hP.lease hQ.large.1 hy hM Q.table_exists hV hh ht.1.meas.stronglyMeasurable
  refine ⟨fun i z hz=>hM z hz i,hV,hh,?_⟩
  change (∫ y in p, G' y ∂F.order G)=_ at hy
  rw [ht.2, ← hy, ← integral_add_compl (show MeasurableSet p from staying_meas ..) (ht.1.integrable (F.order G))] at ha'
  -- full exterior charge in tagged kernel
  
  change (∫ x in p,G' x ∂F.order G)+(∫ x in pᶜ,G' x ∂F.order G)-(∫ x in p,G' x ∂F.order G) ≤ _ at ha'
  simpa only [add_sub_cancel_left] using! ha'
end buys
end YM.RemainderComparison.Aux
