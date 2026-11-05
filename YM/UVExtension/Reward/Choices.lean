import YM.Next.STATIONARY.Level.Transition

/-! Fixed atom layout and reduced retention pitch in delayed issuance. Variants of the respective
lemmas, same real geometry. These witnesses expose the needed price order. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Exterior Wilson Stationary Precision Bloch Laurent Tree Audience Matrix Filter Function Finset Asymptotics Metric
-- Mathlib scoped
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
private lemma box_unit (G : Gauge) (σ : ℝ) (hs : 0<σ) (t : ℕ) [NeZero t] (ht : 2 ≤ t) :
    ∃ w D : ℝ, 0<w ∧ w≤σ ∧ 0 ≤ D ∧ ∀ m : ℕ → Side, Tendsto (fun i => (m i).val) atTop atTop →
    ∀ (F : ∀ i, Link G (m i) → ℝ) (A : ℝ), (∀ i, Pointwise (F i)) → (∀ i, Rays (t+1) (F i)) →
      0≤A → HasRecord F σ A t → ∃ a : Skin G t, AtomWall (issue a) w (A*D) ∧ ∀ i,
        Rays (t+2) (F i-turnSeries (issue a)) := by
  obtain ⟨η,K,hp,he,hK,H⟩ := strokes G t ht σ hs
  refine ⟨η,K*inkCost G t η,hp,he,mul_nonneg hK (inkCost_nonneg ..),fun m hM F A hh ht ha hR => ?_⟩
  obtain ⟨L,hL,Hm⟩ := hR
  obtain ⟨a,g⟩ := H A L ha (withdrew hM (tendsto_const_nhds (x:=(0:ℝ))) hL (fun i => by simpa only [mul_zero] using (Hm i))
    (fun i => (hh i).analytic) (fun i => (hh i).stained) (fun i => (hh i).guard) (fun i j hj _ =>
      (rays_jet (hh i).analytic _).mp (ht i) j hj))
  obtain ⟨hi,hv⟩ := artery_funded g
  refine ⟨a, ⟨?_, hv⟩,fun i => ?_⟩
  · rw [← mul_assoc]; exact hi
  let R := F i-turnSeries (issue a)
  have hV := stain_ink (issue a) hp hi hv (m:=m i)
  have hX := ((hh i).sub hV).analytic
  have hlow : Rays (t+1) R := (ht i).sub (turns_low _ hp hi)
  refine (rays_jet hX _).2 fun j hj => ?_
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with h|h
  · rw [h,iteratedFDeriv_sub_apply (hh i).analytic.contDiffAt hV.analytic.contDiffAt]
    exact sub_eq_zero.mpr (aperture_eq (colors_align (F i) (hh i).analytic (hh i).lights L a g hp (Hm i))).symm
  exact (rays_jet hX _).1 hlow j h

lemma gateReady (G : Gauge) (σ : ℝ) (hp : 0<σ) : ∃ η C : ℝ, 0 < η ∧ η≤σ ∧ 0 ≤ C ∧ ∀ m : ℕ → Side,
    Tendsto (fun i => (m i).val) atTop atTop → ∀ (F : ∀ i, Link G (m i)→ℝ),
      (∀ i, Pointwise (F i)) → (∀ i, Rays 3 (F i)) → ∀ A, 0 ≤ A → HasRecord F σ A 2 → HasRecord F σ A 3 →
    ∃ X : Skin G 2, ∃ V : Skin G 3, AtomWall (issue X) η (A*C) ∧ AtomWall (issue V) η (A*C) ∧
      ∀ i, Rays 5 (F i-turnSeries (issue X)-turnSeries (issue V)) := by
  obtain ⟨w,K,hk,hu,hK,H⟩ := box_unit G σ hp 2 (by decide)
  obtain ⟨τ,B,hτ,hB,I⟩ := orbit_cost G 3 3 hk
  let a := min σ τ
  have ha : 0<a := lt_min hp hτ
  obtain ⟨v,b,hv,hx,hb,L⟩ := box_unit G a ha 3 (by decide)
  let c := (1+K*B)*b
  have hc : 0 ≤ c := by unfold c; positivity
  refine ⟨min w v, K+c, lt_min hk hv,(min_le_left ..).trans hu,add_nonneg hK hc,fun m hm F hg hh A hA hF hG => ?_⟩
  obtain ⟨X,HX,Hz⟩ := H m hm F A hg hh hA hF
  obtain ⟨D,hd,HD⟩ := I (issue X) (A*K) HX.1
  let E i := turnSeries (issue X) (m:=m i)
  have he i : Pointwise (E i) := stain_ink (issue X) hk HX.1 HX.2
  have hy : HasRecord E a (A*K*B) 3 := HasRecord.mono (show HasRecord E τ (A*K*B) 3 from ⟨D,hd,fun i => HD _⟩) ha (min_le_right ..) le_rfl
  obtain ⟨Y,hY,U⟩ := L m hm (F-E) _ (fun i => (hg i).sub (he i)) Hz (by positivity)
    (((hG.mono ha (min_le_left ..) le_rfl)).sub hy (fun i => (hg i).analytic) (fun i => (he i).analytic))
  have hY' : AtomWall (issue Y) v (A*c) := by
    rw [show A*c=(A+A*K*B)*b by unfold c; ring]; exact hY
  exact ⟨X,Y,HX.mono (min_le_left ..) (by gcongr; linarith),hY'.mono (min_le_right ..) (by gcongr; linarith), U⟩

/-- Operates subtracting at same chart and real metric; buys support at the width
chosen from the target widths and free input H phase prices. `M≥1` is the jet
budget in sup. -/
lemma readyAssembly (G : Gauge) (σ σ₀ : ℝ) (A Z : ℝ) (hs : 0<σ) (hσ : 0<σ₀) (hz : 0≤ Z) :
    ∃ τ C : ℝ, 0<τ ∧ τ≤σ ∧ 0≤C ∧ ∀ (m : ℕ → Side), Tendsto (fun i => (m i).val) atTop atTop →
      ∀ (B : Bed) (p : Clip) (a b : ℝ), B.roots.strip σ₀ A → Floor B p 1 a b → p.direct ≤ Z → ∀ E : ∀ i, Link G (m i) → ℝ, (∀ i, Pointwise (E i)) →
        (∀ i, Rays 3 (E i - inputSeries p (blank B G))) → ∀ M : ℝ, 1 ≤ M → HasRecord E σ M 2 → HasRecord E σ M 3 →
      ∃ X : Skin G 2, ∃ V : Skin G 3, AtomWall (issue X) τ (M*C) ∧ AtomWall (issue V) τ (M*C) ∧
        ∀ f : ℕ → Atom G 2, ∀ i, Rays 5 (E i - intended p (emitBase G B f (issue X) (issue V))) := by
  let k := rowPrice σ₀ A
  obtain ⟨v,P,hv,hP,H⟩ := column_price G 2 k Z hσ hz
  obtain ⟨w,Q,hw,hQ,Y⟩ := column_price G 3 k Z hσ hz
  let a := min σ (min v w)
  have hb : a≤σ := min_le_left ..
  have hh : a≤v := (min_le_right ..).trans (min_le_left ..)
  have he : a≤w := (min_le_right ..).trans (min_le_right ..)
  have ha : 0 < a := lt_min hs (lt_min hv hw)
  obtain ⟨x,J,hx,hX,hJ,D⟩ := gateReady G a ha
  refine ⟨x,(1+(P+Q))*J,hx,hX.trans hb,by positivity,fun m hm B p b z hB hu hp E hE hl M hM HF HG => ?_⟩
  have h0 : 0≤M := zero_le_one.trans hM
  let W := blank B G
  have hW : W.Bounds p σ₀ k 0 := blank_cap hσ hB hu le_rfl le_rfl
  have hc : BankRows W σ₀ k := hW.rows
  obtain ⟨ht,U,hU,hU'⟩ := H p _ _ _ _ hp hW hc
  obtain ⟨hα,S,hS,hS'⟩ := Y p _ _ _ _ hp hW hc
  let F i := inputSeries p W (m:=m i)
  have hs i : Pointwise (F i) := stain_knit _ _ hW
  have hm' : HasRecord F v P 2 := ⟨U,hU,fun i => hU' _⟩
  have hm'' : HasRecord F w Q 3 := ⟨S,hS,fun i => hS' _⟩
  obtain ⟨X,V,h₁,h₂,h₃⟩ := D m hm (E-F) (fun i => (hE i).sub (hs i)) hl (M+P+Q) (by positivity)
    ((((HF.mono ha hb le_rfl)).sub (hm'.mono ha hh le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
    ((((HG.mono ha hb le_rfl)).sub (hm''.mono ha he le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
  have hC : (M+P+Q)*J ≤ M*((1+(P+Q))*J) := by rw [← mul_assoc]; gcongr; nlinarith [mul_nonneg (sub_nonneg.mpr hM) (add_nonneg hP hQ)]
  refine ⟨X,V,h₁.mono le_rfl hC,h₂.mono le_rfl hC,fun f i => ?_⟩
  rw [intent]
  convert h₃ i using 1
  change _- (F i + turnSeries (issue X) + turnSeries (issue V))=E i-F i-_-_
  abel

lemma chooseSym (G : Gauge) (hG : G.Simple) (σ : ℝ) (hs : 0<σ) :
    ∃ η K : ℝ, 0<η ∧ η ≤ σ ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop →
    ∀ U : ∀ i, Link G (m i)→ℝ, ∀ W T : ∀ i, Link G (m i)→ℝ,
    ∀ (A B M : ℝ) (ε : ℕ → ℝ) (f g : Picture G 1) (R : FaceRow) (i : G.ColorIndex),
      0≤A → 0≤B → 0≤M → Tendsto ε atTop (𝓝 0) → R.strip σ M → R.read 0=1 →
      (∀ i,Pointwise (U i) ∧ Pointwise (W i) ∧ Pointwise (T i)) →
      (∀ i j,Firm σ A (f i j) ∧ Firm σ B (g i j) ∧ Rays 4 (g i j ∘ axes)) →
      (∀ i,Recorded (slots R G) (T i) 0 ∧ Recorded f (U i) (cents (m i)*ε i) ∧ Recorded g (W i) 0) →
    ∃ Q : Skin G 1,
      let a := alphaPay i f
      AtomWall (issue Q) η ((A + |a| * bedCharge σ M+B)*K) ∧ Bs G (issue Q) ∧
      ∀ i, aperture (cents (m i)*ε i) (turnSeries (m:=m i) (issue Q)) (U i-a • T i + W i) 1 := by
  obtain ⟨η,C,hh,hη,hC,H⟩ := veins G σ hs
  refine ⟨η,C*inkCost G 1 η,hh,hη,mul_nonneg hC (inkCost_nonneg ..),fun m hm U W T A B M ε f g R i hA hB hM he hR hg hP hF hu => ?_⟩
  let a := alphaPay i f
  let V := fun i => U i-a • T i
  let p := f-(a:ℂ) • slots R G
  let u := A + |a| * bedCharge σ M
  have hE (i) : Recorded p (V i) (cents (m i)*ε i) :=
    Recorded.less (F:=U i) (H:=a • T i) (hP i).1.analytic (((hP i).2.2.coin a).analytic) (hu i).2.1
      ((hu i).1.weigh a (hP i).2.2.analytic)
  have hT i j : Firm σ u (p i j) := by
    have hh := ((hF i j).1).sub ((Firm.const (α:=Keys 1) hs (a:ℂ)).mul (slots_cost hs hR i j))
    rw [Complex.norm_real, Real.norm_eq_abs] at hh; exact hh
  have hV (i) : Pointwise (V i) := (hP i).1.sub ((hP i).2.2.coin a)
  have h' := point_receipt hG hm (fun i j => (hF i j).1) he (fun i => (hu i).2.1) (fun i => (hP i).1)
  have hp := point_receipt hG hm hT he hE hV
  have hx : leapTip p (step (0:Axis)) 1 ![i,i]=0 := subtract_fee i h' hR hs hg rfl
  have hw k j := hp.vanish hG 1 0 (by decide) i hx k j
  have hF' i j : Firm σ (u+B) ((p+g) i j) := (hT i j).add (hF i j).2.1
  have hz i := Recorded.both (hV i).analytic ((hP i).2.1).analytic (hE i) (hu i).2.2
  have H' := point_receipt hG (F:=V+W) hm hF' he hz (fun i => (hV i).add (hP i).2.1)
  obtain ⟨Q,hQ,hO⟩ := H (u+B) 2 (p+g) (by unfold u; have hp := bedCharge_nonneg (σ:=σ) hM; positivity) H'.toFeatures (fun i j => (hw i j).add (hF i j).2.2)
  obtain ⟨hi,hb⟩ := artery_funded hQ
  refine ⟨Q,⟨by rw [← mul_assoc]; exact hi,hb⟩, fun i x R hv => issue_normal hQ.price hh hO R hv i x,?_⟩
  intro i
  have hh' := (hV i).add (hP i |>.2.1)
  exact colors_align _ hh'.analytic hh'.lights (p+g) Q hQ hh (hz i)

theorem colorReady (G : Gauge) (hG : G.Simple) (σ w M Z : ℝ) (hs : 0<σ) (hw : 0<w) (hz : 0≤Z) :
    ∃ s K D : ℝ, 0<s ∧ s≤min σ w ∧ 0≤K ∧ 0≤D ∧ ∀ (c f : ℕ → Side), Tendsto (fun i => (c i).val) atTop atTop →
    ∀ (S : ∀ i, StepData (c i) (f i)) (F : ∀ i, Forest (S i).ratio) (t : ∀ i, (S i).Choices), (∀ i, Bid.Larger (G:=G) (S i)) →
    ∀ (p q : Clip) (B C : Bed) (U : PathData G) (ρ : ∀ i, Bid.Dir G (c i) → AxisChart G (F i)) (P : ChartRatio G) (μ τ A Λ η x y z u : ℝ), q.direct ≤ Z → LocalRatio P → 0<μ → 0<η →
      U.Bounds p τ A Λ → Attached B U → (∀ i, PriceGap (F i) p U η ∧ Critical (F i) p U (ρ i) ∧ Bid.HeatG (F i) p U (ρ i) C) →
      (∀ i, Floor B p (f i) x y ∧ Bid.Sworn B (f i) G) → (∀ n : Side, Floor C q n z u) → (∀ i, Bid.Sworn C (c i) G) →
      C.metric.strip w M → C.roots.strip w M →
    ∀ (L α : Picture G 1) (X Φ R : ℝ) (ε : ℕ → ℝ) (i : G.ColorIndex), Tendsto ε atTop (𝓝 0) → (∀ i, 0 ≤ ε i) → 1≤X →
      HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 2 → HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 3 →
      (∀ i j,Firm σ Φ (α i j) ∧ Firm σ R (L i j) ∧ Rays 4 (L i j ∘ axes)) →
      (∀ i, Recorded α (honorarium (F i) (t i) μ p U (ρ i)) (cents (c i)*ε i) ∧ Recorded L (burnished (F i) U (ρ i)) 0) →
    ∃ (T : PathData G) (g : Skin G 1)(wq : Skin G 2)(e : Skin G 3), T=emitBase G C (issue g) (issue wq) (issue e) ∧
      T.row=rowPath C ∧ Attached C T ∧ (∀ s' A' Λ', 0<s' → s'≤s → rowPrice w M ≤ A' → X*K ≤ A' →
        (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D ≤ Λ' → T.Bounds q s' A' Λ') ∧
      (∀ i, ClassicalMatch (F i) p q U T (ρ i)) ∧ ∀ j (Θ g Ω : ℝ), waveBank G*ε j ≤ Θ*Ω*Real.exp (-g * (c j).val) →
        FiniteBound (F j) U T p q (alphaPay i α) P (ρ j) Θ g Ω := by
  let s := min σ w
  have hS : 0<s := lt_min hs hw
  obtain ⟨a,K,ha,h₁,k,I⟩ := readyAssembly G σ w M Z hs hw hz
  obtain ⟨b,D,hb,h₂,d,Q⟩ := chooseSym G hG s hS
  refine ⟨min a b,K,D,lt_min ha hb,(min_le_right ..).trans h₂,k,d,?_⟩
  intro c f hm S F t h p q B C U ρ P μ τ A Λ η x y z u ht hP hg hη hu he H HY hF hx hW hR L α X Φ R ε i hε hv hX hh ho hK hz
  let f0 (i) := victory (F i) (t i) p U (ρ i)
  let f1 i := honorarium (F i) (t i) μ p U (ρ i)
  let f2 i := burnished (F i) U (ρ i)
  have hl j := campaign (H j).2.1 (h j).1 hu (t j) (H j).1 hη hg hP
  let V := blank C G
  have hf : V.Bounds q w (rowPrice w M) 0 := blank_cap hw hR (hF 1) le_rfl le_rfl
  obtain ⟨D3,D4,hD3,hD4,hE⟩ := I c hm C q z u hR (hF 1) ht f0 (fun i => (hl i).1) (fun j => violet (h j) (H j).2.1 (H j).2.2 hu he (HY j).1 (HY j).2 hf (rows_layout rfl) (hF _) (hx j) _) X hX hh ho
  have hp (j) := low_columns hf (rows_layout rfl) (hF _) (hx j)
  let i' : Ink G 2 := fun _ => i
  have hr := hK i' (fun _ => coord 0)
  have hM : 0 ≤ M := (price_step_metric hw hW (plaquette ⟨(0,1),by decide⟩) (plaquette ⟨(1,2),by decide⟩)).budget_nonneg
  obtain ⟨g,H',hx',Hz⟩ := Q c hm f1 f2 (fun j => inputSeries q V) Φ R M ε α L C.metric i hr.1.budget_nonneg hr.2.1.budget_nonneg hM hε (fun i j => (hW i j).mono (min_le_right ..) le_rfl) (hF 1).starts (fun i => ⟨(hl i).2.1,(hl i).2.2,stain_knit V q hf⟩) (fun i j=> ⟨(hK i j).1.mono hS (min_le_left ..) le_rfl,(hK i j).2.1.mono hS (min_le_left ..) le_rfl,(hK i j).2.2⟩) fun j => ⟨according (C.metric.rights w M hW hw.le) (hp j).2.2,hz j⟩
  let T := emitBase G C (issue g) (issue D3) (issue D4)
  let Z := (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D
  have hΛ (s' A' Λ') (hp : 0<s') (hb : s'≤min a b) (hu : rowPrice w M ≤ A') (hz : X*K≤A') (hv : Z≤Λ') : T.Bounds q s' A' Λ' := by
    have hm : s'≤w := (hb.trans ((min_le_right ..).trans h₂)).trans (min_le_right ..)
    have hg := H'.mono (hb.trans (min_le_right ..)) hv
    exact build_cap C hp (fun i j => (hR i j).mono hm le_rfl) (hF 1) (le_trans (show rowPrice s' M ≤ rowPrice w M by unfold rowPrice; gcongr) hu) hg.1 (hD3.mono (hb.trans (min_le_left ..)) hz).1 (hD4.mono (hb.trans (min_le_left ..)) hz).1 (fun i => ⟨hg.2 _, hD3.2 _,hD4.2 _⟩) (fun i x => hx' i x T rfl)
  have hT := hΛ (min a b) (max (rowPrice w M) (X*K)) Z (lt_min ha hb) le_rfl (le_max_left ..) (le_max_right ..) le_rfl
  exact ⟨T,g,D3,D4,rfl,rfl,rows_layout rfl,hΛ,fun j => achieved (h j).1 (H j).2.1 hu hT _ (H j).1 hη (hE (issue g) j),fun j Θ W Ω hg' => draft_pipe (t j) (H j).2.1 (h j).1 hu hT (H j).1 hη hg hP (hv j) (Hz j) _ _ _ hg'⟩
end YM.UVExtension.Reward
