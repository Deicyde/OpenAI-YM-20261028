import YM.Next.STATIONARY.Level.Transition
import YM.FullVolume.Canvas.Return
/-! Adapt Index-assembly quantization Scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η θ γ A A' ℓ V K' : ℝ} {m n : ℕ → Side}
lemma rampInvoice (d : ℝ) (x y : ℝ) {Λ' Λ C B : ℝ} (hd : 0 ≤ γ) (hx : 0 ≤ V) (hΛ : 0 ≤ Λ) (h : Λ/128 ≤ Λ')
    (hp : 2*((C+(d+|y|)*V)*γ) ≤ Λ') (he : |x+y|+1≤d) (hw : B*γ≤1/256) : (C+|x| *V+B*Λ)*γ ≤ Λ' := by
  have hY := driving_abs _ _ _ he
  calc
    _ = (C+|x| *V)*γ+(B*γ*Λ) := by ring
    _ ≤ Λ'/2 + Λ'/2 := add_le_add ((mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right hY hx) _) hd).trans (by linarith)) (by nlinarith only [hw,h,hΛ])
    _ = _ := by ring

def Fluxed (G : Gauge) (K : KernelChoices) (J : ℕ) (ε w D Z δ C Z' A τ κ d s γ : ℝ) (R1 : Reel G) (u : ℕ) (β Λ₀ : Side → ℝ) := ∀ (m n : ℕ→Side) (P : Patch) (X : Armada m n P K)
        (p q : Clip) (R : PathData G) (F : ∀ i,Forest (X.boot i).ratio) (g : ∀ i, fieldDir G (m i) 1 → AxisChart G (F i))
        (B T : Bed) (V : Towers P.L) (Λ eps η : ℝ) (L : ChartRatio G), P.J=J → u ≤ P.L.val → Tendsto (fun i=>(m i).val) atTop atTop → p.direct ≤ Z → q.direct ≤ Z' → Scud X G p q R F g w τ D A D ε Λ δ C eps B T V η → 1≤Λ → 0<η → LocalRatio L →
    ∃ Y : PathData G,∃ α : ℝ,Y.row=rowPath T ∧ Attached T Y ∧ (∀ η' A' Λ', 0<η' → η'≤s → κ≤A' → Λ₀ P.L ≤ Λ' → Λ/128 ≤ Λ' → Y.Bounds q η' A' Λ' ∧ R1.Wing m Y A' Λ') ∧
        |α+G.slopeConstant * Real.log P.L.val|+1 ≤ d ∧ (∀ i, ClassicalMatch (F i) p q R Y (g i)) ∧ ∀ Θ c', β P.L ≤ Θ → c'≤γ → ∀ i, FiniteBound (F i) R Y p q α L (g i) Θ c' 1

set_option maxHeartbeats 2000000 in
theorem flux_cap (G : Gauge) (i : G.ColorIndex) (hS : G.Simple) (r : KernelChoices) (J : ℕ) (ε w D Z δ C Z' : ℝ) (he : 0<ε) (hw : 0<w) (hd : 0≤D) (hz : 0≤Z)
    (hδ : 0<δ) (hC : 0≤C) (hZ : 0≤Z') : ∃ (R1: Reel G), ∃ κ s : ℝ,0 ≤ κ ∧ 0<s ∧ R1.Price s ∧ ∀ τ A,0<τ → 0≤A → HorizCalc G w ε D Z τ A →
    ∃ d γ : ℝ, ∃ u : ℕ, ∃ β Λ₀ : Side→ℝ, 0≤d ∧ 0<γ ∧ Fluxed G r J ε w D Z δ C Z' A τ κ d s γ R1 u β Λ₀ := by
  -- width depends on pregrants only. clip constants funded BEFORE A.
  let F := cabinTicket G D
  have hF : 0≤F := le_trans (Real.exp_pos _).le (cabin_paid G hd)
  obtain ⟨w₀,b,Y,E,hb,hw₀,ht,hV,hY,hE,ha,H⟩ := honored G r J (min w δ) ε D F he (lt_min hw hδ) hd hF
  have hr := hb.trans_le hw₀
  have hx : w₀ ≤ 1 := by linarith
  have hb' : b≤1 := hw₀.trans hx
  obtain ⟨a,c,ha₀,hc,U⟩ := setWest G w b D Z D ε hw hb hb' hz hd J r
  let t := min (min (surfHeight 2 b) (surfHeight 3 b)) (min (surfHeight 1 w₀) (b/2/2))
  have hL : 0<t := lt_min (lt_min (surf_gradient hb _) (surf_gradient hb _)) (lt_min (surf_gradient hr _) (by positivity))
  have hl : t≤ min (surfHeight 2 b) (surfHeight 3 b) := min_le_left ..
  have hL' : t ≤ min (surfHeight 1 w₀) (b/2/2) := min_le_right ..
  let M := 1 + (a+1)/6+((c+1)+3*((a+1)*(E*(a+1))))/24
  have ht1 : 0≤ (c+1)+3*((a+1)*(E*(a+1))) := by positivity
  have hM : 1≤M := by unfold M; linarith
  obtain ⟨R1,s,k,l,hs,h,hP0,he',hv',I⟩ := pierce G hS t δ C Z' hL hδ hZ
  refine ⟨R1,max (M*k) (rowPrice δ C),s,le_trans (mul_nonneg (zero_le_one.trans hM) he') (le_max_left ..),hs,hP0,fun τ A hτ hA HQ => ?_⟩
  obtain ⟨L,N,hN,Rq⟩ := HQ
  obtain ⟨t₀,S₀,T₀,hT,h₂,h₃,G₀⟩ := U τ A hτ hA
  obtain ⟨t',K,h₄,h₅,H₂⟩ := tideMark G w D ε Z τ A hw hd hz hτ hA
  obtain ⟨tL,C₀,hl',hc₀,G₁⟩ := bequest G w₀ D τ hr hd hτ
  let Ξ := feeHead (fun n=> roundBay G (n+1) (Shirley n) K w₀ ((ruffle D)^(n+2)))
  let d := |biteCost (b/2) (reserveCost G E (mealCap G J F Y Ξ r.penalty) (barkPay G J F Y r.penalty))|+N+1
  let P (u : Side) := (u.val:ℝ)^4 * feast G J F Y Ξ r.penalty E
  let β (u : Side) := |waveBank G * royalty (b/2) (P u)|
  let B := bedCharge (min t δ) C
  let Λ₀ (u : Side) := 2*((P u+(d+|G.slopeConstant*Real.log u.val|)*B)*l)
  obtain ⟨W,hW⟩ := age_control t₀ t' tL w C₀ l 64 S₀ T₀ w₀ hc₀ hv' (by norm_num) hT h₄ hl' hw
  refine ⟨d,b/2/4,max L W,β,Λ₀,by unfold d; positivity,by positivity,fun m n X M' p q R FF ρ T T' V Λ ε' η LQ hj hu hy hp hq Fd hEn hη hΦ => ?_⟩
  have hg : X.Branches r G := (Fd.ample 0).1
  obtain ⟨ht0,hj₀,hK₀,hK',hJ,hj',hΛ'⟩ := hW X.L ((le_max_right ..).trans hu)
  have h₀ := Fd.hill1; have h₁ := Fd.hill2
  have Hg := tendsto_atTop_mono (fun i=> (show (m i).val ≤ (n i).val from by rw [M'.binds]; exact Nat.le_mul_of_pos_right _ X.L.pos)) hy
  let tQ (i : ℕ) : (M'.boot i).Choices := Classical.arbitrary _
  let dM (i) := installed (M'.boot i).ratio V.A0
  let Φ := moonlit G X V.A0
  have HH : 0≤ Λ := zero_le_one.trans hEn
  have hcP : T.metric.strip (inch X.L*w₀) D := fun i j=> (h₀.1 i j).mono hK' le_rfl
  have hxW : w₀ ≤ w := ht.trans (min_le_left ..)
  have hx' : Cruise Φ 2 w₀ D := (Fd.legs.cruise G hw hd).less hxW
  have hv i : Premise (M'.boot i) (dM i) Φ := launchBridge _ G (V.A0.rights w _ (Fd.legs [] (by decide)) hw.le)
  obtain ⟨V',Ha,Ht⟩ := H₂ n Hg p R T Λ hp Fd.funded Fd.attached (fun i=> h₀.2.2.1 _) h₀.2.2.2 h₀.1
  let M'' := arriving Φ
  let Y' := RippleF V' Φ
  let Q : PostCard R p X r M'' Y' m n:= garden M' tQ dM hv Fd.funded (fruit_mono Ha hj₀ le_rfl) Ht hr
  let Q' : TicketPost Q η T T' := ⟨FF,ρ,dM,fun _=>rfl, fun i=>(Fd.trial i).trial, Fd.critical, Fd.wind, Fd.educated⟩
  have Hᵥ := cruise_event (G:=G) (Q:=V) (P:=X) Fd.legs hxW hw hd
  have HL : Spotlight X M'' w₀ F := hx'.stars hx
  have HD : Keels Y' w₀ Ξ := cooking Hᵥ hx hr h₅ (fruit_mono Ha hj₀ le_rfl)
  have Hv := H X hj hg p R m n (Loc G 1) M'' Y' T Q hy τ A Λ Ξ D Fd.funded Fd.attached hcP h₀.2.2.1 h₀.2.2.2 HL HD
  obtain ⟨Q₂,Q₃,hc2,hc3,h4,h5,h6⟩ := G₀ m n Hg p R T Λ hp Fd.funded Fd.attached h₀.1 (fun i=> h₀.2.2.1 _) h₀.2.2.2 X hj hg ((mul_le_mul_of_nonneg_left hw₀ (inch_pos _).le).trans ht0) M' tQ Φ (hx'.less hw₀)
  let F0 := fun i => victory (FF i) (tQ i) p R (ρ i)
  have Hx := (medals_right hg hr HL (ha _) Y' HD).covered.tab.skinny hw₀
  obtain ⟨hx2,hx3⟩ := exchangeYield Q' hg Fd.funded hη hb (celestial_flag (hx'.less hw₀).1) hv hc2 hc3 (h4.thin le_rfl (add_le_add_right hJ a)) (h5.thin le_rfl (add_le_add_right hj' c)) Hx Hv hE h6
  obtain ⟨Y₀,g0,hξ⟩ := G₁ m n hy X r hg p T T' R M'' Y' Q η δ ε C A Λ D Q' Φ Fd.funded HH hx' hv h₁.1 hδ hcP h₀.2.2.1 he hK₀
  obtain ⟨X1,X2,K1,K2,HΔ⟩ := quoting Q' hη hb hw₀ hV hδ hg hS h₁.1 hy Fd.funded HL (ha _) HD Hv hE i
  rw [hj] at K1 K2 HΔ X1 X2
  obtain ⟨Yπ,ν,Eπ,e,Hπ,hπ,YH,YZ⟩ := Rq X.L ((le_max_left ..).trans hu) X.odd_side n Hg T p R Λ Fd.funded Fd.attached h₀.1 hp h₀.2.2.1 h₀.2.2.2
  -- pad common M. Verify real support Q'
  have hK1 : T.metric.strip (inch X.L*w₀) (max D C) := fun i j=> (hcP i j).mono le_rfl (le_max_left ..)
  have hK2 : T'.metric.strip w₀ (max D C) := fun i j=> (h₁.1 i j).mono (ht.trans (min_le_right ..)) (le_max_right ..)
  rw [pole_reduced Q' hS hx'.1 hr Fd.funded hK2 hK1 X2 h₀.2.2.1 he h₀.2.2.2 Fd.attached hv (half_pos hb) hy i hπ Hπ YH] at HΔ
  let a0 := profitable (medalCue M'' r.penalty Y'); let α := alphaPay i a0; let F := G.slopeConstant*Real.log X.L.val
  have hz : |α+F|+1 ≤ d := by
    have he := le_trans HΔ (le_abs_self _)
    change |α-alphaPay i Yπ| ≤ _ at he
    apply add_le_add_left _ 1
    calc
      |α+F|= |(α-alphaPay i Yπ)+(alphaPay i Yπ+F)| := by rw [← add_assoc,sub_add_cancel]
      _ ≤ _ := (abs_add_le ..).trans (add_le_add he (YZ i))
  let S i := M'.boot i
  let E' := iceBank G
  let f := fun i=> royalty (b/2) (P X.L)*Real.exp (-(b/2/4)*(m i).val)
  let R₀ := (inch X.L^2*(Λ*C₀))
  have hkE : 0 ≤ P X.L := (K1 ![i,i] ![coord 0,coord 0]).budget_nonneg
  have hkR : 0 ≤ royalty (b/2) (P X.L) := by unfold royalty; positivity
  have hD : 0≤ B := bedCharge_nonneg hC
  obtain ⟨R',H1,H',hk',hPx,hP⟩ := I m n hy S FF tQ Fd.ample p q T T' R ρ LQ (inch X.L) τ A Λ η ε D ε' C hq hΦ (inch_pos _) hη Fd.funded Fd.attached
    (fun i=> ⟨Fd.wind i,Fd.critical i,Fd.heat i⟩) (fun i=> ⟨h₀.2.2.1 _, h₀.2.2.2 i⟩) h₁.2.2.1 h₁.2.2.2 h₁.1 h₁.2.1 Y₀ a0 M (P X.L) R₀ f i (mesh_tend _ hy (by positivity)) (fun i => by unfold f; positivity) hM
    (hx2.mono hL (hl.trans (min_le_left ..)) (by unfold M; linarith))
    (hx3.mono hL (hl.trans (min_le_right ..)) (by unfold M; linarith))
    (fun i j=> ⟨(K1 i j).mono hL (hL'.trans (min_le_right ..)) le_rfl, ((hξ i j).1).mono hL (hL'.trans (min_le_left ..)) le_rfl,(hξ i j).2⟩) (fun j=> ⟨K2 j,g0 j⟩)
  refine ⟨R',α,H1,H',fun x A' Λ' hx hy hb he ht=> hk' x _ _ hx hy ((le_max_right ..).trans hb) ((le_max_left ..).trans hb) ?_, hz,hPx,fun y c u H i=> hP i y c 1 ?_⟩
  · have hu : R₀=inch X.L^2*C₀*Λ := by unfold R₀; ring
    have ht : inch X.L^2*C₀*l≤1/256 := by linarith [hΛ']
    rw [hu]; apply rampInvoice d α F hv' hD HH ‹Λ/128≤Λ'› he hz ht
  exact winter_exp 1 y (royalty (b/2) (P X.L)) (waveBank G) c (b/2/4) le_rfl u _ H
end YM.Stationary
end
