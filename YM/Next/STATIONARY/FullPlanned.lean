import YM.Next.STATIONARY.Level.Recurse
import YM.Next.STATIONARY.OneLoop.MomentumIntegral

/-!
# ANNULUS certificate delivered.

No momentum-comparison assumed on off-mesh continuation. Coupling update
selector will use this via the pole reduction. RShape and prices explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Supply
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {σ μ C : ℝ}

theorem pouring (G : Gauge) (h : G.Simple) : Fluent G := by
  intro σ ε C Z τ A hs he hC hZ hτ hA
  obtain ⟨k,E,hk,hE,H,hH,hL⟩ := vintageWilson G
  obtain ⟨v,M,hv,hM,Y⟩ := saunter G h σ ε C Z τ A hs hC hZ hτ hA
  let w:= min k v
  have hW : 0<w := lt_min hk hv
  have hx : H.fees w E := hH.less hW (min_le_left ..) le_rfl
  obtain ⟨a,b,ha,hb,V⟩ := astronomy hx hL he hW h C M
  let D := cartWeight *costZone a b
  have hD : 0≤D := by unfold D; exact mul_nonneg cart_weight_pos.le (by unfold costZone; positivity)
  refine ⟨1,D,hD,fun L _ _ m hm B p R Λ hp ht hh hu hX hj=> ?_⟩
  obtain ⟨T,hT,hK,HK⟩ := Y m hm B p R Λ hp ht hh hu hX hj
  let F := T.combine H; let X:=F.cast
  let y := inch L; let G' := amena y G X
  have hs' := hT.less hW (min_le_right ..) le_rfl
  have ht' : F.fees w (M+E) := hs'.pay hx
  have hr : 0<y := inch_pos L; have hsr : y≤1 := inch_le _
  have hx' i : Ticket X (fineFlare p R (m:=m i)) := by
    have hl : AnalyticAt ℝ (intended p R (m:=m i)) 0 := (strain p R hp).analytic
    have hw := ((Wilson_stream G 2).1 (m i))
    have hu := Jar.sequelQ (hl.sub hw) hw (HK i) (hL _)
    rw [sub_add_cancel] at hu
    exact Jar.cast_book ht' _ hu hp
  have hg i : Awards G' (PoleTest p R y (n:=m i)) := gemF (hx' i) hp (hX (m i)) ht (hj i) hr
  let k:= min σ (min w (y*(1/128))) -- qualitative only
  have hg' : 0<k := lt_min hs (lt_min hW (by positivity))
  have hw : k≤min w (y*(1/128)) := min_le_right ..
  have hm' : Play X k := ht'.live.mono (hw.trans (min_le_left ..))
  have he' : B.metric.strip k C := fun i j=> (hh i j).mono (min_le_left ..) le_rfl
  have ha' : HouseWord G B p C ε k C y X := ⟨hm',he',⟨hr,hsr⟩,hw.trans (min_le_right ..),hg', massifTabs hm' hm hx' hp (hX 1) (fun i=>hX (m i)) ht hj he' hr hsr (hw.trans (min_le_right ..)) hg', hX,he⟩
  obtain ⟨z,K,hz,hp',P⟩ := HouseWord.done ha'
  obtain ⟨hY,T'⟩ := profit G' hz hp' P
  refine ⟨profitable G',z/2,K,(fun i=> royalty z K*Real.exp (-(z/4)*(m i).val)), mesh_tend _ hm (by positivity : 0<z/4),hY,fun i=> T' _ _ (hg i), fun i=>?_⟩
  obtain ⟨L₁,L₂⟩ := V (show Orion H w C ε M from ⟨k,y,i,B,p,T,ha',hs',hK⟩)
  have hq : |alphaPay i (profitable G')+G.slopeConstant *Real.log y⁻¹| ≤ D := absoluteGeode i P ha hb hr hsr L₁ L₂
  simpa only [y,inch,inv_inv] using hq

/-- B70 production from external linear estimates (WP Craft.Rack). Includes
RScene glue. The pre-L choices guarded by width≤ / growth≥ and days; exponential refinements to a
 common pre-L rate and unit amplitude by shells. Scope metadata:
 finite c asks measured in coarse-output sites; Λ in Planned still.
 -/
theorem geared (G : Gauge) (hS : G.Simple) (B : MapPrices) (K : KernelChoices) (B₀ : ℕ→ℝ) (he : ∀ i, 0 ≤ B₀ i) :
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → ∃ U : Kin W Y,FullPaths U Q :=
  under_contract G hS B K B₀ he (pouring G hS)
end YM.Stationary
