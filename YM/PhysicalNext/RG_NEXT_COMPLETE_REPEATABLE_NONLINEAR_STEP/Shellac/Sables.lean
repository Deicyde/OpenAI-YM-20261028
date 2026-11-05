import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Mars
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Smug
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Purple
/-!
# FULL PURE residual on authentic virtual periods, near 0 real links, with same n Kin station
 Critical/remainder hypotheses purchased downstream, hold all t. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {σ σ' C C' U W : ℝ} {K : KernelChoices} {T' : Teller G} {J : ℕ}
variable (P : Patch) (Q : ConnectedActivityE6.Target G T') (o : Target.Order G W)
    (n : ℕ) (M : Push.Uniform.Before G σ C P.J K ((n+1+2)+3)) (R : FiberFee Q.table (((n+1+2)+3)+1))
    (Z : BareRates.pre G σ' C' (n+1+2)) (T : BareRates.pre G σ' C' ((n+1+2)+3))
local notation "L" => P.L
variable {g h : ℝ→ℝ} {Θ γ : ℝ} (b b' : Clip) (hk : 2 ≤ n) (hv : Bolt G P.L g) (hr : Rate G P.L 0 h) (hΘ : 0< Θ) (hγ : 0< γ)
local notation "x₀" => eaves G L
local notation "m" => furl G L
local notation "M₀" => M.tables b P
local notation "H₀" => (fun t=> pam (n+1+2) Q.table b P M (g t) (g t) R (ConnectedActivityE6.loopBill G L t))
include hk hv hr Z T R hΘ hγ
set_option maxHeartbeats 360000 in
lemma erudite (V a : ℝ) (hA : 0<a) :
    ∀ᶠ t in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (hp:S.patch=P) (ht:S.kernel=K) (_k:S.Choices) (B B' : BudgetPoint), Stores.till t ≤ c.val → B'.threshold=Pressure.temp t → Quilt T F (g t) → T.high=b → T.low=b' → T.up.Bounds b σ C (ConnectedActivityE6.loopBill G L t) → T.down.Bounds b' σ' C' (h t) →
    ∀ (ρ:Bid.Dir G c→ AxisChart G F) (α γ' : ℝ), (Sienna.warm M hp ht).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → FiniteBound F T.up T.down T.high T.low α Q.table ρ Θ γ γ' → 0 ≤ γ' → γ' ≤ h t → |α|≤ |V| →
    ∀ β p : ℝ,Cash W t a L Q o p T (Pane.virgin T B β) → ∀ X:Coat T F, X.x=t → X.width=o.K → X.manifest → flags (Pressure.temp t) X.V=∅ → ∀ x:Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖+2*furl G L t < x₀ t →
        0 < tramp T B β x∧ Brush n ((betaF G t L)^ (-(23/20:ℝ))) (x₀ t)⁻¹ (off (harmony T B β α)) x:= by
  let U :=P.L
  by_cases h₀ : 0 < (M.tables b P).gap
  swap
  · refine Eventually.of_forall fun t c f S T F hp ht k B B' hv hx hq ha hB h𝒦=> False.elim ?_
    subst K; subst P; subst b
    exact h₀ (M.receipt F k h𝒦 hq.large rfl rfl).1.pos_m
  obtain ⟨d,hd,hD⟩:= reaches Q o P M b' b g hv R T a hA (by omega)
  obtain ⟨X,hX,hY⟩:= languid (C:=C) (σ:=σ) (K:=K) Q.table Q.table_exists (M₀) n d (-2) (posts P.L P Q.table b M R hv).1 hv hd h₀
  filter_upwards [hD,hY,pole Θ γ V hΘ hγ ((posts P.L P Q.table b M R hv).1) hX hv.uses hr b' Z] with t hD hY hx c f S T F hp ht k B B' hh hvI hQ hk' hT hz he ρ α p hρ ha HM hP heP hI β e D Y hK he' hm hh' x hν hΞ
  have hβ:=D.laws.intake
  subst K; subst P; subst b; subst b'
  let Q' := Q.table; let C₀ := M.tables T.high S.patch; let D₀ := pam _ Q.table T.high S.patch M (g t) (g t) R (ConnectedActivityE6.loopBill G S.patch.L t)
  let m' := furl G U t
  let A:=eaves G U t; let y:= betaF G t U; have hs:1<y := hβ.height; have hm':0 < m' := Real.rpow_pos_of_pos (zero_lt_one.trans hs) _
  have h₃ : ¬ y<0:=not_lt.mpr (by linarith)
  have hk' : ‖(0:Positions (Uniform.Primary c G))‖ + 2*m' < A:= by rw [norm_zero]; exact lt_of_le_of_lt (add_le_add (norm_nonneg _) le_rfl) hΞ
  have hr' := hD c f S T F rfl rfl hQ rfl rfl hz _ he ρ hρ ha k
  have hρ : M.Service F T.high T.up ρ:=hρ
  have hF x (hx : ‖(x:Positions (Uniform.Primary c G))‖+2*m'<A) : ‖x‖<A:= lt_of_le_of_lt (le_add_of_nonneg_right (show 0≤2*m' by positivity)) hx
  have Hx := hr' Y hK he' hm B B' e β D hvI hh' x hν (hF _ hΞ)
  obtain ⟨hp,hL,hW⟩:= hY c f S T F M B β ρ k T' x hQ rfl rfl rfl hΞ hβ hz hρ Hx
  have hδ : 0<gStep β:=(gS _ hβ.positive).1
  let d' := X t*gStep β*gStep β+y^(-(2:ℝ)); have ht' : (Fintype.card (Uniform.Primary c G):ℝ) ≤ g t:= countsP F (g t) hQ.overall
  let q :=Y.blank
  have hv' : q.manifest := Y.bowed (by exact temp_nonneg _)
  have Hx' :=hr' q hK he' hv' B B' _ _ D hvI (show flags (Pressure.temp t) q.V=∅ by rw [← hK]; exact hv'.symm) 0 (by simp only [map_zero, link_one]; rfl) (hF _ hk'); obtain ⟨-,hL',-⟩:= hY c f S T F M B β ρ k T' 0 hQ rfl rfl rfl hk' hβ hz hρ Hx'
  have h₂ := Hx.1
  have hQ':∃ j, j=5 ∧ j≤n+1+2:= ⟨5,rfl,by omega⟩ -- local
  have hv:= auster F T Q.table B ρ β α k h₂ he Z hQ.one ht' ha (by omega) hQ.large.1 hQ.primary HM hρ.critical.1 Q.table_exists hΘ hP x (mem_ball_zero_iff.mpr (hF _ hΞ)) (by omega) (by omega) (hβ.positive) hL hL' (fun i hi=> (hW i ?_).smaller n.le_succ)
  · have hB:0 ≤ BareRates.bill Z T.low:= (bareSocket c Z he (x:=0) (mem_ball_self zero_lt_one) 0).2.2.2.1.le
    have hr₀:= sticks F T Q.table ρ k h₂ he Z hQ.one ht' (0:Positions (Uniform.Primary c G)) (mem_ball_self h₂.pos)
    refine ⟨hp, hv.climb (hx d' _ _ _ c hh rfl hQ.one hI (mul_nonneg hΘ.le hP) (mul_le_mul_of_nonneg_left heP hΘ.le) hβ.positive hβ.window.2 hβ.window.1 (le_trans (norm_nonneg _) (hr₀.2 1 (by omega) (by omega))) hB) le_rfl⟩
  have he : ‖x‖ + 2*m' < A := hΞ; change ‖i‖+m' < _
  exact lt_of_le_of_lt (add_le_add (mem_closedBall_zero_iff.mp hi) (by linarith only [hm'])) he
end YM.PhysicalNext.Repeat.Shellac
