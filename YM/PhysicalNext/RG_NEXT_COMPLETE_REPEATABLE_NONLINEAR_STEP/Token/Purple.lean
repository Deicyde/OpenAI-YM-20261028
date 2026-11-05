import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Canvas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Vetting
/-!
# Calm within actual seam around all any x (Poly volume).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {P : Teller G} {C Z u a p c' σ η : ℝ} {L : Side}
variable (O : ChartRatio G) (he : LocalRatio O) {K : KernelChoices} (V : ChartPrices) {f r:ℝ→ℝ}
include he
local notation "B" => (fun t=> betaF G t L)
set_option maxHeartbeats 600000 in
theorem languid (j : ℕ) (d e : ℝ) (hg : Rate G L 0 f) (hr : Bolt G L r) (hd : 0<d) (hf:0 < V.gap) :
    ∃ H: ℝ→ℝ, Rate G L 0 H ∧ ∀ᶠ t in atTop, let z:= betaF G t L; let D:= wick G L d t; let u:= eaves G L t
      ∀ (c g:Side) (S:StepData c g) (T : Tube G S) (F:Forest S.ratio) (A:Before G σ C S.patch.J S.kernel ((j+1+2)+3)) (B': BudgetPoint) (β : ℝ) (ρ:Bid.Dir G c→AxisChart G F) (k:S.Choices) (P : Teller G) (b : Positions (Uniform.Primary c G)),
        Quilt T F (r t) → S.kernel = K → S.patch.L=L → A.tables T.high S.patch=V → ‖b‖+2*furl G L t < u → Intake P T t (Pane.virgin T B' β) → T.up.Bounds T.high σ C (ConnectedActivityE6.loopBill G L t) →
        A.Service F T.high T.up ρ → receiptS T A B' F ρ k L O d (f t) t β b →
           0 < tramp T B' β b ∧ Brush j (z^e) 1 (lack F T O B' ρ β k D) b ∧ ∀ v : Positions (Uniform.Primary c G), ‖v‖+ furl G L t < u → Brush (j+1) (H t*gStep β*gStep β+z^(- (2:ℝ))) 1 (pigment F T O ρ β k D) v := by
  let v:= V.gap/2; have hv:0<v:= half_pos hf; let Y t:= furl G L t
  obtain ⟨w,hw,hW⟩:= lookingGlass G L (j+1) r _ f _ v⁻¹ d vow 1 zero_lt_one (inv_pos.mpr hv) hd vow_ok hg (edge G L) (edge G L) hr (-(2:ℝ))
  obtain ⟨c₁,hU⟩:= paint_supply G (j+1); obtain ⟨R,hR,hϕ⟩:= Brush.compact (f:=Real.exp) (k:=j+1) (s:=({0}:Set ℝ)) (isCompact_singleton) fun i _=> Real.contDiff_exp.contDiffAt
  obtain ⟨L₁,hL₁,hΛ⟩:= Brush.compact (f:=Real.log) (k:=j+1) (s:=({1}:Set ℝ)) isCompact_singleton (fun i hi=> Real.contDiffAt_log.mpr ((mem_singleton_iff.mp hi) ▸ one_ne_zero))
  let k t:= r t * (Fintype.card Axis:ℝ)
  let q t:= prime G K (j+1) c₁ R (2*betaF G t L) (k t); let J t:= clump (j+1) (q t) L₁; let h t:=w t
  -- just coarse over bound ht*w*b*b ≤ h', when t large.
  let Q t:= |w t|+ betaF G t L ^ (-(2:ℝ)); let M t:= J t+(oat (j+1) (f t) (2*B t)+oat (j+1) (f t) (2*B t))+(Q t+Q t)+1
  let S₀:ℝ:= ((j+1:ℕ):ℝ)^2+2; have hQ: Rate G L 0 Q:= (Brim.absolut hw).add ((Rate.power (G:=G) (L:=L)).weaken (by norm_num))
  have hu := primeR k K (n:=j+1) (a:=R) (Z:=c₁) (hr.uses.mul_right (Fintype.card Axis))
  have hs : 0 ≤ S₀-1:= by unfold S₀; nlinarith [sq_nonneg (((j+1:ℕ):ℝ))]
  have hs':1≤S₀-1:=by unfold S₀; nlinarith [sq_nonneg (((j+1:ℕ):ℝ))]
  have hA : Rate G L (S₀-1) M:=
    ((((climbF hu (by positivity) (j+1) L₁).weaken (by unfold S₀; linarith)).add ((oatr (j+1) hg).weaken hs')).add ((hQ.add hQ).weaken hs)).add ((Rate.const _).weaken hs)
  obtain ⟨C',hE⟩:= iteration G L j (d:=S₀) (m:=e) zero_lt_one
  let U₀ := min (-1) C'; let T₀ := Real.exp (-1)*(1/2); have ht₀:0<T₀:=by unfold T₀; positivity
  let p:= V.gap*d^2/8; have hp : 0<p:=by unfold p; positivity
  have hL:=budgeting (G:=G) (L:=L) (a:=T₀) U₀ _ hp (show U₀<0 from (min_le_left ..).trans_lt (by norm_num))
  refine ⟨w,hw,?_⟩; filter_upwards [hW,hA _ (show S₀-1<S₀ by linarith), hE, hL, edge G L |>.below vow_ok _ zero_lt_one] with t hx hm hQ heT hr x D u c f' S T F A B' β ρ k' P b hv' hK hL hA hZ hP hB' hρ hS
  obtain ⟨hF,hβ,HX,Hy⟩:=hS; let δ:=gStep β; have hβx : 0<β:= hP.positive
  have hz:1≤x:= (hL ▸ hP.height).le; have hx' : 0<x := zero_lt_one.trans_le hz
  let G':= gram F T.up T.high ρ k'; let q':= Lapis.table F k' T.up T.high; let p':=mist F O T.up; let u':= orbit F ρ; have hg i (hi : ‖i‖<u) j:= wakes F k' T.up T.high ρ σ C (ConnectedActivityE6.loopBill G L t) A hv'.large hB' hρ i (hi.trans_le HX)|>.2.2.1 j
  have hc : (Fintype.card (Precision.Key F G):ℝ) ≤ r t:= countsK F (r t) hv'.overall
  have hd : 0<δ:= (Fare.gS _ hβx).1; rw [hA] at hg
  let J' := ratify q' p' u' G' D
  have ht y (hy : ‖y‖+furl G L t<u):=
    hx _ _ q' p' u' G' hc hF hg δ y hd hβ hy
  let W := w t*δ*δ+x^(- (2:ℝ))
  have hV : 0 < furl G L t:= Real.rpow_pos_of_pos hx' _
  let s t':=pures T B' β t'
  let m:=Y t; let S':=closedBall b m; let K' :=lack F T O B' ρ β k' D
  have hκ : (Real.exp (-((A.tables T.high S.patch).gap*D^2/4)/2)) = Real.exp (-p*Delay.fineMonitor G L t^2) := by apply congr_arg; rw [hA]; unfold p D wick; ring
  have h' (y) (hy:y∈ S') : Brush (j+1) (x^S₀) 1 K' y ∧ ‖K' y‖ ≤ x^C' ∧ 0<tramp T B' β y:= by
    have hk : ‖y-b‖ ≤ m:= mem_closedBall_iff_norm.mp hy
    have hQ: ‖y‖ ≤ ‖b‖ + m:= by
      conv_lhs=> rw [show y=b+(y-b) by abel ]
      exact (norm_add_le ..).trans (add_le_add le_rfl hk)
    have hy: ‖y‖+furl G L t<u:=by change ‖b‖+2*m<u at hZ; change ‖y‖+m<u; linarith only [hZ,hQ];
    have hδ : δ ≤ 1:= hβ.le.trans hF.small
    have hy' : ‖y‖<u:=by linarith only [hy,hV]
    have hs: 0 ≤ (k t):=by unfold k; have hr := hv'.one; positivity
    have hk : (Fintype.card (Bond c):ℝ) ≤ k t:= by rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right hv'.primary (Nat.cast_nonneg _)
    have ht:=ht _ hy; have hl := gradeAt F T O B' ρ β k' hβx ht₀ (Hy _ hy' (by assumption)) ht.1 he
    rw [hκ] at hl; have hv:= primeN (G:=G) K (n:=j+1) hβx (hL ▸ (show β ≤ 2 * betaF G t S.patch.L from hP.window.2)) hR.le hU.1.le hs
    rw [← hK] at hv
    refine ⟨?_, (hl.2.trans (heT.1.trans (Real.rpow_le_rpow_of_exponent_le hz (min_le_right ..)))),hl.1⟩
    have he := usurp F T O B' ρ β k' hF hP (show j+1 ≤ _ by omega) hy' hβx (ht.2.2) hl.1 hk hU hv.1 (hϕ _ (mem_singleton 0)) (hΛ _ (mem_singleton 1)) (hl.2.trans heT.2)
    apply he.climb _ le_rfl; apply le_trans _ ((le_abs_self _).trans hm)
    have hInv:= hv.1
    have hv : prime G S.kernel (j+1) c₁ R β (k t) ≤ q t:= by unfold q; rw [← hK]; exact hv.2
    have hg := (hF.curve _ hy').nonneg; have hC:=rung (j:=j+1) hβx.le hg (hL ▸ (show β≤_ from hP.window.2)); have h₁:x^(- (2:ℝ))≥0:=by positivity
    have hw : (W) ≤ Q t := add_le_add (calc
      _ ≤ |w t| * δ*δ:= by gcongr; exact le_abs_self _
      _ ≤ _ := ((mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hd.le) hδ).trans (mul_le_of_le_one_right (abs_nonneg _) hδ))) le_rfl
    exact add_le_add (add_le_add (add_le_add (rising _ hInv hv hL₁.le) (add_le_add hC hC)) (add_le_add hw hw)) le_rfl -- edit
  have hT:b∈S':=mem_closedBall_self hV.le
  exact ⟨(h' b hT).2.2,hQ _ _ K' b (fun i hi=> (h' _ hi).1) (fun i hi=> (h' _ hi).2.1),fun i hi=> (ht i hi).2.2⟩
end YM.PhysicalNext.Repeat.Token
