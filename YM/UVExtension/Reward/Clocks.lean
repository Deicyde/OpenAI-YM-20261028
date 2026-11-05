import YM.UVExtension.Reward.Budget
/-! Rate choices purchased before learning L. After L post waits only. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a}
lemma Choices.preserves {Z W V X Y J Z' A D C s σ d α k C' d' u v pace g g' U U'} (h : Choices G J k Z W V X Y Z' A D C C' d s g u pace U U') (hp : σ≤s) (hv : C' ≤ α) (he : d≤d') (ht : u ≤ v) (hz : g' ≤ g) {B B' : Side → ℝ} (hc : U≤ B) (hd : U'≤B') : Choices G J k Z W V X Y Z' A D C α d' σ g' v pace B B' := by
  intro m n P H p q R F M Gx Gy GK b r c l hk hL hm hu hQ S hB hC hE
  obtain ⟨T,w,H1,H2,H3,H4,h1,h2,h3,h4,h5,h6⟩ := h m n P H p q R F M Gx Gy GK b r c l hk (ht.trans hL) hm hu hQ S hB hC hE
  exact ⟨T,w,H1,H2,H3,H4,h1,h2,fun s v w he hh hu hg hl=>h3 s v w he (hh.trans hp) (hv.trans hu) ((hd _).trans hg) hl,h4.trans he,h5,fun i j hp hx=> h6 i j ((hc _).trans hp) (hx.trans hz)⟩

theorem owned (G : Gauge) (hG : G.Simple) (K : KernelChoices) (P : MapPrices) (Z : ℕ→ℝ) (hZ : ∀ i,0 ≤ Z i) : ∃ s A : ℕ→ℝ,(∀ i,0<s i) ∧ (∀ i,0≤A i) ∧ BasesFine G P Z s A ∧
    ∀ (τ C pace : ℕ→ℝ), (∀ i, 0<τ i) → (∀ i,0 ≤ C i) → (∀ i,0<pace i)→ Fluent G →
       ∃ (d γ : ℕ →ℝ) (u : ℕ→ℕ) (F W : ℕ→ Side→ℝ),(∀ i, 0≤d i ∧ 0< γ i) ∧ Charges G P K Z s A τ C d γ u pace F W := by
  obtain ⟨b,E,H,H',H₀⟩ := beckon G P Z hZ
  obtain ⟨i⟩ := colorAvail G hG
  choose v w hv hw I using fun (j r : ℕ) => ceilings G i hG K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α r) (pacesE P r) (Z r) (P.eta_pos j) (P.alpha_pos j) (paces_pos P j) (hZ j) (P.alpha_pos r) (paces_pos P r) (hZ r)
  let s (i) := min (b i) (min (w i i) (w (i+1) i))
  let A (i) := max (E i) (max (v i i) (v (i+1) i))
  have hx i j (h : j=i ∨ j=i+1) : s i ≤ w j i ∧ v j i ≤ A i := by
    obtain rfl|rfl := h; exact ⟨(min_le_right ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_right ..)⟩; exact ⟨(min_le_right ..).trans (min_le_right ..), (le_max_right ..).trans (le_max_right ..)⟩
  refine ⟨s,A,fun i=>lt_min (H i) (lt_min (hw ..) (hw ..)),fun i=>(H' i).trans (le_max_left ..),?_,fun τ C pace hτ hC hP Y=>?_⟩
  · intro j m hm p hp B h hc hS he; obtain ⟨R,h₁,h₂,h₃,h₄,h₅⟩ := H₀ j m hm p hp B h hc hS he
    exact ⟨R,h₁,h₂,h₃,fun σ a Λ hu hs hf hg=> h₄ σ a Λ hu (hs.trans (min_le_left ..)) ((le_max_left ..).trans hf) hg, h₅⟩
  choose d c hd' F W hd hc h using fun (j i : ℕ) => I j i (τ j) (C j) (pace i) (hP i) (hτ j) (hC j) (Y _ _ _ _ _ _ (P.alpha_pos _) (P.eta_pos _) (paces_pos ..) (hZ _) (hτ _) (hC _))
  refine ⟨fun i=>max (d i i) (d i (i-1)),fun i=> min (c i i) (c i (i-1)),fun i=> max (hd' i i) (hd' i (i-1)),fun i x => max (F i i x) (F i (i-1) x),fun i x => max (W i i x) (W i (i-1) x),fun i=> ⟨(hd i i).trans (le_max_left ..),lt_min (hc i i) (hc i (i-1))⟩,?_⟩
  refine ⟨fun i j he=> Choices.preserves (h i j) (hx j i he).1 (hx j i he).2 ?_ ?_ ?_ ?_ ?_⟩
  all_goals
    rcases he with rfl|rfl <;> first
    | exact le_max_left ..
    | exact min_le_left ..
    | exact fun j=> le_max_left ..
    | (simp only [Nat.add_sub_cancel]; first|exact le_max_right ..| exact min_le_right ..| exact fun j=> le_max_right .. )
structure Mints (D:Knobs a)(P:MapPrices)(V:Horizon a)(Q:PostCost L)(Z:ChartRatio G)(b:ℝ):Prop where
    pulse m : 1 ≤ a.clock.loopCap m
    blanket N: ∃ R:PathData G,BranchRow V N R
    work m: Working D V P m
    pays m N : m<N → ∀ R, SatPath V N (m+1) R → ∃ x α ρ,Courtesy V D Q Z b N m R x α ρ

theorem office (G : Gauge)(hS:G.Simple)(B:MapPrices)(K:KernelChoices)(B₀ : ℕ→ℝ)(he:∀ i,0 ≤ B₀ i)(h: Fluent G) (ε:ℝ)(hε:0<ε)(hb:ε≤1):
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∃ d : Knobs a, ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → Mints d B W Q Y ε:=by
  obtain ⟨σ,A,hσ,hA,H,P⟩:= owned G hS K B B₀ he
  let Z i:= overhead G (σ i)
  let δ i:= ε/(4*Z i); let t0 i:=min (σ i/3) (B.α i/3); let c i:=4*A i/ε+1
  let D i:=max (max (A i) (rowPrice (B.α i) (pacesE B i))) (c i* Z i)
  have hZ i:0<Z i:= (overhead_cases ..).2.2.2
  have hZ' i:1 ≤ Z i:= (cover_one (n:=1) _).trans (overhead_cases ..).1
  have hP i:0<c i:=by have h:=hA i; unfold c; positivity
  have hδ i:0<δ i:=by unfold δ; have h:=hZ i; positivity
  have hδ' i:δ i≤1:= by unfold δ; have h:=hZ i; have hw:=hZ' i; rw [div_le_one (by positivity)]; linarith
  refine ⟨t0,D,fun i=> lt_min (div_pos (hσ _) (by positivity)) (div_pos (B.alpha_pos _) (by positivity)),fun i=> (hA i).trans ((le_max_left ..).trans (le_max_left ..)),fun τ A' ht hv hw=>?_⟩
  obtain ⟨d,y,u,F,W,h1,Lh⟩ := P τ A' (fun i=> δ i/2) hv (fun i => ((hA _).trans ((le_max_left ..).trans (le_max_left ..))).trans (hw i)) (fun i=>half_pos (hδ i)) h
  refine ⟨d,fun i=> y i/2,u,fun i=>(h1 i).1,fun i=> half_pos (h1 i).2,fun s hs hB L => ?_⟩
  obtain ⟨η,H'⟩ := scene_gate L B
  choose V hT using fun i => waits_up (F i (L.L i)) (y i) 1 (h1 i).2 zero_lt_one
  refine ⟨fun i=> max (GateVolume i) (V i),η,H',fun Θ=> ?_⟩
  obtain ⟨Δ,hΔ⟩ := clocks G hS s L Θ (fun i=> max (W i (L.L i)/δ i) (W i (L.L i)/δ (i-1)))
  refine ⟨Δ,fun w β b he hl Q hη hg hc a hd => ?_⟩
  have hw₀ := hΔ w β b he a hd
  let J:= a.clock.J; let C m := a.clock.loopCap m
  have htC i : 0<C i:= zero_lt_one.trans_le (hw₀ _).2.2
  let Y : Knobs a:=⟨fun m=>σ (J m),fun m=> c (J m),fun m=> C m / Z (J m),fun m=> ⟨hσ _,hP _, div_pos (htC _) (hZ _)⟩⟩
  refine ⟨Y,fun X V₁ hX hV T hR=> ?_⟩
  have hpW i : (s.profile i).width < σ i/2 := ((hB.fields i).1.trans_le ((ht i).trans (min_le_left ..))).trans_lt (by have hp:=hσ i; linarith)
  have hvW i : (s.profile i).width ≤ σ i := le_of_lt ((hpW i).trans (half_lt_self (hσ i)))
  have he i : D i ≤ (s.profile i).paths := (hw i).trans_eq (hB.fields i).2.symm
  have hk i : A i ≤ (s.profile i).paths := ((le_max_left ..).trans (le_max_left ..)).trans (he i)
  have hg' i (n : Side) (hL': w.shells i ≤ n.val) : F i (L.L i) * Real.exp (-(y i)*n.val) ≤ Q.Γ i*Real.exp (-(Q.c i)*n.val) := by
    have hh : Q.c i ≤ y i/2 := hc i; have hξ : 1≤Q.Γ i := hg i
    refine (hT i n ((le_max_right ..).trans ((hl i).trans hL'))).trans (mul_le_mul hξ (Real.exp_monotone (by gcongr)) (Real.exp_pos _).le (zero_le_one.trans hξ))
  have hM (m:ℕ): a.params m=s.profile (J m):=by unfold Levels.params Calendar.params; rw [hd.stage]
  have HH m : Working Y V₁ B m:=by
    let i:= J m
    have hu' : (a.params m).width < B.α i:= by
      rw [hM]; exact ((hB.fields i).1.trans_le ((ht i).trans (min_le_right ..))).trans_lt (by have hx:= B.alpha_pos i; linarith)
    have hp':(a.params m).width < Y.widths m/2:=by rw [hM]; exact hpW _
    refine ⟨fun N h=> hull_fact hX hV h,hu',hp',fun N hi x hx hu=> ⟨rfl,rows_layout rfl,?_⟩⟩
    have hH:=hull_fact hX hV hi
    have he': D i ≤ (a.params m).paths:=by rw [hM]; exact he _
    exact Rates.take (label Y m) (V₁.H N m) (a.params _).width_pos hu'.le hp'.le hH.2.1 (hH.2.2.1 1) (((le_max_right ..).trans (le_max_left ..)).trans he') ((le_max_right ..).trans he') (by change C m/Z i*Z i≤ C m; rw [div_mul_cancel₀ _ (hZ _).ne']) x hu hx
  refine ⟨fun i=> (hw₀ i).2.2,fun N=> budding hd hvW hk hB.axis hX hV H (fun i=> (hw₀ i).2.2) N,HH,fun m N hi R h_paths=>?_⟩
  let i:=J m; let j:=J (m+1); let v:= δ i*C m
  have h0 m:= (hw₀ m).2.2
  have hh : j=i ∨ j=i+1 := by
    have hf : i≤j:= a.fits.mono (Nat.le_succ _); have hH : j ≤ i+1:=a.fits.stepSlow _; omega
  refine bought (T:=W) hd (hη.symm ▸ H') (fun i=> (le_max_left ..).trans (hl i)) hg' hB.axis hvW hk hB.gradient hB.days hR hX hV (pace:=fun i=>δ i/2) ?_ hb (HH m) le_rfl (Er:=v) ?_ ?_ (mul_le_of_le_one_left (htC m).le (hδ' i)) ?_ (h0 (m+1)) h_paths.bound h_paths.ties hi
  · rw [hs,funext fun i=> (hB.fields i).1,funext fun i=> (hB.fields i).2]; exact Lh
  · have hu: W j (L.L j)/δ i ≤ C m:=by
      apply le_trans ?_ (hw₀ _ |>.1); change _ ≤ max (W j (L.L j)/δ j) (W j (L.L j)/δ (j-1))
      obtain H|H:=hh
      · rw [H]; exact le_max_left ..
      rw [H]; simpa only [Nat.add_sub_cancel] using! le_max_right (W (i+1) (L.L (i+1))/δ (i+1)) (W (i+1) (L.L (i+1))/δ i)
    exact ((div_le_iff₀ (hδ _)).mp hu).trans_eq (mul_comm ..)
  · change δ i/2*C (m+1) ≤ v; rw [div_mul_eq_mul_div, mul_div_assoc]; exact mul_le_mul_of_nonneg_left (hw₀ m|>.2.1) (hδ i).le
  change v / (C m/Z i)+ A i/c i + A i/c i≤ε
  have hp : A i/c i ≤ ε/4:=by
    rw [div_le_iff₀ (hP _)]
    refine le_of_sub_nonneg ?_; unfold c; field_simp; nlinarith
  have ht': v/(C m/Z i)=ε/4:=by unfold v δ; have hx:= hZ i; have hu:=htC m; field_simp
  rw [ht']; linarith
end YM.UVExtension.Reward
