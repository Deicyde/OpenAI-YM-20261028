import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arcus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Parterre
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Vignette

/-!
# All sufficiently small displacements inside the same FREE chart

Raw extended I/F, no cut, includes normalized stencils exactly from real
punch operations. For flat-window probe, will use around projected center. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel   
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {j : ℕ} {U : E → Config G f} {V Q : E → Config G c} {x : E} {v z a w b d e : ℝ}
open Brush

lemma predicts_mul (D : Patch) (K : KernelChoices) (h : D.Branches K G) (j : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ v : ℝ,∀ (c f:Side) (S:StepData c f), S.patch=D → S.kernel=K →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→Config G f) (x:E), Mode U x j v →
      (∀ i, ‖G.mat (U x i)-1‖ ≤ r) → ∀ k:S.Choices, Mode (fun i=> S.prediction (U i) k) x j (C*v) := by
  obtain ⟨r,C,hR,hC,hg⟩:= Shadow.transfers D K G j h
  obtain ⟨J,d,hp⟩:= cleanly G j r hR
  let c':= (1+j.factorial*C)*((1+j.factorial*J)*(1+royalty G))
  refine ⟨c',d,by unfold c'; have := hp.value; have := royalty_ge G; positivity,hp.pos,?_⟩
  intro v c f S hS hK E _ _ U x he hx k
  obtain ⟨hk,hr,h⟩:= ep he hp hx
  let W (s:E) := toLog (n:=f) fun i=> G.plog (G.mat (U s i))
  have hv (i) : Brush j (royalty G) (c'*v) (fun t=> G.mat (S.prediction (U t) k i)) x := by
    have hh : Brush j _ _ _ x := thicken (f:=fun t=> S.prediction (represent (W t)) k i) (hk.pine (hg c f S hS hK _ k (W x) hr))
    refine hh.shimmy (g:=fun t=> G.mat (S.prediction (U t) k i))
      (h.mono fun z hz=> congrArg (fun u: Config G f=> G.mat (S.prediction u k i)) hz) |>.climb le_rfl ?_
    unfold c'; apply le_of_eq; ring
  exact ⟨(hv (0,0)).pos,hv⟩

lemma later (p : Mode V x j v) (h : v ≤ w) : Mode V x j w := ⟨p.pos.trans h,fun i=> (p.atLink i).climb le_rfl h⟩

abbrev ZipP (G : Gauge) (c f : Side) := Directions G c × Directions G f

def shaft (S : StepData c f) (u : ZipP G c f) : Config G f := increment (replica S.ratio (increment 1 u.1)) u.2

/-- Four actual arguments: V, U, Q, and M's base Q on V COPY. -/
theorem dressed (P : Teller G) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) : ∃ r v : ℝ, 0<r ∧ r≤1 ∧ 0≤v ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T→ S.patch=D→
    ∀ u : ZipP G c f, ‖u‖ ≤ r → ∀ k : S.Choices, let V (u:ZipP G c f):=increment 1 u.1
    Mode V u j v ∧ Mode (shaft S) u j v ∧ Mode (replica S.ratio ∘ V) u j v ∧
      Mode (fun v=> S.prediction (shaft S v) k) u j v ∧ Mode (fun v=> S.prediction (replica S.ratio (V v)) k) u j v := by
  obtain ⟨a,C,ha⟩ := expCost G j 1
  -- `δ` for input fromLog projections.
  let m := royalty G; have hm := royalty_ge G
  let v:= ((1+j.factorial*a)*((1+1)*(1:ℝ)))
  have hv : 0 ≤ v := by unfold v; positivity
  let w:= v*m+v; have ht : v≤w := le_add_of_nonneg_left (mul_nonneg hv (zero_le_one.trans hm))
  have hw : 0≤w := hv.trans ht
  obtain ⟨Z,r,hZ,hr,hp⟩:= predicts_mul D P.bind hD j
  obtain ⟨c,r',hc,hr',hy⟩:= chord_chart_cost G
  obtain ⟨d,hd,hd',h₁,h₂⟩: ∃ d : ℝ, 0<d ∧ d≤1 ∧ d≤r' ∧ (c*d+c*d)*m ≤ r := by
    have hx : 0 < royalty G := lt_of_lt_of_le zero_lt_one hm
    let d := min 1 (min r' (r/(2*c*m)))
    have he : 0<d := lt_min zero_lt_one (lt_min hr' (by unfold m; positivity))
    obtain ⟨hv,hh⟩:= le_min_iff.mp (show d≤min r' _ from min_le_right ..)
    exact ⟨d,he,min_le_left ..,hv,by have hk := (le_div_iff₀ (show 0<2*c*m by dsimp only [m]; positivity)).1 hh; linarith⟩
  let V := w+Z*w
  have h3 : w≤V := le_add_of_nonneg_right (mul_nonneg hZ.le hw)
  have h4 : Z*w≤V := le_add_of_nonneg_left hw
  refine ⟨d,V,hd,hd',hw.trans h3,?_⟩
  intro c' f S T he hS u hu k f'
  have hA : ‖u.1‖≤d ∧ ‖u.2‖≤d := max_le_iff.mp hu
  have he₁ : Brush j 1 1 Prod.fst u := linearB (ContinuousLinearMap.fst ℝ (Directions G c') (Directions G f)) (hA.1.trans hd') (by rw [one_mul]; exact ContinuousLinearMap.norm_fst_le ℝ (Directions G c') (Directions G f)) zero_le_one
  have he₂ : Brush j 1 1 Prod.snd u := linearB (ContinuousLinearMap.snd ℝ (Directions G c') (Directions G f)) (hA.2.trans hd') (by rw [one_mul]; exact ContinuousLinearMap.norm_snd_le ℝ (Directions G c') (Directions G f)) zero_le_one
  have hF : Mode f' u j v := fromLogL Prod.fst he₁ 1 zero_lt_one ha (fun p => (norm_le_pi_norm u.1 p).trans (hA.1.trans hd')) _
  let U := shaft (G:=G) S; let P:=replica S.ratio ∘ f'
  have hp' : Mode P u j v := ⟨hv,recopy S hF.atLink⟩
  have hU : Mode U u j w := by
    have ht := fromLogL Prod.snd he₂ 1 zero_lt_one ha (fun i=> (norm_le_pi_norm u.2 i).trans (hA.2.trans hd')) (1:Config G f)
    refine ⟨hw, fun i=> ?_⟩
    have he : Brush j m v (fun k:ZipP G c' f=>G.mat (G.lieExp (k.2 i))) u := by
      simpa only [increment,Pi.one_apply,mul_one,m,v] using! ht.atLink i
    exact links (f:=fun k:ZipP G c' f=> G.lieExp (k.2 i)) (g:=fun k=> G.mat (P k i)) he (hp'.atLink i) m (max_le hm le_rfl)
  have hh i : G.chord (replica S.ratio (f' u) i) ≤ c*d := by
    unfold replica; split
    · rw [G.chord_one]; positivity
    next h =>
      dsimp only [f',increment]; rw [Pi.one_apply,mul_one]
      apply (hy (u.1 _) ((norm_le_pi_norm u.1 _).trans (hA.1.trans h₁))).trans
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm u.1 _).trans hA.1) hc.le
  have hq i : ‖G.mat (U u i)-1‖≤r := by
    have hv := ((G.chord_triangle (G.lieExp (u.snd i)) (replica S.ratio (f' u) i)).trans (add_le_add
      ((hy _ ((norm_le_pi_norm u.2 i).trans (hA.2.trans h₁))).trans
        (mul_le_mul_of_nonneg_left ((norm_le_pi_norm u.2 i).trans hA.2) hc.le)) (hh i)))
    have ht : ‖G.mat (U u i)-1‖/m ≤ c*d+c*d := hv
    exact ((div_le_iff₀ (lt_of_lt_of_le zero_lt_one hm)).mp ht).trans h₂
  have he' i : ‖G.mat (P u i)-1‖≤r := by
    have ht : ‖G.mat (P u i)-1‖/m≤ c*d+c*d := (hh i).trans (le_add_of_nonneg_right (mul_nonneg hc.le hd.le))
    exact ((div_le_iff₀ (lt_of_lt_of_le zero_lt_one hm)).mp ht).trans h₂
  refine ⟨later hF (ht.trans h3),later hU h3,later hp' (ht.trans h3),later ?_ h4,later ?_ h4⟩
  · exact hp w c' f S hS he.knobs _ U u hU hq _
  exact hp w c' f S hS he.knobs _ P u (later hp' ht) he' _
end YM.ConnectedActivityE6.Blaze.Frond
