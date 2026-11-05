import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Royal
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Royal for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Lattice RG Pressure Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision Filter
    MeasureTheory SectorTools.PhysicalGaussianSwitch
    Pump Display Display.Docking Push.AbsoluteSums AnalyticNext.ConnectedActivity
    Next.Rank Perch Tapes Atlas Supply RankCovariance
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
-- post with all geometric hypotheses scheduled
def vent (v : Purse) (x:ℝ): Purse:= {v with band:=x}

structure TimingSky (P : Teller G) (J : ChartRatio G) (j : ℕ) (L : Side) (ξ : Purse) (b W d s : ℝ): Prop where
  onRoad : Ports P J j L ξ W d s
  kraft (D : Patch) : D.J=j → D.L=L → D.Branches P.bind G → Kraft J (vent ξ b) P D W d s
  specs (hb : 0 ≤ b) (hL : 1 < (L.val:ℝ)): Escalates (vent ξ b) L s
  costs : Costs P.top G s

-- request before L. Still allow higher lengths, includes indicator comparing k fixed-depth value.
def AvailableSky (P : Teller G) (L : Side) (i : Purse) (b : ℝ):Prop:= ∀ᶠ W:ℝ in atTop,∀ J : ChartRatio G, LocalRatio J→ ∃ a d : ℝ,0<a∧0<d ∧
    ∀ (d' δ : ℝ),d≤d' → ∀ hp :0<δ,δ ≤ a → ∀ᶠ s in atTop, TimingSky P J P.j L (InteractingRank.trim i δ hp) b W d' s
lemma solubleSky (P : Teller G) (i : Purse): ∃ n:ℕ,∀ L:Side,n≤ L.val → ∀ b:ℝ, 0 ≤ b → AvailableSky P L i b:=by
  obtain ⟨n₁,hnᵤ⟩:= Pump.billable P i
  obtain ⟨n,hn⟩:= Wax.preheat P
  obtain ⟨C,hC⟩:= Aff.reserves P
  obtain ⟨u,hu⟩:= Jewels.pre P C
  let e:= Docking.increment (load i.era+1); let A:=P.top.supportExponent; let t:= A/4
  have he :0≤e:=by unfold e Docking.increment load Flux.ucap; linarith only [i.spend]
  have hA:0<A:=P.top.price_pos; have ht:0<t:=by unfold t; positivity
  obtain ⟨p,hp⟩:= Fees.exponent 1 ht he (show 2*t < A by unfold t; linarith only [hA])
  refine ⟨n+n₁+u+p+2,fun L hL b hb=>?_⟩; have hg:= hnᵤ L (by omega); have hy : (2:ℕ)≤ L.val:=by omega
  have hLarge : 1 < (L.val:ℝ):= by exact_mod_cast (show 1<L.val from hy)
  have hF (δ : ℝ) (hp : 0<δ) :∀ᶠ s:ℝ in atTop, let v:=InteractingRank.trim i δ hp; (0 ≤ b → Escalates (vent v b) L s) := by
    let v:= InteractingRank.trim i δ hp; exact (waterfall (vent v b) hb L hLarge).mono (fun s h _=>h)
  unfold AvailableSky
  filter_upwards [hn L (by omega),eventually_gt_atTop (0:ℝ), Jewels.settlers P C,hg] with W hw hW h' hQ J hJ
  obtain ⟨m,hm,hM⟩:=hw
  obtain ⟨a₀,d₀,h,hx,hv⟩:=hQ J hJ
  let α:=m/4; have ha:0<α:=div_pos hm zero_lt_four; let a:=α/8; have hh:0<a:=by unfold a; positivity
  by_cases hz:∃ Q : Patch,Q.J=P.j ∧ Q.L=L ∧ Q.Branches P.bind G
  swap
  · refine ⟨a₀,d₀,h,hx,fun d δ hD hh he=>?_⟩
    filter_upwards [hv d δ hD hh he,hF δ hh,prediction G P.top] with s he hh hg
    exact ⟨he,fun D h hb hp=> (hz ⟨D,h,hb,hp⟩).elim,fun h _=> hh h,hg⟩
  obtain ⟨Q,hS,hy,hK⟩:=hz; subst L
  obtain ⟨d,ε,hd,hε,H⟩:= excels J hJ P Q hK W hC (hu Q.L (by omega)) hW h'
  refine ⟨min a a₀,max d d₀,lt_min hh h,hd.trans_le (le_max_left ..),fun d' δ hE hh ht' =>?_⟩
  let i':= InteractingRank.trim i δ hh; have he:d≤d':=(le_max_left ..).trans hE
  have hs : ∀ᶠ s in atTop, Kraft J (vent i' b) P Q W d' s:=by
    refine accepts_stock P Q hK J hJ (vent i' b) (fun {c f} S hS=>hp c f S.ratio (by change p≤ S.patch.L.val; rw [hS]; omega)) ht (H d' he) (hM _ _) hm ha hε (by unfold α; linarith only) hW (hd.le.trans he) ?_
    change 2*δ≤_; have hx : δ ≤ a := ht'.trans (min_le_left ..); unfold a at hx; linarith only [hx]
  have hD {D:Patch} (hj : D.J=P.j)(hL : D.L=Q.L): D=Q:= by cases Q; cases D; congr; simp_all
  filter_upwards [hF δ hh,hv d' δ ((le_max_right ..).trans hE) hh (ht'.trans (min_le_right ..)), prediction G P.top, hs] with s ht h hv hh
  exact ⟨h,fun D h hv hB=> (hD h hv).symm ▸ hh,fun h _=> ht h,hv⟩
variable (B : MapPrices) (X : Supply.Sheet G)

end YM.PhysicalNext.InteractingRank.Soft
