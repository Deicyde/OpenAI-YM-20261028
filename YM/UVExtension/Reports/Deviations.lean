import YM.UVExtension.Upland.Plinth

/-!
 # Checking the topology of the normalized vacuum convergence

 Not a pointwise-in-configurations statement: `Readings` uses supremum
 over simultaneous bills on finitely many addresses, and completion. Here
 is a test using the ORIGINAL labelled deviation of activities from Shoot
 (including all-address l1 sum and every left jet through the stage order).
 No relabeling in this test. Do not require the norm to compare E off-domain
 extensions; E values and ordered LEFT derivatives on `Healthy`, INCLUDING
 threshold equality. Forced comparison includes *all* configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension
open Function Filter Metric Lattice RG Precision Wilson
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Lamppost Concert BoundedContinuousFunction
open PhysicalNext.Repeat Org Input RG.Shoot Tabernacle Ovens
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical

section deviation
variable {G : Gauge} {n : Side}

private lemma difference_budget (p : BudgetPoint) (u w : Tabernacle.Field G n)
    (h : Tabernacle.rake p u) (hp : Tabernacle.rake p w) :
    ∃ b t, (floor p (u-w)).EBound p b ∧ (floor p (u-w)).KBound p t := by
  obtain ⟨q,z,hq⟩ := h
  obtain ⟨s,y,hs⟩ := hp
  obtain ⟨f,H,hF⟩ := hq.boundE
  obtain ⟨g,L,hL⟩ := hs.boundE
  refine ⟨q+s,z+y,⟨fun i=> f i+g i, fun i=> sup_sub (hq.regular.smooth i) (hs.regular.smooth i) (H i) (L i),fun i=> ?_⟩,?_⟩
  · have hk (p':Prop) [Decidable p'] (X Y:ℝ) : (if p' then X else 0)+(if p' then Y else 0) = if p' then X+Y else 0 := by
      by_cases h:p'<;> simp [h]
    simpa only [BudgetPoint.mass,floor,mul_add,hk] using! budget_plus (hF i) (hL i)
  obtain ⟨x,hx,hX⟩ := hq.boundK
  obtain ⟨c,hc,hC⟩ := hs.boundK
  refine ⟨fun i=> x i+c i, fun i=> ⟨add_nonneg (hx i).1 (hc i).1, fun U=> ?_⟩,fun j=> ?_⟩
  · exact (norm_sub_le ..).trans (add_le_add ((hx i).2 U) ((hc i).2 U))
  have hk (p':Prop) [Decidable p'] (X Y:ℝ) : (if p' then X else 0)+(if p' then Y else 0) = if p' then X+Y else 0 := by
    by_cases h:p'<;> simp [h]
  simpa only [BudgetPoint.mass,floor,mul_add,hk] using! budget_plus (hX j) (hC j)

-- no coin transport required between Cham choices
lemma difference_sees (p : BudgetPoint) (σ τ a : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (u w : Tabernacle.Field G n) (h : Tabernacle.rake p u) (hp : Tabernacle.rake p w) :
    ‖tuning p σ τ u - tuning p σ τ w‖ ≤ a ↔
      (floor p (u-w)).EBound p (σ*a) ∧ (floor p (u-w)).KBound p (τ*a) := by
  obtain ⟨b,t,hb,ht⟩ := difference_budget p u w h hp
  obtain ⟨z,r,h⟩ := h; obtain ⟨y,X,hp⟩ := hp
  let Δ := u-w; let R := floor p Δ
  let P := ChimeE G p n; let Q:=ChimeK G p n
  have he : P.MeasureP (sheetE p (u-w)) b := (Above.floorE p R).2 hb
  have hT : Q.MeasureP (sheetK p (u-w)) t := (Above.floorK p R).2 ht
  have hx : tuningE p (u-w) = tuningE p u - tuningE p w := by
    refine subPrint _ _ _ _ (fun i k=> ?_) ⟨_,he⟩ ⟨z,(Above.floorE p (floor p u)).2 h.boundE⟩ ⟨y,(Above.floorE p (floor p w)).2 hp.boundE⟩
    let q:= (drawer G n).reg i; let t:Concert.Tap p G q.site q.support:= k
    exact left_sub ((h.regular.smooth i).smooth t.view t.live) ((hp.regular.smooth i).smooth t.view t.live) t.card
  have hv : tuningK p (u-w)= tuningK p u-tuningK p w:= subPrint _ _ _ _ (fun i k=> rfl) ⟨_,hT⟩ ⟨r,(Above.floorK p (floor p u)).2 h.boundK⟩ ⟨X,(Above.floorK p (floor p w)).2 hp.boundK⟩
  have hh : tuning p σ τ (u-w) = tuning p σ τ u - tuning p σ τ w:=by unfold tuning; rw [hx,hv,smul_sub,smul_sub]; rfl
  rw [← hh]
  unfold tuning; simp only [Prod.norm_def,norm_smul,norm_inv,Real.norm_of_nonneg hσ.le,Real.norm_of_nonneg hτ.le,max_le_iff]
  rw [inv_mul_le_iff₀ hσ,inv_mul_le_iff₀ hτ]; refine ⟨fun h=>?_,fun H=>?_⟩
  · exact ⟨(Above.floorE p R).1 (paper P ⟨_,he⟩ h.1),(Above.floorK p R).1 (paper Q ⟨_,hT⟩ h.2)⟩
  have hl : a ≥ 0:= nonneg_of_mul_nonneg_right (budget_nonneg (H.1.choose_spec.2 0)) hσ
  exact ⟨ticks P ((Above.floorE p R).2 H.1) (by positivity), ticks Q ((Above.floorK p R).2 H.2) (by positivity)⟩

private lemma allSites {n: Side} {f : ℕ → ℝ} (h : ∀ i, 0 ≤ f i) {c : ℝ}
    (P : ℕ → Site n → Prop) [DecidableRel P]
    (hv : ∀ i, ∃ x, P i x) (hh : ∀ x, SumBudget (fun i => if P i x then f i else 0) c) :
    SumBudget f (Fintype.card (Site n)*c) := by
  let v (x:Site n) (i:ℕ) := if P i x then f i else 0
  suffices H : SumBudget (fun i=> ∑ x, v x i) (Fintype.card (Site n)*c) by
    refine budget_mono H h (fun i=> ?_)
    obtain ⟨x,hx⟩ := hv i
    exact (show v x i=f i from if_pos hx) ▸ (Finset.single_le_sum (s:=Finset.univ) (f:=fun x' : Site n=> v x' i) (fun x' _=> (hh x').1 i) (Finset.mem_univ x))
  simpa using budget_over Finset.univ v (fun _=>c) (fun x _=>hh x)

lemma accounted_deviation (p : BudgetPoint) (σ τ a : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) (ha : 0 ≤ a)
    (u w : Tabernacle.Field G n) (h : Tabernacle.rake p u) (hp : Tabernacle.rake p w)
    (H : ‖tuning p σ τ u - tuning p σ τ w‖ ≤ a) :
    Shoot.deviation p (floor p u) (floor p w) (Fintype.card (Site n) * max σ τ * a) := by
  obtain ⟨⟨b,hb,hB⟩,c,hc,hC⟩ := (difference_sees p σ τ a hσ hτ u w h hp).mp H
  refine ⟨b,c,fun i=> ?_,hc,?_,?_⟩
  · obtain ⟨y,X,h⟩:=h; obtain ⟨y',X',hp⟩:=hp
    exact (sup_varies (h.regular.smooth i) (hp.regular.smooth i)).2 (hb i)
  · let U:= floor p (u-w)
    exact budget_loosen (allSites (n:=n) (f:=fun i=> p.mass (U.reg i).support (b i)) (fun i=> (hb i).1.trans (p.loMass _ _ (hb i).1)) (fun i x=> (U.reg i).site=x) (fun i=> ⟨_,rfl⟩) hB) (by rw [mul_assoc]; gcongr; exact le_max_left ..)
  let U := floor p (u-w)
  exact budget_loosen (allSites (n:=n) (f:=fun i=> p.mass (U.forced i).support (c i)) (fun i=> (hc i).1.trans (p.loMass _ _ (hc i).1)) (fun i x=> x∈(U.forced i).support) (fun i=> (U.forced i).inventory_ne.mono (U.forced i).inventory_sup) hC) (by rw [mul_assoc]; gcongr; exact le_max_right ..)
end deviation

open PhysicalNext Roost Spire MeasureTheory Topology
variable {G : Gauge} {X : Metals G} {D : Supply.Rolls X.p} {A : Alloy X D}
    {R : Factor A} {hG : G.Simple} {S : Uses R hG} {Y : Bolt A}

lemma deviation_test (h : Upland.Arc R S Y) (m p : ℕ) {b : ℝ} (hb : |b| < Upland.Arc.radius S)
    (ε : ℝ) (he : 0 < ε) :
    ∃ M, ∀ N₁ : ℕ, M ≤ N₁ → ∀ N₂ : ℕ, M ≤ N₂ →
      Shoot.deviation (A.B.a.budget m) ((S.realBeat b N₁ p m).activities)
        ((S.realBeat b N₂ p m).activities) ε := by
  have hh : (b:ℂ)∈ ball 0 (Upland.Arc.radius S) := mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt hb)
  obtain ⟨g,hg,hK⟩ := (Upland.Arc.uv h m p).2
  have hv: CauchySeq (fun i=> Upland.Arc.view S m p i b) := by
    refine Filter.Tendsto.cauchySeq (x:=g b) ?_
    simpa only [iteratedDeriv_zero] using! ((hK 0).tendsto_at hh)
  let σ:= A.B.a.clock.allowance m; let τ:= A.B.a.clock.forcedAllowance m
  let r:=Fintype.card (Site (A.B.a.S.side m p)) * max σ τ
  obtain ⟨hl,hτ⟩:= Dales.fundedP m A.B.a
  have hr : 0 < r := by
    refine mul_pos (by exact_mod_cast Fintype.card_pos) ?_
    exact lt_of_lt_of_le hl (le_max_left ..)
  let H i := S.realBeat b i p m
  let P i := (H i).activities
  let U i := ((P i).E,(P i).K)
  have hp i (hm : m≤ i) : Tabernacle.rake (A.B.a.budget m) (U i) := by
    have hx : Lives A.B.bake i m p (H i):=((S.ticking i p hh).prices _ (Nat.zero_le m) hm).1
    have h := hx.valid.labels; rw [hx.point] at h
    exact ⟨_,_,h⟩
  obtain ⟨k,hk⟩:= Metric.cauchySeq_iff.mp hv (ε/r) (div_pos he hr)
  refine ⟨max k m, fun n hn i hi=>?_⟩
  have hv:= hk n ((le_max_left ..).trans hn) i ((le_max_left ..).trans hi)
  have h1 : m≤ n:= (le_max_right ..).trans hn
  have h2 : m≤ i:= (le_max_right ..).trans hi
  obtain ⟨_,_,_,_,_,_,hx⟩ := Upland.Arc.real S m p n h1 b hh
  obtain ⟨_,_,_,_,_,_,hy⟩ := Upland.Arc.real S m p i h2 b hh
  change dist (Upland.Arc.view S m p n b) (Upland.Arc.view S m p i b) < _ at hv
  rw [dist_eq_norm,hx,hy] at hv
  have hF:= accounted_deviation (A.B.a.budget m) σ τ _ hl hτ (div_nonneg he.le hr.le) _ _ (hp n h1) (hp i h2) hv.le
  change Shoot.deviation (A.B.a.budget m) ((S.realBeat b n p m).activities) ((S.realBeat b i p m).activities) (r*(ε/r)) at hF
  rwa [mul_comm,div_mul_cancel₀ _ hr.ne'] at hF
end YM.UVExtension
#print axioms YM.UVExtension.deviation_test
