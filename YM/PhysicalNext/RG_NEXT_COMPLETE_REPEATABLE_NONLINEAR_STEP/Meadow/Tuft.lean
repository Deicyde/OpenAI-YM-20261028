import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Span
/-! # Inverse anchored map & arcs equality. Use Month before χ comparisons.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' m: ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (x:Site C) (hp:R'.path=R.path)
local notation "B" => radiusB p
local notation "D" => roomSize X.halo B
local notation "τ" => Mint.width X.halo B B
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include I I' hC he hp
lemma ramify (z: Park c f) (h: Seed I z) (hk : Meadow.ground I z⊆ neighbors D' x') (ht : D'+τ≤ m) (hm: 2 * m < c.val) : ∃ v, Seed I' v ∧ Meadow.ground I' v⊆neighbors m x ∧ wrappers (L) v=z := by
  let P:= L 
  let y := verse_down P
  choose Y' HY hp' using (nest_mint (h:=by assumption) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).esc x -- maybe inference
  let v:=z.image Y'
  have hx' i (hi:i∈z) : separation x (pace Y (Y' i)) ≤ D':=(hp' i).trans_le ((neighbors_mem ..).1 (hk (centers h hi)))
  have hr k (hk:k∈v): pace Y k ∈ Meadow.ground I' v ∧ I'.supportP (disc (Y) k) ⊆ neighbors m x:= by
    obtain ⟨p,hpK,rfl⟩:= mem_image.mp hk; let A':=Y' p; have hh:= contempt hC he hp (I:=I) (I':=I') A'; have ht' := hx' p hpK
    obtain ⟨hz,hV⟩:= centered X.halo B B (lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) A' Y T' R' (((hh.1.trans (congr_arg (verse R.path) (HY p))).trans_le (h.earns _ hpK)))
    refine ⟨mem_biUnion.mpr ⟨_,mem_map_of_mem (disc Y) (show A'∈ v from mem_image_of_mem _ hpK),hz⟩, fun i hi=> ?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (pace Y A') _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hV hi))).trans ht)
  have hM:Meadow.ground I' v⊆neighbors m x:= by intro i hi; obtain ⟨k,hk,h⟩:= mem_biUnion.mp hi; obtain ⟨s,hs,rfl⟩:=mem_map.mp hk; exact (hr s hs).2 h
  have ht': Set.InjOn (verse_down P) v:= fun i hi j hj hh=> (nest_mint (hC:=hC) (he:=he) (h:=by assumption) (H:=H) (Q:=Q)).point hm x i j ((neighbors_mem ..).1 (hM (hr i hi).1)) ((neighbors_mem ..).1 (hM (hr j hj).1)) hh
  have hL:wrappers P v=z:= by unfold wrappers v; rw [Finset.image_image,show verse_down P ∘ Y'=id from funext HY,image_id]
  exact ⟨v,(seed_order hC he hp v (I:=I) (I':=I') ht' ((garden hC x hm).mono (coe_subset.mpr hM))).2 (hL.symm ▸ h),hM,hL⟩
lemma returns (s: Vines c f) (hs: Stir I s) (hx:x'∈Meadow.pasture I s) (hH:2*(D+τ) < c.val):
    ∃ u, Stir I' u∧ x∈Meadow.pasture I' u∧ forward (L) u=s:= by
  choose f hp' hZ hf using fun i=> ramify hC he x hp (I:=I) (I':=I') (s.2 i) (hs.each i) ((your (z:=s) i).trans (entered hs x' hx)) le_rfl hH
  let u:Vines C F:= ⟨s.1,f⟩
  have h : forward (L) u=s:= by unfold forward u; congr 1; exact funext hf
  have ht : Meadow.pasture I' u⊆ neighbors (D+τ) x:= by
    intro i hi; obtain ⟨j,-,hq⟩:=mem_biUnion.mp hi; exact hZ j hq
  have hy := receipts (I:=I) hC he x hp u hH ht hp'; rw [h] at hy
  refine ⟨u,⟨hs.small,hp',hy.symm ▸ hs.moves⟩,?_,h⟩
  obtain ⟨i,hk,hh⟩:=mem_image.mp (show (L).low.cut x∈ (Meadow.pasture I' u).image (L).low.cut from (by rw [← pitchRoll hC he hp (I:=I) (I':=I') u,h]; exact hx))
  exact ((garden hC x hH (ht hk) (show x ∈ neighbors _ x from (neighbors_mem ..).2 (by simp)) hh) : i=x) ▸ hk
end YM.PhysicalNext.Repeat.Meadow
