import YM.TraceExtension.Prom.Order.Stack
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision Supply
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Ac Baler Glyph Tapes Marker
open Display Display.Docking  Value Flux SectorNext.Vacuum Station Perch Tapes.West
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{X : Sheet G}(B:MapPrices){D: Rolls X}{b:Purse}{j u:ℕ}
abbrev baseSky (D: Rolls X) (j:ℕ):= D.L (j-1)
abbrev farSky (j:ℕ):= ({j,j-1}:Finset ℕ)
abbrev adjoining (j:ℕ): Finset (ℕ × ℕ):= ((farSky j) ×ˢ (farSky j)).filter (fun i=> i.2 ≤ i.1)
private lemma ventSat (Q : Teller G) (Y : ChartRatio G)(i:ℕ)(L:Side)(p:Purse)(x b s d v W:ℝ) (h : TimingSky Q Y i L p b W d s) : TimingSky Q Y i L (vent p x) b W d s:= by
   -- Mesa band actually not change
   obtain ⟨⟨h1,h2⟩,h,H,c⟩:=h; refine ⟨⟨?_,h2⟩,fun P hj hp he=> h P hj hp he,H,c⟩
   intro D hf hL hx; obtain M:= h1 D hf hL hx; cases M; constructor <;> assumption
lemma allySky (hp:∀ i∈ farSky j,Roh X B j b u (D.L i))(hb:0≤ b.band)(J: ChartRatio G)(hJ:LocalRatio J): ∃ (W d δ:ℝ),∃ (he:0<δ), δ ≤ b.era.coast.a ∧
    let Q:=InteractingRank.trim b δ he
    -- h timing even for variable band.Principle
    (∀ i∈farSky j,∀ t∈farSky j, t ≤ i →
    ∃ v:ℝ,0≤ v ∧ ∀ᶠ s in atTop, stretch ((baseSky D j).val:ℝ) Q.band s ≤ stretch (D.L i).val v s ∧
       ∀ y:ℝ, TimingSky (initials B X.profile X.kernel i t) J i (D.L i) (vent Q y) v W d s ∧
        PostsSky J B X.profile X.kernel i t (vent Q y) (D.L i) W d s):= by
    let P:=adjoining j;let Z (i:ℕ × ℕ): Teller G:= initials B X.profile X.kernel i.1 i.2
    have hz(i):1 < ((D.L i).val:ℝ):= by exact_mod_cast (le_trans (by norm_num:2≤3) (D.large i).size)
    choose v hv he using fun i=> raises_more ((baseSky D j).val:ℝ) (D.L i).val b.band (hz (j-1)) (hz i) hb
    have hQ : ∀ᶠ W:ℝ in atTop, ∀ i∈P, ∃ a d:ℝ,0<a ∧ 0<d ∧ ∀ (d' δ:ℝ), d ≤ d' → ∀ h:0<δ,δ ≤ a → ∀ᶠ s in atTop, TimingSky (Z i) J i.1 (D.L i.1) (InteractingRank.trim b δ h) (v i.1) W d' s:= by
       refine (eventually_all_finset _).2 fun i hi=>?_
       obtain ⟨hF,hI⟩:= mem_filter.mp hi; obtain ⟨h1,h2⟩:= mem_product.mp hF
       exact (((hp i.1 h1).merit _ h1 _ h2 hI).2 _ (hv _)).mono fun W h=> h J hJ
    obtain ⟨W,hW,hρ⟩:= (hQ.and (eventually_gt_atTop (0:ℝ))).exists
    choose! a d hα hd ht using hW
    have hm:P.Nonempty:= ⟨(j,j),mem_filter.mpr ⟨mem_product.mpr ⟨mem_insert_self ..,mem_insert_self ..⟩,le_rfl⟩⟩
    let d':= sup' P hm d; let A:= inf' P hm a; let c:= b.era.coast; let δ:= min c.a A
    have hδ : 0<δ := lt_min c.posA ((lt_inf'_iff ..).2 fun i hi=> hα _ hi)
    let T:= InteractingRank.trim b δ hδ
    refine ⟨W,d',δ,hδ,min_le_left ..,fun i h1 t h2 hI=>?_⟩
    have hj: (i,t)∈P:= mem_filter.mpr ⟨mem_product.mpr ⟨h1,h2⟩,hI⟩
    let L:= D.L i; have hb:= ((hp i h1).merit i h1 t h2 hI).1
    have he' : BrevitySky (G:=G) B X.kernel i t T L:= ⟨hb.capital,hb.width,hb.pulse,hb.credits,hb.ceiling⟩
    obtain ⟨w,hw,h'⟩:= politeSky J B X.profile X.kernel i t T hJ L he' W hρ
    refine ⟨v i,hv i,?_⟩; filter_upwards [he i,h', ht (i,t) hj d' δ (le_sup' d hj) hδ ((min_le_right ..).trans (inf'_le a hj))] with s he hP hX
    have he:= proclaimSky B X hX.onRoad hP
    refine ⟨‹_›,fun y=>⟨ventSat _ _ _ _ _ _ _ _ _ 0 _ (show TimingSky _ J i _ T _ W d' s from hX),?_⟩⟩
    exact ⟨⟨he.monitor.vote,he.monitor.optics,he.monitor.earn⟩,he.clamp,he.mile,he.melt,he.wool,he.stamp⟩
end YM.PhysicalNext.InteractingRank.Soft
