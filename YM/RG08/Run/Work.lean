import YM.RG08.Run.Rill
/-!
# Projection-null stencils transfer in meshed histories. Carry within stratum
in chosen representative independent of ever comparing gradient representatives.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type}{u:I→Windows}{w:J→ ShoreP u} {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ A C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
section paying
-- run ticket down one ancestor. Titles may be for ANY path schedule supplied.
variable {v: J→Side}{Z:∀ i, Cross (v i) (Candles G) (Loc G 1)}{y σ δ ρ η p:J→ℝ}{U:J→ BoardU D R G}{V:J→EnvelopeU D R G j}
lemma par_for (h:Audience y)(hz:SafeRow y 1 Z p)(hR:1/2≤R)(hk:∀ i, Odd (v i).val)(hp:∀ i,0<p i)(he:0≤η)(hx:η≤1)(ht:∀ i,η i/(v i).val≤σ i)(h1:σ ≤ 1)(hm:Weighed y (fun i=>utter k (p i)))(hf:Weighed y (fun i=> ((v i).val:ℝ)))(hV:Card k y ρ V σ) : Card k y ρ (fun i=> ((↑(v i).val:ℝ)^d *((Fintype.card (Site (v i)):ℝ))⁻¹) • ∑ b:Site (v i),rue b (Z i) (V i) r) η := by
    obtain ⟨A,hA,H⟩:=hV.money; obtain ⟨C,hC,HZ⟩:=hz
    let a := (1+4*(r:ℝ))^k; let b:= (((r+1:ℕ):ℝ)^k*silkSale G j r)
    have ha:0≤a:= by unfold a; positivity
    have hb:0≤b:= mul_nonneg (by positivity) (silkSale_pos ..)
    have hZ i: Row.strip (Z i) (p i) (C i):= by simpa only [Pi.one_apply,mul_one] using HZ i
    refine ⟨_, (hf.powers d).times (((Weighed.constant y ha).times ((hm.times ((Weighed.constant y (show 0≤ (Fintype.card (Loc G 1):ℝ) by positivity)).times hC)).powers r)).times ((Weighed.constant y hb).times hA)),fun i=>?_⟩
    apply Ink.raise (Ink.scale (Ink.additions (fun b _=>runeP b hR (hk i) (r:=r) (H i) (he i) (hx i) (h1 i) (ht i) (hZ i) (hp i) (hC.positive i)) (zero_le_one.trans (tailp (he _)))) _)
    rw [sum_const,card_univ,nsmul_eq_mul, Real.norm_of_nonneg (by positivity)]; apply le_of_eq; unfold a b; simp only [Pi.mul_apply]; field_simp
lemma marry_for (h:Audience y)(hz:SafeRow y 1 Z p)(hR:1/2≤R)(hk:∀ i, Odd (v i).val)(hp:∀ i,0<p i)(he:0≤η)(hx:η≤1)(ht:∀ i,η i/(v i).val≤σ i)(h1:σ ≤ 1)(hm:Weighed y (fun i=>utter k (p i)))(hf:Weighed y (fun i=> ((v i).val:ℝ)))(hV: ∀ j< e,∀ r, Card k y ρ (fun i=> U i j r) σ)(hO:r≤m+e): Card k y ρ (fun i=> curse m (m+e-r) r d (U i) (Z i)) η := by
  let A j i:= moreU m (m+e-r) (U i) j
  have hQ j (hj:j<r): Card k y ρ (A j) σ:= by
    unfold A moreU; split; next hP=> apply hV; omega
    exact Card.zero
  let W j i:= ((↑(v i).val:ℝ)^d *((Fintype.card (Site (v i)):ℝ))⁻¹) • ∑ b:Site (v i),rue b (Z i) (A j i) r
  rw [show (fun i=> curse m (m+e-r) r d (U i) (Z i))=(fun i=> ∑ j∈range r,W j i) from funext fun i=>by unfold curse; rw [sum_comm,Finset.smul_sum]]; exact Card.group _ h he fun j hj=>par_for h hz hR hk hp he hx ht h1 hm hf (hQ j (mem_range.mp hj))
end paying

section work
variable (he:Tights T S ν D' u)(hv:Heirs T' u)
local notation "Ⓨ" => wallY X
local notation "Δ" => tiltP X
local notation "Υ" => Ye X ν D' T
local notation "Γ" => heights X ν D'
variable {L:Wall w 1→Wings u 1}

-- Ward & contraction on copies of wing shelf
include he
lemma walkerF (F: J→ ShoreP u)(M:Wall F n→ Wings u 1)(hp:∀ i,(M i).toLaunch=i.world.toLaunch) : ∃ Z : ∀ i:Wall F n, Cross (X.S.block (M i).i) (Candles G) (Loc G 1), SafeRow Ⓨ 1 Z (fun t=> ώ T (M t).i) ∧ Weighed Ⓨ (fun t:Wall F n=> (↑(X.S.block (M t).i).val:ℝ)) ∧ Weighed Ⓨ (fun t=>utter k (ώ T (M t).i)) ∧ ∀ i, Speaks (babyQ G X (M i)) (Z i) (Γ (M i)).tree:= by
  choose Z hZ H using he.walks
  have he' : Weighed (wallY (b:=F) (n:=n) X) (fun t=> menu X (M t)) := by unfold Wings.menu; simp_rw [hp]; exact Wall.invested X
  have hh:= (he.hc.turn.transfer (fun x=> (M x).toLaunch)); have h : Audience (wallY (b:=F) (n:=n) X):= Wall.plusOne X
  refine ⟨_,⟨_,he'.sway h hh,fun i=> ?_⟩,he'.sway h (he.operator.crop.transfer M), utterBuy k (he'.sway h (he.he.costs.transfer (fun x=>(M x).toLaunch))) (fun t=> ((tick_t T _).1.trans ((tick_t T _).2.trans (min_le_right ..)))),fun i=> H (M i)⟩ -- Z meta
  simp only [Pi.one_apply,mul_one]; exact hZ _
variable {U: Wall w 1→BoardU D R G}{p : J→ℝ}
-- namesake ℝ; use width input one; same clocks via proof on toLaunch
lemma dean (hp:∀ i,(L i).toLaunch=i.world.toLaunch) (hT : ∀ i,Marvel m (U i))(hm : r≤m+e)(hx:∀ j<e,∀ r,Card k Ⓨ (strideP X w p) (fun i=> U i j r) 1): Card k Ⓨ (strideP X w p) (fun i=> aboard d (Γ (L i)).tree (U i e r)-aboard d (babyQ G X (L i)) (U i e r)) 1:= by
  obtain ⟨Z,hZ,H,hP,hS⟩:= walkerF (k:=k) he _ _ hp
  have hh (i:Wall w 1): (1:ℝ)/(X.S.block (L i).i).val≤1:= one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast (X.S.block _).property) |>.trans (by simp)
  let Q i:= curse m (m+e-r) r d (U i) (Z i)
  rw [show (fun i=>aboard d (Γ (L i)).tree _ - aboard d (babyQ G X (L i)) (U i e r)) = -Q from ?_]; swap -- set explicit
  · ext1 i; rw [abroad (hT i) h (X.S.block_odd _) (babyW (L i)) (he.fair _|>.ct) (hZ.status (fun _=>T.pos _) i) (hS i), if_pos hm]; exact sub_sub_cancel_left ..
  exact (marry_for (Wall.plusOne X) hZ h (fun i=> X.S.block_odd ((L i).i)) (fun _=> T.pos _) (η:=1) zero_le_one le_rfl hh le_rfl hP H hx hm (d:=d)).neg

end work
end YM.RG08.Run
