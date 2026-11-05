import YM.RG08.Pill.Zoar
/-!
# Common-variable product costs on entire announced scope. True lengths. Sending formal matrix from coarse to upper mesh, inert tests and diagrams in reference.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I:Type}{u:I→Windows}
section gauges
variable (σ: ShoreP u)
def face (i:ℕ)(ht:i<σ.city): Wings u 1 := by
  refine ⟨⟨σ.next.b,σ.low+i,σ.ready.trans (Nat.le_add_right ..)⟩,σ.next.N,σ.next.M,le_trans ?_ σ.next.cut, σ.next.side⟩; unfold ShoreP.city at ht; change σ.low+i+1≤ σ.next.i; omega
def walker (i:ℕ)(ht:i<σ.city) : Roam u:= ⟨(face σ i ht).low,σ.next.fromK,σ.next.ends⟩
def ShoreP.rate (X:Chain):= gain X.S (1/4) (max σ.next.i σ.next.main) σ.next.N
lemma nearWalk (X:Chain)(i:ℕ)(hp:i<σ.city) : (walker σ i hp).measure X ≤ σ.y X := by
    apply src_cost σ X (walker σ i hp) rfl (show σ.low ≤ σ.low+i from Nat.le_add_right ..)
    unfold ShoreP.city at hp; change σ.low+i≤ σ.next.i; omega
lemma vigor (X:Chain)(i:ℕ)(hp:i<σ.city): let v:= face σ i hp; chop X (1/4) v≤ ShoreP.rate σ X ∧ (walker σ i hp).cost X ≤ σ.rate X := by
   intro v; unfold ShoreP.city at hp; let x:=max σ.next.i σ.next.main; have H: v.i ≤ x := (le_trans (show σ.low+i≤ σ.next.i by omega) (le_max_left ..))
   have h y (he:y ≤ x) : gain X.S (1/4) y σ.next.N ≤ σ.rate X := Real.exp_monotone (by have hh:=age_scale_mono X.S he; dsimp only [x] at hh; linarith)
   exact ⟨h _ H,h _ (le_trans (max_le H (show (walker σ i hp).main ≤ _ from le_max_right ..)) le_rfl)⟩
end gauges


variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
local notation "Z" => ladder X ν D' N
-- ordering coarse-l severe. prefix products starting lower i, priced upper/store with reference k
-- using unshifted at g. T index from DATA not T-Signals
def firstT (x:ℕ→Session (Letter F))(p:ℕ→PowerSeries ℝ)(i n:ℕ): Session (Letter F):= turn (fun j=> awake (p (i+j)) ((x (i+j))⁻¹)) n
def trump (T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(D':ChartRatio G)(N i k j:ℕ): Session (Letter F):= firstT (dice X ν D' H Ω (d.le_succ.trans hD) h N) (fun j=> ladder X ν D' N j k) i j
private abbrev Si (u:I→Windows):=DeckSeat (ShoreP.city (u:=u)) 1
variable (ht:Tights T S ν D' u)
def fans (T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(D':ChartRatio G)(i:ShoreP u)(n:ℕ): Session (Letter F) := awake (ladder X ν D' i.next.N (i.low+n) i.next.main) ((dice X ν D' H Ω (d.le_succ.trans hD) h i.next.N (i.low+n))⁻¹) -- hD inference?
private def flows (T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(D':ChartRatio G)(i:ShoreP u)(n:ℕ): Session (Letter F) := awake (ladder X ν D' i.next.M (i.low+n) i.next.main) ((dice X ν D' H Ω (d.le_succ.trans hD) h i.next.M (i.low+n))⁻¹) --
include ht
lemma framesB (hk : e≤E): Lying (fun i:Si u=> i.i.y X) (fun i=>i.i.rate X) (fun i=> hot (fans T ν D' i.i i.k) e) (fun i=>hot (flows T ν D' i.i i.k) e) := by
  let y t:= (t:Si u).i.y X
  let b i:= face (i:Si u).i i.k i.hw
  have ha: Audience y:=fun i=> city_one ..
  have hm : Weighed y (fun t=>menu X (b t)) := (show Weighed y y by simpa only [pow_one] using Weighed.power y ha 1).mono (fun _=> zero_le_one.trans (sh X _)) (fun i=> nearWalk i.i X i.k i.hw)
  apply awake_b (M:=fun i=> (Te T ν D' (b i))⁻¹) (A:=fun i=> (Te T ν D' (b i).wingR)⁻¹) (B:=fun i=> afternoons (rootsRatio X ν D' i.i.next.N (i.i.low+i.k) i.i.next.main)) (C:=fun i=>afternoons (rootsRatio X ν D' i.i.next.M (i.i.low+i.k) i.i.next.main)) ha
  · intro j hj x v; exact leaseT (Summit.Lease.whirls (cashOut ht (hj.trans hk) x v) b) ha hm (fun i=>(vigor i.i X i.k i.hw).1)
  intro i hi; have hQ:= prices_come ht.hc ht.hv ht.hz ht.hs (hi.trans hk); exact leaseT (Summit.Lease.whirls hQ (fun t:Si u=> walker t.i t.k t.hw)) ha hm (fun i=> (vigor i.i X i.k i.hw).2)
lemma trump_pay (hk:e≤E): Lying (fun i:ShoreP u=> i.y X) (fun i=> i.rate X) (fun i=>hot (trump T ν D' i.next.N i.low i.next.main i.city) e) (fun i=>hot (trump T ν D' i.next.M i.low i.next.main i.city) e) := by
  let S:=fans (u:=u) T ν D'; let A:=flows (u:=u) T ν D'
  have h:= ticker (L:=ShoreP.city (u:=u)) (M:=S) (T:=A) (fun i=>city_one i X) (fun i=> show 0 ≤ i.rate X from (gain_pos ..).le) (subsegment X) (fun i j=> X.S.block (i.low+j)) (fun i k he=> show Thick _ _ from awake_z ((ht.reads (face i k he)).1) _) (fun i k he=> show Thick _ _ from awake_z ((ht.reads (face i k he|>.wingR)).1) _) (fun i (hi:i ≤ e)=> framesB ht (hi.trans hk))
  exact fun i j=> Summit.Lease.whirls (h i j) (fun i=> (⟨i,i.city,le_rfl⟩:DeckSeat (ShoreP.city (u:=u)) 0))
end YM.RG08.Pill
