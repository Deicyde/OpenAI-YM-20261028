import YM.RG08.Needle.Fonts
/-!
# Priming the independent transition graph at the same g
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries Conductor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F: Labels.Frame G d}
variable {T:Session (Letter F)} {φ : ReadsU F D R}{b: Letter F}
variable {V U : BoardU D R G} {Ω:SectionData F}
-- Actual square ratio correction post-step. Keep positive linear coefficient one.
variable (G) in
structure StripU (L : Side) where
  cv : Row (Fink G L) (Fink G L)
  tree : Cross L (Loc G 1) (Loc G 1)
  song : Canticle (Park G L)
  scale : PowerSeries ℝ

variable {Q:StripU G L} (H:Hol G)

def push (Q:StripU G L)(τ d : ℕ)(U:BoardU D R G):BoardU D R G :=
    hill Q.scale (filop Q.cv Q.tree Q.song none τ d U)
def uprise (Q:StripU G L)(φ:ReadsU F D R)(i:Letter F): BoardU D R G := push Q (slot i) d (φ i)
def mapU (Q:StripU G L)(φ:ReadsU F D R) : Session (Letter F):= atlas H (uprise Q φ)
def repose (Q:StripU G L) (φ:ReadsU F D R) : ReadsU F D R := bureau (uprise Q φ) (mapU H Q φ)⁻¹
structure Fair (S:StripU G L) : Prop where
  odds: Odd L.val
  cm:Whole S.cv
  ct:Whole S.tree
  tune i j:Tunable (S.song i j)
  bought i j:Glows (S.song i j)
  lived:Decked S.song
  once:constantCoeff S.scale=1
  pass {D:ℕ}{R:ℝ} {d:ℕ} {τ:ℕ} {V:BoardU D R G}: 1/2≤R→Marvel τ V→Marvel τ (filop S.cv S.tree S.song none τ d V)
lemma crest_u (he:Fair Q)(hr:1/2≤R)(hp:Marvel τ V): Marvel τ (push Q τ d V) := ridges Q.scale he.once (he.pass hr hp)
lemma crest_l (he:Fair Q)(hr:1/2≤R)(hp:Marvel τ V)(hU:Lank V): Lank (push Q τ d V) := fun i j=> by unfold push Tall.hill; exact polished_sum fun k _=> polished_scale (capstan he.cm he.ct hp.cap he.odds hp.hem he.tune he.lived hr he.bought hU _ k j) _ -- fix
lemma heart (he:Fair Q)(hr:1/2≤R)(hp:Boards φ): Boards (uprise Q φ):= ⟨fun i=>crest_u he hr (hp.rank i),fun i=>crest_l he hr (hp.rank i) (hp.paid i)⟩
lemma filament_tops {X': Cross L (Loc G 1) (Loc G 1)}{Z:Cross L (Candles G) (Loc G 1)}(he:Fair Q)(hr:1/2≤R)(hp: Marvel τ V)(hx:Whole X')(hy:Whole Z)(hz:Speaks X' Z Q.tree): push Q τ d V 0 τ=aboard d X' (V 0 τ) := by -- fix binders
  rw [push,ridge _ he.once]; simp only [range_zero,sum_empty,add_zero]
  rw [opening he.cm he.ct hp.hem hp.cap hr he.odds he.tune he.lived,almost Q.tree he.odds hr hp.cap hp.hem he.cm he.lived he.tune,spring_zero (scan_whole he.ct),add_zero,abroad hp hr he.odds hx he.ct hy hz, if_pos (by omega),add_zero,tsub_self, curse]
  rw [Finset.sum_eq_zero, smul_zero, sub_zero]; intro i _; refine Finset.sum_eq_zero fun k hk=> ?_; unfold moreU; rw [if_neg (by have h:=mem_range.mp hk; omega),rue_empty he.odds hr hy]
lemma map_d (he:Fair Q)(hr:1/2≤R)(hv: Boards φ) : Dilation (mapU H Q φ):= by
  refine ⟨fun i b v=> ?_⟩; unfold mapU; rw [atlas_fees]; intro hp; exact le_of_not_gt (fun h=> hp (audit_cap H ((heart he hr hv).rank v).cap b (by omega)))
lemma arch_turn (P:Flight j k)(s:ℝ)(Z:Cross P.L (Candles G) (Loc G 1)) (Q:StripU G P.L) (hs:0<s)(ht:4≤k)(hq:d≤j)
    (he:Fair Q)(hr:1/2≤R)(hp:Ω.Sound H)(hB:Bid.pop Ω)(hh:d≤D)(hZ:Whole Z)(hT:Speaks (painted G (Carrier.linesOf P s)) Z Q.tree) (hx:Genuine H φ) (i b:Letter F)(ho:slot i=slot b) : hot (mapU H Q φ) 0 b i=leadingV H Ω hh hr P s i b := by
  unfold mapU; rw [atlas_fees]; let Q':= painted G (Carrier.linesOf P s)
  have hc(v : BoardU D R G): auditT H F v 0 b= invest H (v 0 (slot i)) b:= by
    unfold auditT; rw [Finset.sum_eq_single_of_mem (slot i) (by rw [ho]; simp),if_pos (by omega),show 0+slot i-slot b=0 from by omega]; intro j hj hz; rw [if_neg (by have he:=mem_range.mp hj; omega)]
  have hm:Whole Q':=spray_whole P s hs ht; have hy:=(abstractMinor H hx hp hB hh hr)
  let p':=(show (0:ℝ)≤R from (by norm_num : (0:ℝ)≤1/2).trans hr)
  let S:= startU Ω i hh p'
  let W:=φ i-S
  rw [hc,uprise,filament_tops he hr (hx.rank i) hm hZ hT]; unfold leadingV
  have hf: Marvel (slot i) W:= hy.1.rank i; have hw: Marvel (slot i) S:=start_duty Ω i _ _ hB H hp; have hj:= hf.hem 0 (slot i); have hN:= hw.hem 0 (slot i)
  rw [show φ i 0 _= W 0 (slot i)+S 0 (slot i) from (sub_add_cancel ..).symm, aboard_add he.odds hr hm hj hN]; let L: Side := P.L
  let X (V:BoardU D R G): EnvelopeU D R G (slot i) := aboard d Q' (V 0 (slot i)); have he' V (h:Marvel (slot i) V): Toute (X V):=tot_weight (tot_sums (F:=fun p : Site L=> Vale.halo p (V 0 (slot i)) Q') (fun j _=>paid_color (seat_made h) _ (Carrier.stored P s hs ht) j he.odds hr)) _
  have hu:Polished (W 0 (slot i)):= hy.1.paid i 0 (slot i); have hg:Abates (W 0 (slot i)) (d+1):= held H (h:=hf) (hp:=show Lank W from hy.1.paid i) (ht:=show auditT H F W=0 from hy.2 i) _ _ -- fix
  change invest H (X W+X S) b= invest H (X S) b
  rw [invest_more H b (he' W hf) (he' S hw) (all_aboard he.odds hr hm hu) (all_aboard he.odds hr hm (start_lank Ω i _ p' _ _))]; unfold X; rw [payout H hr P hs ht hq hu (seat_made hf) hg b (b.bill.trans (Nat.le_succ d)) ho.symm d,amount_empty H hu (seat_made hf) hg b (b.bill.trans_lt (Nat.lt_succ_self _)) ho.symm,mul_zero,zero_add]
lemma issued (P:Flight j k)(s:ℝ){Q:StripU G P.L} (hs:0<s)(ht:4≤k)(hq:d≤j)
    (he:Fair Q)(hr:1/2≤R)(hp:Ω.Sound H)(hB:Bid.pop Ω)(hh:d≤D)(hZ: ∃ Z,Whole Z ∧ Speaks (painted G (Carrier.linesOf P s)) Z Q.tree)(hv:Genuine H φ) :
    Flash P.L (mapU H Q φ) := by
  obtain ⟨Z,hZ,HZ⟩:=hZ
  refine ⟨map_d H he hr hv.toBoards,fun i=> ?_,fun i j hi hPx hz=>?_⟩
  · rw [arch_turn H P s Z Q hs ht hq he hr hp hB hh hZ HZ hv i i rfl, capitalT i hh hr H hp hB P hs ht hq i rfl le_rfl, if_pos rfl]; rfl
  by_contra! hn
  have hP:=hp
  rw [arch_turn H P s Z Q hs ht hq he hr hP hB hh hZ HZ hv j i hz.symm,capitalT j hh hr H hP hB P hs ht hq i hz.symm hn,if_neg hi] at hPx
  exact hPx rfl
lemma fountain (he:Fair Q)(hr:1/2≤R)(h:Boards φ)(hT:Flash L (mapU H Q φ)) : Genuine H (repose H Q φ) ∧ uprise Q φ=bureau (repose H Q φ) (mapU H Q φ):= by
  have hh:=heart he hr h
  refine ⟨⟨stays hh (fireplace hT),?_⟩,?_⟩
  · unfold repose; rw [tells H hh]; exact Matrix.mul_nonsing_inv _ (recoupC hT)
  unfold repose; rw [← bureau_acts, Matrix.nonsing_inv_mul _ (recoupC hT),bureau_one]
end YM.RG08.Needle
