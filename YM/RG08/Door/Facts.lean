import YM.RG08.Door.Oriel
/-!
# Supplies for canonical sector Rails. Coarse gauges and stencil choices.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain} {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
local notation "Ⓨ" => menu X
local notation "Δ" => chop X
-- K supplied & overlaps
abbrev Ae (T:Signals P Q E τ H Ω h hD):ReadsU F D R:= fun i=> startU Ω i (d.le_succ.trans hD) ((by norm_num : (0:ℝ)≤1/2).trans h)
abbrev Ye (X:Chain) (ν:G.ColorIndex)(Z:ChartRatio G){P:KPrices X.kernel}{Q:Lending G X.kernel}(T:Signals P Q E τ H Ω h hD) (t:Wings u 0):= stepboard X ν Z H Ω (d.le_succ.trans hD) h t.N t.i
abbrev Xe (T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(Z:ChartRatio G)(t: Wings u 1):= uprise (heights X ν Z t) (Ye X ν Z T t.up)
abbrev Te (T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(Z:ChartRatio G)(t: Wings u 1): Session (Letter F):= atlas H (Xe T ν Z t)
structure Tights (T:Signals P Q E τ H Ω h hD)(S: Prism G X.kernel g Q E)(ν:G.ColorIndex)(Z:ChartRatio G)(u:I→Windows) : Prop where
   hc:Circuit S ν Z u
   he:Enabled T u
   hh:d≤τ
   hs:G.Simple
   hv:X.Wake G
   hz:LocalRatio Z
   sound:Ω.Sound H
   pop: Bid.pop Ω
variable (he:Tights T S ν D' u)
include he
lemma Tights.firs (i : Wings u 0): Genuine H (Ye X ν D' T i):= decks X ν D' H Ω _ h P he.hv he.hz he.sound he.pop _ _ i.cut (show d ≤ _ from le_trans (Nat.le_add_right ..) (he.he.stepCap i.toLaunch))
lemma Tights.ran : Genuine H (Ae T):= section_genuine H Ω he.sound he.pop (d.le_succ.trans hD) h
lemma Tights.fair (i:Wings u 1) : Fair (heights X ν D' i):= fairground X ν D' he.hv he.hz i.cut
lemma Tights.lived (i:Wings u 1): Boards (Xe T ν D' i) := heart (he.fair i) h (he.firs i.up).toBoards
lemma Tights.reads (i:Wings u 1): Flash (X.S.block i.i) (Te T ν D' i) ∧ Xe T ν D' i=bureau (Ye X ν D' T i.low) (Te T ν D' i) := dice_step X ν D' H Ω _ h P he.hv he.hz he.sound he.pop _ _ i.cut (le_trans (Nat.le_add_right ..) (he.he.stepCap i.up.toLaunch))
set_option linter.unusedSectionVars false in
lemma Tights.rested (t)(m : Wings u 0→ℕ) : Tin (menu X) 1 (fun i:Wings u 0=>Ae T t e r) (fun i=> ώ T (m i)) := by -- will duplicate? unify
  obtain ⟨B,hB⟩:= start_lit Ω t (d.le_succ.trans hD) ((by norm_num : (0:ℝ)≤1/2).trans h) 1 zero_le_one e r
  exact Tin.soften (F:=fun v:Wings u 0=> Ae T t e r) (w:=1) ⟨_,Weighed.constant _ (Ink.nonneg hB),fun i=> Ink.raise hB (by simp)⟩ (fun i=> (tick_t T _).1.trans ((tick_t T _).2.trans (min_le_right ..)))
lemma Tights.prior (i : Wings u 1)(b c:Letter F) : ‖singSl (Te T ν D' i)⁻¹ b c‖ ≤ price_u T i.toLaunch := by
  apply T.posts _ _ (X.flight i.N i.i) (X.adm _) (he.he.stepCap i.up.toLaunch) _ (he.reads i).1 ?_ b c
  intro x y hp; obtain ⟨Z,hZ,HZ⟩:= demandPrint X ν D' P he.hv he.hz i.N i.i i.cut
  apply arch_turn H (X.flight i.N i.i) X.kernel.penalty Z (dance X ν D' i.N i.i) X.kernel.penalty_pos (X.adm _) (le_trans (Nat.le_add_right ..) (he.he.stepCap i.up.toLaunch)) (he.fair i) h he.sound he.pop _ hZ HZ (he.firs _) x y hp
lemma Tights.operator : Bucks τ E (menu X) (chop X (1/4)) (fun t:Wings u 1=>ώ T t.i) (fun t=>T.vi (X.J t.i)) (fun t=>ώ T (t.i+1)) (heights X ν D') (fun t=>heights X ν D' t.wingR) := book_f he.he he.hc he.hs he.hv he.hz
lemma Tights.walks (i:Wings u 1): ∃ Z:Cross (X.S.block i.i) (Candles G) (Loc G 1), Z.strip (ώ T i.i) (fundsTor G (P.b (X.J i.i)) (P.bill (X.J i.i)) _ X.kernel (X.trees i.i)) ∧ Speaks (babyQ G X i) Z (heights X ν D' i).tree := by
   obtain ⟨Z,hZ,H⟩:= earn G X i.N i.i he.hv i.cut P; exact ⟨_,strip_mono hZ (T.rose _) le_rfl,H⟩
variable {U:Wings u 1→ BoardU D R G}
lemma Tights.walkPays (hP:∀ i, Marvel m (U i))(hx:r≤τ+E)(hm :r≤m+e)(hp:∀ j< e,∀ k,Tin (menu X) (chop X θ) (fun i: Wings u 1=>U i j k) (fun i=>ώ T (i.i+1))) :
    Tin (menu X) (chop X θ) (fun i=> aboard d (heights X ν D' i).tree (U i e r)- aboard d (babyQ G X i) (U i e r)) (fun i=>ώ T i.i) := by
  choose Z hZ H' using he.walks
  have hz : SafeRow (menu X) 1 Z (fun i=>ώ T i.i) := ⟨_, he.hc.turn.transfer toLaunch,fun i=>by simpa only [Pi.one_apply,mul_one] using hZ i⟩
  rw [show (fun i=> aboard d (heights X ν D' i).tree _- aboard d (babyQ G X i) _) = -(fun i=> curse m (m+e-r) r d (U i) (Z i)) from funext fun i=>?_]
  · exact (tulip he.he Z hz U hx hm hp (he.operator.crop)).neg
  rw [abroad (hP i) h (X.S.block_odd _) (babyW i) (he.fair i).ct (hz.status (fun i=>T.pos _) i) (H' i),if_pos hm,Pi.neg_apply]; exact sub_sub_cancel_left .. 
end YM.RG08.Door
