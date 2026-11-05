import YM.RG08.Run.Haven
/-!
# Segment statutes. Clocks with only arbitrary-end misstated hopes won't apply; pricing depends on reference center.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill
open scoped BigOperators Topology Real ContDiff
open Wings
variable {I J:Type}{u:I→Windows}{b: J→ ShoreP u}{n:ℕ}
-- enumeration zero at low. Opp facing.
structure Wall (b:J→ShoreP u)(n:ℕ) where
  a : J
  i : ℕ
  first : (b a).low ≤ i
  last : i+n≤(b a).next.i
variable (X:Chain)
def wallY (t:Wall b n):= (b t.a).y X
def tiltP (t:Wall b n):= (b t.a).rate X
namespace Wall
def world (t:Wall b n): Wings u n:= let V:= (b t.a).next; ⟨⟨V.b,t.i,(b t.a).ready.trans t.first⟩,V.N,V.M, t.last.trans V.toWings.cut,V.side⟩
def roof (t:Wall b 1):Wall b 0:= ⟨t.a,t.i+1,t.first.trans (Nat.le_succ _),t.last⟩
def low (t:Wall b 1) : Wall b 0:= ⟨t.a,t.i,t.first,(Nat.le_succ _).trans t.last⟩
def tip (b:J→ShoreP u)(a:J): Wall b 0:=⟨a,(b a).next.i,(b a).init,le_rfl⟩
lemma owed (t:Wall b n): menu X t.world ≤ wallY X t := by
    let v : Wings u 0:= ⟨t.world.toLaunch,t.world.N,t.world.M,(Nat.le_add_right t.i n).trans t.world.cut,t.world.side⟩
    let M: Roam u:= ⟨v,(b _).next.fromK,(b _).next.ends⟩; exact src_cost (b t.a) X M rfl t.first ((Nat.le_add_right _ n).trans t.last)
lemma loan (t:Wall b n): chop X (1/4) t.world ≤ tiltP X t:= by
    let q:= (b t.a); apply Real.exp_monotone; change -(1/4:ℝ)*(X.S.scale q.next.N-X.S.scale t.i) ≤ -(1/4:ℝ)*(X.S.scale q.next.N-X.S.scale (max q.next.i q.next.main)); have he:t.i≤ q.next.i:= (Nat.le_add_right _ n).trans t.last; linarith [age_scale_mono X.S (he.trans (le_max_left q.next.i q.next.main))]
lemma plusOne : Audience (wallY X (b:=b) (n:=n)) := fun _=> city_one ..
lemma invested : Weighed (wallY X (b:=b) (n:=n)) (fun i=> menu X i.world):= (show Weighed (wallY X (b:=b) (n:=n)) (wallY X) by simpa only [pow_one] using Weighed.power (wallY X (b:=b) (n:=n)) (plusOne X) 1).mono (fun i=> zero_le_one.trans (Wings.sh X _)) (owed X)
-- iterative pressure
lemma gain_fewer {c:ℝ} (hp:c ≤ (1/2:ℝ)) (t:Wall b 1) :
   gain X.S (1/2) t.i (t.i+1) ≤ gain X.S c t.i (t.i+1):= by
   apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (age_scale_mono _ (Nat.le_succ _)))
end Wall
section tariff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l s :ℕ}{R θ A C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
-- API transfer to segment families
lemma Card.tax {α: I→Type}{Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{y v δ w:I→ℝ}{F:∀ i,Rooted Y (α i) r}(h:Card k y δ F w)(he: Weighed v y)(hp:Audience v): Card k v δ F w := ⟨_,he.sway hp h.money.choose_spec.1,h.money.choose_spec.2⟩
variable {α β : Wings u n → Type} {w : Wings u n→ℝ} {η v : Wall b n→ℝ}
lemma knit_h {F H : ∀ i,Row (α i) (β i)} (hp : ∀ t, chop X (1/4) (Wall.world (b:=b) t)≤η t)
    (hx:RowBoth (menu X) (chop X (1/4)) F H w): RowBoth (wallY X) η (fun t=> F t.world) (fun t=> H t.world) (fun t=> w t.world) := by
   have ht {F: ∀ i,Row (α i) (β i)} {v:Wings u n→ℝ}(h: SafeRow (menu X) v F w):SafeRow (wallY X) (fun i:Wall b n=> v i.world) (fun i=> F i.world) (fun i=> w i.world):= ⟨_,(Wall.invested X).sway (Wall.plusOne X) (h.choose_spec.1.transfer Wall.world),fun i=> h.choose_spec.2 i.world⟩
   exact ⟨ht hx.fresh,ht hx.again,(ht hx.moves).raise hp⟩
variable (he:Tights T S ν D' u)
local notation "Ⓨ" => wallY (b:=b) X
local notation "Δ" => chop X (1/4)
local notation "Γ" => heights X ν D'
include he
lemma billsT (b:J→ShoreP u){δ: Wall b 1→ℝ}(hp:∀ i, Δ (i.world)≤δ i) k : LensP k E τ (wallY X) δ (fun i=>T.vi (X.J i.i)) (fun i=> Γ i.world) (fun i=>Γ i.world.wingR):= by
   let B:=he.operator; have hh: Weighed (wallY (b:=b) (n:=1) X) (fun i=> menu X i.world):= Wall.invested X
   have ht(t:Wall b 1):0<T.vi (X.J t.i):=(T.pos _).trans_le (tick_t T _|>.1)
   have hx:Audience (wallY (b:=b) (n:=1) X):=Wall.plusOne X
   have hz:Weighed (wallY X) (fun i:Wall b 1=> (T.vi (X.J i.i))⁻¹):= (hh.sway hx (he.he.costs.transfer (fun i:Wall b 1=> i.world.toLaunch))).mono (fun i => inv_nonneg.mpr (ht i).le) (fun i=> inv_anti₀ (T.pos _) (tick_t T _|>.1))
   refine ⟨fun i=>B.faith _,fun i=> B.bond _,hx,hh.sway hx (B.crop.transfer Wall.world), knit_h hp B.hessian,knit_h hp B.meansT,?_,fun e hk=> leaseT (Summit.Lease.whirls (B.castG e hk) Wall.world) hx hh hp,ht,utterBuy k hz (fun i=> B.hv i.world),fun i=>le_trans (B.hs _) (hp i)⟩
   intro e hk n hl r
   have he:= RG08.Both.mold (B.ribs e hk n hl r) (Wall.world (b:=b)); exact ⟨he.fresh.age hh hx,he.again.age hh hx, ((he.moves.age hh hx).raise hp)⟩
end tariff
end YM.RG08.Run
