import YM.RG08.Door.Facts
/-!
# Price absolute Wilson fields in the true stencil topology. Uncut forces only.
Outputs include ordered signatures (path-independent via profiles).
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
local notation "Ⓨ" => menu X
local notation "Δ" => chop X
local notation "U♭" => Wings u 1→BoardU D R G -- avoid binders section leak
-- canonical Gabs and λ fields
abbrev basinT (T:Signals P Q E τ H Ω h hD) (ν:G.ColorIndex)(D':ChartRatio G)(t: Wings u 0):ReadsU F D R:= Ye X ν D' T t-Ae T
-- canonical mark residual exp same.
variable (he:Tights T S ν D' u)
include he
local notation "Γ" => heights (u:=u) X ν D'
local notation "S♭" => basinT (u:=u) T ν D'
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "T♭" => Te (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Ҝ" => (Ae T)
lemma mist (i:Wings u 0) : Boards (S♭ i) ∧ ∀ b,auditT H F (S♭ i b)=0 := abstractMinor H (he.firs i) he.sound he.pop _ h
lemma resound (hk:e≤E)(b:Letter F) (hp: ∀ j l s, dag e (slot b) r j l s→ Cage T 0 S♭ Ξ T♭ j l s) : Tin Ⓨ 1 (fun i:Wings u 1=>fetchU (Γ i) (slot b) d (Υ i.up b) e r) (fun i=>ώ T i.i):= by
  let f i:= Υ (Wings.up i) b
  have hV i:= (he.firs (i:Wings u 1).up).rank b
  refine (forms_bucks he.operator ((slot_le _).trans he.hh) hk hV ?_ h (V:=f) ?_).one
  -- same f BOTH (diff=0). Right op applied to f irrelevant
  · exact hV
  intro j k ha; refine Twill.same ?_
  have hz:=he.rested (e:=j) (r:=k) b (fun i=>i.i+1)
  have ht := ((hp j (slot b) k (below ha)).first b rfl).lapP he.hc.M.crop (by norm_num) -- hp arguments
  rw [a_zero] at ht; convert ht.plus (hz.move Wings.low) (sh X) using 1
  funext i; exact (sub_add_cancel ..).symm
lemma clear1 : Rails 0 T S♭ Ξ (fun _:Wings u 1=> Ҝ) T♭ T♭ := by
  have hv b e r: Tin Ⓨ 1 (fun i:Wings u 1=> Ҝ b e r) (fun i=>ώ T (i.i+1)) := (he.rested b (fun i=>i.i+1) (e:=e) (r:=r)).move Wings.low
  have hB (b:Letter F) (e r:ℕ) : Tin Ⓨ 1 (fun i:Wings u 1=> aboard d (Γ i).tree (Ҝ b e r)) (fun i=>ώ T i.i):= (aboard_bucks he.operator (fun _=> he.ran.rank b) (fun _=> he.ran.rank b) h (Twill.same (hv b e r))).one -- n actually initial parameter e r not included. generalize
  refine {bound:=he.hh,small:=by norm_num, lam:=fun i=>mist he i|>.1, wave:=he.lived, eve:=fun _=>he.ran.toBoards, nullL:=fun i=>mist he i|>.2, shine:=fun i=>(he.reads i).1,inverse:=he.prior,pay:=?_,pruner:=fun _=>rfl,fuel:=fun e _ b r=>(he.rested b (fun i=>i.i) (e:=e) (r:=r)).move low, switch:=fun _ _ _ _ h=> by simpa only [a_zero] using h, stage:=?_,top:=?_,upgrade:=?_}
  · intro i; rw [(he.reads i).2,← bureau_add]; rw [show S♭ i.low+Ҝ=Υ i.low from sub_add_cancel ..]
  · intro e _ b r
    have hP(i:Wings u 0): S♭ i.roof b e r=0:= by
      unfold basinT; rw [Pi.sub_apply, Ye]; erw [step_top]; exact sub_self _ -- needs show Pi.sub nested
    simp_rw [hP]; exact Tin.zero
  · intro e b r hk hR hp
    let D i:= fetchU (Γ i) (slot b) d (Υ i.up b) e r
    have hp' i:= (mist he (i:Wings u 1).up).1.rank b
    have hZ := he.walkPays hp' (θ:=0) (r:=r) (by have hh:slot b≤τ:=(slot_le _).trans he.hh; omega) hR (fun j hj k=> ((hp j (slot b) k (Or.inl hj)).first b rfl).lapP he.hc.M.crop (by norm_num))
    have hz i:=formula_bucks (he.fair i) ((he.firs (Wings.up i)).rank b) h d e r
    let A i:= aboard d (Γ i).tree (Ҝ b e r)
    let V i:= aboard d (Γ i).tree (S♭ i.up b e r)-aboard d (babyQ G X i) (S♭ i.up b e r)
    rw [show (fun i=> _- aboard d (babyQ G X i) ((S♭ i.up) b e r))=V+A+D from funext fun i=>?_]
    · rw [a_zero]; rw [a_zero] at hZ; exact (hZ.plus (hB b e r) (sh X)).plus (resound he hk b hp) (sh X)
    have hP:= Needle.aboard_sub (X.S.block_odd _) h (he.fair i|>.ct) ((he.firs i.up).rank b|>.hem e r) ((he.ran.rank b).hem e r) d
    have ht : S♭ i.up b e r= Υ i.up b e r- Ҝ b e r:=rfl
    change _= V i+A i+D i
    unfold V; change Needle.push _ _ _ _ _ _ - _ = _; rw [hz i, ht,hP]; unfold A D; abel
  · intro e b r hk hm hp hx
    have hD:= resound he hk b hp
    have hz := hx.lapP he.hc.M.crop (by norm_num)
    rw [a_zero] at hz ⊢
    let H i:= Υ (Wings.up i) b
    have hh: Tin (menu X) 1 (fun i:Wings u 1=> H i e r) (fun i=> ώ T (i.i+1)):= by convert hz.plus (hv b e r) (sh X) using 1; funext i; exact (sub_add_cancel ..).symm
    rw [show (fun i:Wings u 1=> Ξ i b e r)=(fun i=>aboard d (Γ i).tree (H i e r)) + (fun i: Wings u 1=>fetchU (Γ i) (slot b) d (Υ i.up b) e r) from funext fun i=> ?_]; · exact ((aboard_bucks he.operator (fun i=>(he.firs _).rank b) (fun i=>(he.firs _).rank b) h (Twill.same hh)).one).plus hD (sh X)
    exact formula_bucks (he.fair _) ((he.firs _).rank b) h d e r
lemma cashIn (hk:e≤E) (b:Letter F) (r:ℕ): Tin (menu X) 1 (fun i:Wings u 0=> Υ i b e r) (fun i=>ώ T i.i) := by
  have ht:= (railway (clear1 he) he.he hk (slot b) r).first b rfl; rw [a_zero] at ht; convert ht.plus (he.rested b (fun i=>i.i) (e:=e) (r:=r)) (sh X) using 1; funext i; exact (sub_add_cancel ..).symm
lemma stakesPay (hk:e≤E) (b v: Letter F): Dig (menu X) 1 (fun i:Wings u 1=> hot (T♭ i) e v b) := by simpa only [a_zero] using (railway (clear1 he) he.he hk (slot b) (slot v)).knows b rfl v rfl
end YM.RG08.Door
