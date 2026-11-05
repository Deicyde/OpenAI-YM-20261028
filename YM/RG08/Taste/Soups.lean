import YM.RG08.Taste.Candy
/-!
# Compensation rates relative to unit of value of root inputs. Why actual chosen cutoff histories line up all renewal coefficients.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
variable {U V:J→ BoardU D R G} {p q:J→ℝ}{δ ρ y:J→ℝ}
section cost
local notation "℘₁" => call H F
lemma call_grad (A:ℕ)(U:BoardU D R G)(V:BoardU D R G)(hU:Marvel A U)(hp:Lank U)(he:Marvel A V)(ht:Lank V): ℘₁ U-℘₁ V=℘₁ (U - V) := by -- notation below
    ext1 i; unfold call; ext k; rw [Pi.sub_apply,map_sub,coeff_mk,coeff_mk,audit_sub H hU he hp ht, coeff_mk]; rfl
lemma call_pin (H:Aperture G P k E τ d D R)(p:Hol G)(U:J→BoardU D R G)(he:∀ i,Marvel τ (U i))(h:Audience y)(hz:e≤ E)(hp:∀ i≤e,∀ r,Card k y δ (fun j=> U j i r) 1) (b:Letter F) : Dig y δ (fun j=>coeff e (call p F (U j) b)) := by
    simp_rw [call,coeff_mk,auditT]; refine Dig.sums _ h (fun i hi=>?_); have he': i ≤ slot b:= mem_range_succ_iff.mp hi; split_ifs with hh; swap; exact Dig.zero
    have ht:e+i-slot b ≤ e:= by omega
    by_cases hv:i≤τ+E
    · exact cardDig p b (hp _ ht _) (le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (slot_le b)) hv) H.budget)
    rw [show (fun j=>invest p (U j (e+i-slot b) i) b)=0 from funext fun j=>?_]; · exact Dig.zero
    have he:= not_ne_iff.mp (mt ((he j).cap (e+i-slot b) i) (by omega)); rw [he]; exact invest_zero p b
lemma call_pair (θ:Aperture G P k E τ d D R)(H:Hol G)(h:Audience y)(hE:e≤E)(hu:∀ i,Marvel τ (U i))(hp:∀ i,Lank (U i))(he:∀ i,Marvel τ (V i))(ht:∀ i,Lank (V i))(hk:∀ i≤e,∀ r,Drum k y q p (fun j=> U j i r) (fun j=>V j i r) 1)(b: Letter F): Tonic y p q (fun i=>coeff e (call H F (U i) b)) (fun i=>coeff e (call H F (V i) b)):= by
    refine ⟨call_pin θ H _ hu h hE (fun j hj r=>hk j hj r|>.first) b,call_pin θ H _ he h hE (fun j hj r=>hk j hj r|>.second) b,?_⟩
    rw [show _-_ = (fun i:J=>coeff e (call H F ((U-V) i) b)) from funext fun i=>?_]; swap
    · rw [Pi.sub_apply,Pi.sub_apply, ← call_grad τ (U i) (V i) (hu _) (hp _) (he _) (ht _),Pi.sub_apply, map_sub]
    exact call_pin θ H (U-V) (fun i=>by rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus (hu i) (choir_weight (he i) _)) h hE (fun i hi r=> (hk i hi r).funds) b
variable {M A:J→Native (Letter F)}{Z H': J→ ReadsU F D R} -- shadow name
lemma heads_up (hp:∀ i,Boards (Z i))(hk:∀ i,Boards (H' i))(hz:Audience y)(he:0 ≤ q)(ht:∀ i≤e,∀ b r,Drum k y q 1 (fun j=>Z j b i r) (fun j=> H' j b i r) 1)(hm:∀ i≤ e,∀ b,Tonic y p q (fun j=>coeff i (M j b)) (fun j=>coeff i (A j b))) : Drum k y q p (fun j=>edgeBook (Z j) (M j) e r) (fun j=>edgeBook (H' j) (A j) e r) 1 := by
   have hx i: Boards (Z i-H' i):= slate_minus (hp i) (hk i)
   refine ⟨by rw [← mul_one p]; exact elig hz zero_le_one (fun i hi b r=> (ht i hi b r).first) hp (fun i b hv=> (hm i (by omega) b).one),by rw [← mul_one p]; exact elig hz zero_le_one (fun i hi b r=> (ht i hi b r).second) hk (fun i b hv=> (hm i (by omega) b).two),?_⟩
   let X i:= edgeBook (Z i-H' i) (A i); let Y i:= edgeBook (Z i) (M i-A i)
   rw [show _-_ =(fun i=>X i e r)+(fun i:J=>Y i e r) from funext fun i=> congr_fun (congr_fun variance_b e) r]
   have h : Card k y (p*q) (fun i=> X i e r) 1:= elig hz he (fun i hi b r=> by have hh:= ht i hi b r|>.funds; rw [mul_one] at hh; exact hh) hx (fun i b hv=> (hm i (by omega) b).two)
   rw [mul_comm] at h; refine h.more ?_ zero_le_one hz; rw [← mul_one (q*p)]; refine elig hz zero_le_one (fun i hi b r=>(ht i hi b r).first) hp (fun i b hv=> ?_); simp_rw [Pi.sub_apply,_root_.map_sub]; exact (hm i (by omega) b).both
lemma drumCut {α:J→Type}{Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{F U A B:∀ i, Rooted Y (α i) r}(h:Drum k y q p F U δ)(hp:Drum k y q p A B δ)(he:Audience y)(hx:0≤δ): Drum k y q p (F-A) (U-B) δ:= by
    rw [sub_eq_add_neg F, sub_eq_add_neg U]; apply Drum.more h _ hx he
    exact ⟨hp.first.neg,hp.second.neg,by rw [show -A- -B= -(A-B) by abel]; exact hp.funds.neg⟩
end cost
abbrev wallD:= wallY X (b:=w) (n:=n)
abbrev wallQ (p:J→ℝ)(i:Wall w n):= p i.a
abbrev topY (X:Chain)(w:J→ ShoreP u) (i:J):= wallY X (Wall.tip w i)
local notation "Υ" => phase0 ν D' T
lemma south (he:Tights T S ν D' u)(hQ:∀ i,(w i).rate X ≤ q i)(hk:e≤E)(b:Letter F)(k r:ℕ): Drum k (wallY X) (wallQ q) 1 (fun i:Wall w 0=> (Υ (offerD w) i) b e r) (fun i=> Υ (offerF w) i b e r) 1 := by
   have ht:= Lens_pay he hk b r k; have hp:= ht.mold (Wall.world (n:=0) (b:=w))
   exact ⟨hp.first.tax (Wall.invested _) (Wall.plusOne X),hp.second.tax (Wall.invested _) (Wall.plusOne X), ((hp.funds.tax (Wall.invested X) (Wall.plusOne X)).raise (fun i=> mul_le_mul_of_nonneg_right ((Wall.loan X i).trans (hQ _)) zero_le_one))⟩
-- compact phrasing relative to Lives. No moment assumptions on M inputs apart from actual Ward/Lank. Counts for any works.
structure Mirth (X:Chain)(U V:J→BoardU D R G)(w:J→ ShoreP u)(p q:J→ℝ)(E k t:ℕ):Prop where
   has i : Marvel t (U i)
   does i : Lank (U i)
   owes i : Marvel t (V i)
   lives i : Lank (V i)
   price : 0 ≤ p
   peak i : Pill.ShoreP.rate (w i) X ≤ q i
   drums i : i ≤ E→∀ r, Drum k (topY X w) q p (fun j:J=> U j i r) (fun j=>V j i r) 1
lemma cWiz (h : Mirth X U V w p q E k τ) : 0≤q:= fun i=> ((gain_pos ..).le).trans (h.peak i)
section
variable (he : Tights T S ν D' u)(hh:Heirs T' u)(hp:Mirth X U V w p q E k τ)
local notation "[↓]" => offerD w
local notation "[↑]" => offerF w
local notation "◍" => wallY X
local notation "▽" => wallQ (w:=w) q
local notation "▵" => strideP X w p
local notation "Ⓒ" => curtain ν D' T [↓] U
local notation "ℂ'" => curtain ν D' T [↑] V
include he T' hp
lemma curtain_p (hE:e≤E) : Drum k (topY X w) q p (fun i=>Ⓒ i e r) (fun i=> ℂ' i e r) 1:= by
  have hP:Audience (topY X w):= fun i=>Wall.plusOne X _
  have hq:= hp.price
  let Z i:=Υ [↓] (Wall.tip w i); let W i:= Υ [↑] (Wall.tip w i)
  refine drumCut (hp.drums e hE r) (heads_up (Z:=Z) (H':=W) (fun i=> (he.firs _).toBoards) (fun i=>(he.firs _).toBoards) hP (cWiz hp) (fun i hi b r=> Drum.mold (south he hp.peak (hi.trans hE) b k r) (Wall.tip w)) (fun i hi b=> call_pair T' H hP (hi.trans hE) hp.has hp.does hp.owes hp.lives (fun j hj r=> hp.drums j ((hj.trans hi).trans hE) r) b)) hP zero_le_one
include hh
lemma rise_k (hk:e≤ E) (r): Drum k ◍ ▽ ▵ (fun i=> riseV ν D' T [↓] U i e r) (fun i=> riseV ν D' T [↑] V i e r) 1 := by
    have he₁ i:= pin H (hp.has i) (hp.does i) (he.firs ((offerD w).part (Wall.tip w i))); have he₂ i:=pin H (hp.owes i) (hp.lives i) (he.firs ((offerF w).part (Wall.tip w i)))
    obtain ⟨A,B,D⟩:= balances he hh (le_refl τ) he₁ he₂ hp.price (cWiz hp) (fun i=>hp.peak i.a) (fun i hi r=> curtain_p he hp hi (T':=T')) hk r -- ignored? Mirth uses T' dependent k; implicit section of lemma curtain_p Lean won't include T'
    refine ⟨B.cards,D.cards,?_⟩; rw [show (wallQ (w:=w) (n:=0) q)*▵=strideP X w (q*p) from funext fun i=>by simp only [Pi.mul_apply,strideP,wallQ,mul_assoc]]; exact A.cards
lemma shift_k (hE:e≤E)(b: Letter F): Tonic ◍ ▵ ▽ (fun i=>coeff e (shiftV ν D' T [↓] U i b)) (fun i=> coeff e (shiftV ν D' T [↑] V i b)):= by
    let A:=riseV ν D' T [↓] U; let B:=riseV ν D' T [↑] V
    have he₁ i:=pin H (hp.has i) (hp.does i) (he.firs ([↓].part (Wall.tip w i))); have he₂ i:=pin H (hp.owes i) (hp.lives i) (he.firs ([↑].part (Wall.tip w i)))
    let Y:= arcV ν D' T [↓] U; let Z:= arcV ν D' T [↑] V
    have hK(i):=barriers ν D' T [↓] U he hp.has hp.does|>.zone i; have hL(i):=barriers ν D' T [↑] V he hp.owes hp.lives|>.zone i
    refine call_pair T' H (U:=Y) (V:=Z) (Wall.plusOne X) hE (fun i=>crest_u (he.fair _) h (hK _).hU) (fun i=>crest_l (he.fair _) h (hK _).hU (hK _).paid) (fun i=>crest_u (he.fair _) h (hL _).hU) (fun i=>crest_l (he.fair _) h (hL _).hU (hL _).paid) (fun j hj r=>?_) b
    obtain ⟨K,W,L⟩:= balances he hh (le_refl τ) he₁ he₂ hp.price (cWiz hp) (fun i=>hp.peak i.a) (fun i hi r=> curtain_p he hp hi (T':=T')) (hj.trans hE) r --
    refine ⟨W.univ,L.univ,?_⟩; rw [show (wallQ (w:=w) (n:=1) q)*▵=strideP X w (q*p) from funext fun i=>by simp only [Pi.mul_apply,strideP,wallQ,mul_assoc]]; exact K.univ
end
end YM.RG08.Taste
