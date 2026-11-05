import YM.UVExtension.Camp.Buckles
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open Oriel Oriel.Charted Guild Tabernacle Above Spire Spire.Fitted Dales Camp.Cart
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A}
    {hG:G.Simple}(S: Uses R hG)
local notation "T!"=> A.B.a
local notation "CST"=> S.grove.pledge
variable (n:ℕ)(H : Sign S) (w:∀ b, PlotN b) (hp:∀ b:ℕ,w b∈Harbor b)(ht:∀ b, Light b (w b))
variable (hw:Charting w) (hC : Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha)

def rose (m:ℕ) : WordsI S m n:=fun i=> (S.fits i n).graceT (w i) m
def cup (m k:ℕ) (h:m≤ k): WordsI S m n:= Nat.decreasingInduction (motive:=fun m _=> WordsI S m n) (fun i _ x=> wood S (centers w S (i+1)) i n x) 0 h
lemma chase (i:ℕ): ∀ k m (h:k< m), cup S n w k m h.le i= wood S (centers w S (k+1)) k n (cup S n w (k+1) m h) i:=fun k m h=> congr_fun (Nat.decreasingInduction_succ_left _ _ (show k+1 ≤ m from h) _) _
-- along real coordinates get renewal again for cup.Journal. measure contraction not heuristic. 
include hp ht
lemma gains (m i:ℕ)(hi:m ≤ i): play T! i _ (S.cart i n) (w i) m hi= place A.B.a m n ((S.fits i n).W m) (rose S n w m i):= by
   unfold rose Fitted.graceT; rw [dif_pos hi]; exact ((S.fits i n).officious (S.cart i n) (S.token i n) (hp i) (ht i) m hi).2
private def up (k i:ℕ) (h:k ≤ i)(x:Chest S k n i):= ((node i (w i) k h).re,x)
lemma polars {m i}(hi:m ≤ i)(x: Chest S m n i)(he: ‖place T! m n _ x‖≤Camp.soft): river T! m n _ (up S n w m i hi x) = (node i (w i) m hi, place T! m n _ x)∧ river T! m n _ (up S n w m i hi x) ∈ Grip:=by
  let K:= river T! m n ((S.fits i n).W m); let p:= node i (w i) m hi
  have hz: K (up S n w m i hi x)=(p,place T! m n _ x):=by
    apply Prod.ext
    · change Complex.ofReal p.re=p; have hh:= Complex.re_add_im p; rw [show p.im=0 from ht i _, Complex.ofReal_zero,zero_mul,add_zero] at hh; exact hh
    rfl -- indent
  rw [hz]; refine ⟨rfl,mem_ball_zero_iff.mpr ?_⟩; exact max_lt ((norm_le_pi_norm (w i) _).trans_lt ((mem_closedBall_zero_iff.mp (hp i)).trans_lt (by norm_num [rad,Oriel.rim]))) (he.trans_lt (by norm_num [Camp.soft,Oriel.rim]))

lemma purchase (m k:ℕ)(h:m<k) (i:ℕ)(hh:k≤ i) (x:WordsI S (m+1) n) (he:‖drawerE S i (m+1) n (x i)‖≤ Camp.soft):
    ‖drawerE S i m n (wood S (centers w S (m+1)) m n x i)‖≤ Camp.soft ∧ chestR S (centers w S (m+1)) m n x i ∧ ‖drawerE S i m n (wood S (centers w S (m+1)) m n x i)-drawerE S i m n (rose S n w m i)‖ ≤ Camp.soft*‖drawerE S i (m+1) n (x i)-drawerE S i (m+1) n (rose S n w (m+1) i)‖:= by
    let C:=S.fits i n; let J:= S.cart i n; have hV : m < i:=lt_of_lt_of_le h hh
    let v:= up S n w (m+1) i hV (x i); let z:= river T! (m+1) n (C.W (m+1)) v; have hz:=polars S n w hp ht hV (x i) he
    let g:= play T! i _ J (w i); let p:= pivot T! i _ J (w i) (m+1) hV
    have ha k (hi:k≤ i): place T! k n (C.W k) (rose S n w k i) = g k hi:= by
       unfold rose Fitted.graceT; rw [dif_pos hi]; exact ((C.officious J (S.token ..) (hp i) (ht i) k hi).2).symm
    let w0:= centers w S (m+1) i; have hl:w0=lock R (w i) (m+1) hV:=dif_pos (show m+1≤ i from hV)
    have hE : chestR S (centers w S (m+1)) m n x i:= ⟨show w0∈band T! (m+1) from hl ▸ locking (R:=R) (hG:=hG) (hp i) _ hV,he.trans (by norm_num [Camp.soft,rim])⟩
    let v0:= wood S (centers w S (m+1)) m n x i; let u:= place T! m n (C.W m) v0; have hJ := S.token i n|>.phase m hV
    have he': J.car m hV z=u:=by apply Eq.trans (hJ.ray v hz.2); let d:= Tour.choiceV R hG CST (C.charts m hV) (C.W (m+1)) (C.shirts m hV); change place T! m n _ (d (x i) (lock R (w i) (m+1) hV))= _; rw [← hl]; apply congr_arg (place T! m n (C.W m)); exact (show v0=_ from dif_pos (c:= m < i) hV).symm
    refine ⟨(show ‖u‖≤ Camp.soft from he' ▸ hJ.bounds.2.1 z hz.2),hE,?_⟩
    have hx: ‖z-p‖= ‖drawerE S i (m+1) n (x i)-drawerE S i (m+1) n (rose S n w (m+1) i)‖:= by rw [show z=_ from hz.1]; change max ‖node i (w i) (m+1) hV-node i (w i) (m+1) hV‖ ‖place T! (m+1) n (C.W (m+1)) (x i)-g (m+1) hV‖= ‖place T! (m+1) n (C.W (m+1)) (x i)- place T! (m+1) n (C.W (m+1)) (rose S n w (m+1) i)‖; rw [ha _ hV,sub_self,norm_zero,max_eq_right (norm_nonneg _)] 
    rw [←hx]; apply Eq.trans_le _ (hJ.bounds.2.2 z hz.2 p (J.seats _ _ _ (hp i) _ hV).2); change ‖u-place T! m n (C.W m) (rose S n w m i)‖= ‖J.car m hV z-J.car m hV p‖; rw [ha _ (Nat.le_of_lt hV), he']; unfold g; rw [edge T! i _ _ (w i) _ hV]

include hw H hC
lemma mist (m k:ℕ)(h:m≤k): Arrives (fun i=> drawerE S i m n (cup S n w m k h i)) ∧ ∀ i:ℕ,k≤ i → ‖drawerE S i m n (cup S n w m k h i)‖≤ Camp.soft ∧‖drawerE S i m n (cup S n w m k h i)-drawerE S i m n (rose S n w m i)‖≤ Camp.soft^(k-m):= by
   induction h using Nat.decreasingInduction with
   | self=>
     have hm: cup S n w k k le_rfl=0:= Nat.decreasingInduction_self ..
     rw [hm]; simp only [drawerE,Pi.zero_apply,map_zero,ZeroMemClass.coe_zero]; constructor; exact Arrives.steady _
     intro i hi; have hh:= gains S n w hp ht k i hi; simp only [zero_sub,norm_neg,norm_zero,Nat.sub_self,pow_zero]; exact ⟨by norm_num [Camp.soft,Oriel.rim], (show ‖place T! k n _ (rose S n w k i)‖≤1 from hh ▸ ((S.cart i n).seats _ _ _ (hp i) k hi|>.1.trans (by norm_num [Camp.soft,Oriel.rim])))⟩
   | of_succ i hi ih=>
     have hx j (h:k≤j):= purchase S n w hp ht i k hi j h (cup S n w (i+1) k hi) (ih.2 _ h |>.1)
     rw [show cup S n w i k (Nat.le_of_lt hi) = wood S (centers w S (i+1)) i n (cup S n w (i+1) k hi) from funext fun j=>chase S n w j _ _ hi]
     constructor; · exact (H.stamps _ _ _ _ ((eventually_ge_atTop k).mono fun j hj=> hx j hj|>.2.1) (ratings S w hw hC _) ih.1).2
     intro j hj; refine ⟨(hx j hj).1,?_⟩; apply (hx j hj).2.2.trans; nth_rw 1 [show k-i=k-(i+1)+1 by omega]; rw [pow_succ']; exact mul_le_mul_of_nonneg_left (ih.2 _ hj|>.2) (by norm_num [Camp.soft,Oriel.rim])
end YM.UVExtension.Camp
