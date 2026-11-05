import YM.UVExtension.Camp.Plum
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
include hp ht
lemma cap (m:ℕ): ∀ᶠ i in atTop,chestR S (centers w S (m+1)) m n (rose S n w (m+1)) i:=by
    filter_upwards [eventually_ge_atTop (m+1)] with i hi; unfold chestR centers Fitted.faceV rose Fitted.graceT; rw [dif_pos hi,dif_pos hi]; exact ((S.fits i n).officious (S.cart i n) (S.token ..) (hp i) (ht i) (m+1) hi).1
lemma tells (m:ℕ): ∀ᶠ i in atTop,(S.cart i n).tally T! i _ (w i) m=Complex.ofReal (compass S (centers w S (m+1)) m n (rose S n w (m+1)) i):=by
    filter_upwards [eventually_gt_atTop m] with i hi; rw [(S.fits i n).bonusR (S.cart i n) (S.token ..) (hp i) (ht i) m hi]; unfold Camp.compass centers Fitted.faceV rose Fitted.graceT; rw [dif_pos hi,dif_pos (show m+1≤ i from hi),dif_pos (show m+1 ≤ i from hi)]; exact congr_arg Complex.ofReal (show Tour.bonus _ _ _ _= _ from Eq.symm (show Tour.claim _ _ _ _ _=_ from dif_pos ((S.fits i n).officious (S.cart i n) (S.token ..) (hp i) (ht i) (m+1) hi).1))
include hw hC H

lemma income (m:ℕ): Arrives (fun i=> drawerE S i m n (rose S n w m i)) := by
    refine Camp.trim ?_; intro ε h
    have he (v:ℕ):= mist S n H w hp ht hw hC m (m+v) (Nat.le_add_right ..)
    obtain ⟨k,hk⟩:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [Camp.soft,Oriel.rim]:0≤ Camp.soft) (by norm_num [Camp.soft,Oriel.rim])).eventually_le_const h).exists
    exact ⟨_, (he k).1,(eventually_ge_atTop (m+k)).mono fun i hi=> by rw [dist_comm,dist_eq_norm]; exact ((he k).2 _ hi|>.2.trans (by simpa only [Nat.add_sub_cancel_left] using hk))⟩
lemma frameP (m:ℕ): Arrives (fun i=>(S.cart i n).tally T! i _ (w i) m):=by
    have he: Arrives (compass S (centers w S (m+1)) m n (rose S n w (m+1))):= H.stamps m n _ _ (cap S n w hp ht m) (ratings S w hw hC _) (income S n H w hp ht hw hC (m+1))|>.1
    exact (he.post Complex.continuous_ofReal).copy ((tells S n w hp ht m).mono (fun _ h=> h.symm))
lemma operable (b:ℝ): Charting (fun i=> (S.cart i n).veil T! i _ b (w i)) := by
   intro m; let f i:= ∑ j∈ Finset.range m,(S.cart i n).tally T! i _ (w i) j
   refine Arrives.copy ((show Arrives f from Arrives.sum _ (fun i _=> frameP S n H w hp ht hw hC i)).post (T:=fun x:ℂ=> (Camp.pulse T! m:ℂ)⁻¹*((b:ℂ)-x)) (by fun_prop)) ?_; filter_upwards [eventually_ge_atTop m] with i hi; rw [emit,dif_pos hi]; rfl

omit hw hC H
lemma white (b:ℝ)(k:ℕ): Light k ((S.cart k n).veil T! k _ b (w k)):=by
   have he i: ((S.cart k n).tally T! k _ (w k) i).im=0:=by
      by_cases hi:i < k
      · rw [(S.fits k n).bonusR (S.cart k n) (S.token ..) (hp k) (ht k) i hi]; rfl
      rw [Cart.tally,dif_neg hi]; rfl
   intro i; unfold Cart.veil; simp [← Complex.ofReal_inv, he]
omit hp ht
variable (b:ℝ)(hh:(b:ℂ) ∈ Camp.Broad A.B.a)
def perform (k:ℕ)(i:ℕ): PlotN i:=((S.cart i n).veil T! i _ b)^[k] 0
include hh H hC
lemma stair (k:ℕ): (∀ i:ℕ, perform S n b k i∈ Harbor i ∧ Light i (perform S n b k i)) ∧ Charting (perform S n b k):= by
  induction k with
  | zero=> refine ⟨fun i=> ⟨Cart.harbor i,fun _=>rfl⟩,fun j=>?_⟩; apply (Arrives.steady (0:ℂ)).copy; filter_upwards with i; unfold emit; split <;> exact rfl
  | succ k ih=>
    rw [show perform S n b (k+1)=(fun i=> (S.cart i n).veil T! i _ b (perform S n b k i)) from funext fun i=> Function.iterate_succ_apply' ..]; let f:=perform S n b k
    exact ⟨fun i=> ⟨(S.cart i n).access hG T! i _ S.grove.coins hh (ih.1 i|>.1), white S n f (fun i=> (ih.1 i).1) (fun i=> (ih.1 i).2) b i⟩, operable S n H f (fun i=> (ih.1 i).1) (fun i=> (ih.1 i).2) ih.2 hC b⟩

def beaux (b:ℂ)(i:ℕ): PlotN i:= (S.fits i n).sonnet (S.cart i n) S.grove.coins b
lemma climb : Charting (beaux S n (b:ℂ)):=by
    intro j; refine Camp.trim ?_; intro ε hε
    have ht:Tendsto (fun k:ℕ=> rad*(1/2)^k/(1-1/2)) atTop (𝓝 0):= by simpa only [mul_zero,zero_div] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num)).const_mul rad).div_const ((1:ℝ)-1/2))
    obtain ⟨k,hk⟩:= (ht.eventually_le_const hε).exists
    refine ⟨_,(stair S n H hC b hh k).2 j,?_⟩; filter_upwards [eventually_ge_atTop j] with i hi; unfold emit; rw [dif_pos hi,dif_pos hi,dist_comm]
    let V:=perform S n b k i; let z:=beaux S n b i; have hT: ‖V-z‖≤ ε:=(dist_eq_norm V z) ▸ ((S.cart i n).speed hG T! i _ S.grove.coins hh k|>.trans hk)
    rw [dist_eq_norm]; exact (norm_le_pi_norm (V-z) _).trans hT

lemma artistry (m:ℕ): Arrives (fun i=> drawerE S i m n ((S.fits i n).Rest (S.cart i n) S.grove.coins b m)) ∧ Arrives (fun i=> (S.fits i n).Third (S.cart i n) S.grove.coins b m):= by
    have ht:= climb S n H hC b hh; let f i := beaux S n (b:ℂ) i; exact ⟨income S n H f (fun i=>(S.fits i n).glint _ S.grove.coins _ hh) (fun i=>(S.fits i n).blessed _ (S.token i n) S.grove.coins hh) ht hC m, ratings S f ht hC m⟩
end YM.UVExtension.Camp
#print axioms YM.UVExtension.Camp.artistry
