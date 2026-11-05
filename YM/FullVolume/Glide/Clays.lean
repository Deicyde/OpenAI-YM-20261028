import YM.FullVolume.Glide.Wings
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
lemma alongS {E:Type}[TopologicalSpace E]{s t:ℕ→E}(n:ℕ)(h:Glints atTop (fun i=> s (i+n)) (fun i=>t (i+n))): Glints atTop s t:=by obtain ⟨x,h,H⟩:=h; exact ⟨_,Pith.high n h,Pith.high n H⟩
variable (h:Stationary.Artes.Cadre A.post A.B.kin)(he: Next.Free.Amplify A.B.M)(hp:Jams.Wild R.shape A.delay) {u v:ℕ→ℕ}{Q:∀ i, Ops L (u i) p}{Q':∀ i,Ops L (v i) p} {U V:ℕ→ℕ→ℝ}{T:∀ i,Runup (Q i) (U i)}{B':∀ i,Runup (Q' i) (V i)} {r s':ℕ→ℕ}
variable (hx:∀ i,Cage (Q i) (U i) (r i) (T i))(hg:∀ i, Cage (Q' i) (V i) (s' i) (B' i))(hu:Tendsto u atTop atTop)(hv:Tendsto v atTop atTop)(hw: ∀ j:ℕ, Glints atTop (fun i=> U i j) (fun i=> V i j))
include h he hp hx hg hu hv hw Y
lemma marchA (m:ℕ)(hk:∀ᶠ i in atTop,m<r i∧m<s' i)(hf:Glints atTop (fun n=>gifts (T n) (m+1)) (fun n=> gifts (B' n) (m+1))): Glints atTop (fun n=> gifts (T n) m) (fun n=>gifts (B' n) m) ∧ Glints atTop (fun n=>price (T n) m) (fun n=>price (B' n) m):=by
    obtain ⟨a,ha⟩:= eventually_atTop.mp (((hu.eventually_gt_atTop m).and (hv.eventually_gt_atTop m)).and hk); let f(n:ℕ):= n+a; have hH i :a≤f i:=Nat.le_add_left .. ; have hP:=fun i=>ha _ (hH i); let P i:=hP i|>.1.1; let S i:=hP i|>.1.2; have hz:Tendsto f atTop atTop:=tendsto_atTop_mono (f:=id) (fun i=>Nat.le_add_right ..) tendsto_id
    let g(i):=T (f i)|>.liftP (m+1) (P i); let g' i:= B' (f i)|>.liftP (m+1) (S i)
    let x i:wish (Q (f i)) m (P i):=(U (f i) (m+1),g i); let y(i):wish (Q' (f i)) m (S i):= (V (f i) (m+1),g' i)
    have hr: Glints atTop (fun i=> room (Q (f i)) (x i).2) (fun i=>room (Q' (f i)) (y i).2) := (glitters hf hz hz).carve (Eventually.of_forall fun i=>lifts (m+1) (P i)) (Eventually.of_forall fun i=>lifts (m+1) (S i))
    obtain ⟨hA,hT⟩:= eternity Y h he hp (u:=u∘f) («P»:=x) (T:=y) (fun n=> ⟨hx _|>.moods _ (P n),(T _|>.valid _ (P n))⟩) (fun n=>⟨hg _|>.moods _ (S n), B' _|>.valid _ (S n)⟩) (hu.comp hz) (hv.comp hz) (glitters (hw _) hz hz) hr
    refine ⟨alongS a (hA.carve ?_ ?_), alongS a (hT.carve (Eventually.of_forall fun i=> (prime (T:=T (f i)) m (P i)).symm) (Eventually.of_forall fun i=> (prime (T:=B' (f i)) m (S i)).symm))⟩
    · exact Eventually.of_forall fun i=> ((lifts (T:=T (f i)) m (P i|>.le)).trans (hx _|>.route m (P i) (hP i|>.2.1))).symm
    exact Eventually.of_forall fun i=> ((lifts (T:=B' (f i)) m (S i|>.le)).trans (hg _|>.route m (S i) (hP i|>.2.2))).symm
omit hx hg
include hx hg -- specialized shadows require omit
omit hx hg
variable (hX:∀ i,Cage (Q i) (U i) (u i) (T i))(hY:∀ i,Cage (Q' i) (V i) (v i) (B' i))
lemma brittle (m:ℕ)(T:∀ i,Runup (Q i) (U i))(K':∀ i,Runup (Q' i) (V i))(hx:∀ i,Cage (Q i) (U i) m (T i))(hg:∀ i,Cage (Q' i) (V i) m (K' i)) : ∀ j:ℕ, j ≤ m →  Glints atTop (fun n=> gifts (T n) j) (fun n=>gifts (K' n) j):=by
    intro j hj; induction hj using Nat.decreasingInduction with
    | self=>
        have ha : Glints atTop (fun _=> (0:cloud B m p)) (fun _=>(0:cloud B m p)):= ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
        refine ha.carve ?_ ?_
        · exact (hu.eventually_gt_atTop m).mono fun n hn=> Eq.symm ((lifts (T:=T n) m hn.le).trans ((hx n|>.seats hn.le).resolve_right (Ne.symm hn.ne)))
        exact (hv.eventually_gt_atTop m).mono fun n hn=> Eq.symm ((lifts (T:=K' n) m hn.le).trans ((hg n|>.seats hn.le).resolve_right (Ne.symm hn.ne)))
    | of_succ i hi ih => exact marchA Y h he hp (r:=fun _=>m) (s':=fun _=>m) hx hg hu hv hw i (Eventually.of_forall fun i=>⟨hi,hi⟩) ih|>.1
include hX hY
lemma breakaway (m:ℕ): Tendsto (fun n=> gifts (T n) m-gifts (B' n) m) atTop (𝓝 0):=by
    refine Metric.tendsto_nhds.mpr fun ε ho=>?_ ; let t:= ε/3; have hs:0<t:= div_pos ho (by norm_num); let C:= 8*glint; obtain ⟨k,hk⟩:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (r:=C) (by norm_num [C,glint]) (by norm_num [C,glint])).eventually (gt_mem_nhds hs)).exists
    let b:= m+k; choose X hx H using fun i=> guild Y (O:=Q i) (hX i|>.moods) b; choose K' hS Ω' using fun i=>guild Y (O:=Q' i) (hY i|>.moods) b
    have ha: m ≤ b:= Nat.le_add_right ..; have hz := (brittle Y h he hp hu hv hw b X K' hx hS m ha).shrank; filter_upwards [(Metric.tendsto_nhds.mp hz t hs),hu.eventually_ge_atTop b,hv.eventually_ge_atTop b] with n hn ht hh; have hg : dist (gifts (X n) m) (gifts (T n) m) < t:=lt_of_le_of_lt (culprit Y (hx n) (hX n) ht m ha) (by rw [Nat.add_sub_cancel_left]; exact hk)
    have hv' : dist (gifts (K' n) m) (gifts (B' n) m)<t :=lt_of_le_of_lt (culprit Y (hS n) (hY n) hh m ha) (by rw [Nat.add_sub_cancel_left]; exact hk)
    rw [dist_zero_right,←dist_eq_norm] at hn ⊢; apply lt_of_le_of_lt (dist_triangle4 _ (gifts (X n) m) (gifts (K' n) m) _); rw [dist_comm] at hg; unfold t at *; linarith
lemma aglow (m:ℕ) : Glints atTop (fun i=> gifts (T i) m) (fun i=>gifts (B' i) m):=by
    refine wait fun f g hf hh=>?_ ; exact breakaway Y h he hp (Q:=fun i=> Q (f i)) (Q':=fun i=> Q' (g i)) (T:=fun i=> T (f i)) (B':=fun i=> B' (g i)) (hu.comp hf) (hv.comp hh) (fun j=>glitters (hw j) hf hh) (fun i=>hX (f i)) (fun i=>hY (g i)) m
lemma scored (m:ℕ): Glints atTop (fun i=>price (T i) m) (fun i=>price (B' i) m):= marchA Y h he hp hX hY hu hv hw m ((hu.eventually_gt_atTop m).and (hv.eventually_gt_atTop m)) (aglow Y h he hp hu hv hw hX hY (m+1))|>.2
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
