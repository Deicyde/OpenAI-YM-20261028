import YM.FullVolume.Amp.Sieve
import YM.FullVolume.Table.Whiz
/-!
# Articulate certificates for Hymn. Beta-tuned arc. Real coefficient along issued campaigns.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable (g:G.Simple){v q d t t':ℝ}{N n m:ℕ}(H:Chord R N m n t t)(h:Degree R.shape R.scout A.delay)(hq:Savvy R.scout R.target A.delay q v d t)
-- Ap rise and step witnesses
variable {T:Team (stageP A.B.a (m+1) n)} {U:Team (stageP A.B.a m n)}(hp:Passage H (T:=T) (U:=U))
open UniformSpace
-- Wrapped type avoids accidental (non-instance-transparent) inherited seminorms in algebra API.
def World {c:Side}{X: Price G c}(U:Team X): Type:= Completion (Home U)
namespace World
variable {c:Side}{B:Price G c}
instance (T:Team B): NormedAddCommGroup (World T):= inferInstanceAs (NormedAddCommGroup (Completion (Home T)))
instance (T:Team B): NormedSpace ℝ (World T):= by
  exact inferInstanceAs (NormedSpace ℝ (Completion (Home T)))
instance (T:Team B): CompleteSpace (World T):= by exact inferInstanceAs (CompleteSpace (Completion (Home T)))
abbrev ready {T:Team B}(x:Completion (Home T)):World T:=x
end World
local notation "β" => A.B.a.clock.hatBeta
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
-- require q ≥...
def choir (q:ℝ):Prop:= 4≤q ∧ FullVolume.Amp.fee (q/4) (1/4) ≤ 1
lemma concert : ∀ᶠ q in atTop, choir q:=by
  filter_upwards [eventually_ge_atTop (4:ℝ),eventually_ge_atTop (32*Real.exp 1)] with x hx he; refine ⟨hx,(div_le_one ?_).mpr ?_⟩ <;> linarith
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable (ht:Climate (A.B.a.clock.hatBeta (m+1)))
-- bring bundle for call φ normalized. identify over affine local coupon.
section gram
variable {X Y Z:Type}[SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z][CompleteSpace Z]
variable {f:X→Y} (e:X→L[ℝ] Z) {k c:ℝ} (x:X)
structure Hits (Q: FullVolume.Amp.Pulse Z Y k) :Prop where
   correct:∀ y:X,‖y‖≤1/4→ HasSum (fun n=>Q.poem n (fun _=> e y)) (f (x+y))
namespace Hits
variable {e x}
lemma jingle {P:FullVolume.Amp.Pulse Z Y k}(h: Hits (f:=f) e x P){y:X}(hv:‖y-x‖≤1/4): FullVolume.Amp.sees P (e y-e x)= f y-f x:=by
  rw [← map_sub]; have hp:=h.correct 0 (by norm_num)
  simp only [add_zero,map_zero] at hp; apply P.earned
  · simpa using h.correct (y-x) hv
  rw [← hp.tsum_eq,tsum_eq_single 0]
  intro i hi
  exact (P.poem i).map_coord_zero ⟨0,by omega⟩ rfl
lemma wave {P:FullVolume.Amp.Pulse Z Y k}(h: Hits (f:=f) e x P){y:X}(hv:‖y-x‖≤1/4)(he:Isometry e): ‖f y-f x‖ ≤ 2*k*‖y-x‖:= by
   have hz : ‖e y-e x‖= ‖y-x‖:=by simpa only [dist_eq_norm] using he.dist_eq y x
   rw [← h.jingle hv]; have hp:= h.jingle (y:=x) (by simp); simp only [sub_self] at hp; simpa only [hp,sub_zero,hz] using P.seesD (hz.trans_le hv) (show ‖(0:Z)‖≤ (1/4:ℝ) by norm_num)
end Hits
lemma roundTrip (f:ℝ→Y)(hp:Rebar (q/2) (phraseS (fun i:sun=> f i)) c)(hv:4≤q): Scout (q/4) f (2*c):=by
   have h:= hp.recovery (show 1≤q/4 from (by linarith)) (show q/4<q/2 from (by linarith))
   apply (h.enlarged (le_of_eq (by rw [show q/4/(q/2)=(1/2:ℝ) from (by have hh:q≠0:=(by linarith); field_simp <;> ring)]; ring))).replace
   exact fun t ht=> by unfold phraseS pinch; rw [dif_pos ht]
lemma exitP (q' : choir q)(he:Isometry e)(hv:DenseRange e)(hb:c≤k)
   (hV:Often (q/4) f x (1/4) c):∃ Q:FullVolume.Amp.Pulse Z Y k,Hits (f:=f) e x Q:=by
   obtain ⟨P,h,hP⟩:= FullVolume.Amp.stage e he hv hV; exact ⟨⟨P,fun n=>(h n).trans (mul_le_mul (pow_le_pow_left₀ (by unfold FullVolume.Amp.fee; have hx:=q'.1; positivity) q'.2 _) hb (hV.pays.2) (by positivity))⟩,⟨hP⟩⟩
end gram
section step
variable {x: ℝ × (Home T)}
def zipB {s:Side}{B:Price G s} (T:Team B): (ℝ × Home T)→L[ℝ](ℝ × World T):=by
    exact ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) (Completion.toComplL (𝕜:=ℝ) (E:=Home T))
lemma zipped (T:Team (stageP A.B.a m n)): Isometry (zipB T)∧ DenseRange (zipB T):= by
  constructor
  · exact Isometry.prodMap (show Isometry (@id ℝ) from isometry_id) (Completion.coe_isometry (α:= Home T))
  exact DenseRange.prodMap denseRange_id (show DenseRange ((↑): Home T → Completion (Home T)) from Completion.denseRange_coe)
include g H h hq hp ht
lemma termsN (hC:choir q)(h':mild Ω x.1) (hv:‖x.2‖≤1): ‖reading H hp x‖ ≤d ∧ ‖drum H x‖ ≤ fn A.B.a m v:=by
    have hb:= Pass.samples ht h' (show |x.1-x.1|≤2 by simp); obtain ⟨hP,hF⟩:= Pass.income g H h hq hp ht x 0 hb (by norm_num) (fun i=>by simpa using hv)
    exact ⟨by simpa using solo hP Jams.tip,by simpa using solo hF Jams.tip⟩
-- at radius any x cert with norm≤1/8. `fee p r ≤1`.
lemma incomeP (hC: choir q)(hd:2*d≤ FullVolume.Amp.glint)(h':mild Ω x.1)(hv:‖x.2‖≤ 1/8): (∃ P:FullVolume.Amp.Pulse (ℝ × World T) (World U) FullVolume.Amp.glint,Hits (f:=fun y=>World.ready (reading H hp y)) (zipB T) x P)∧ ∃ P:FullVolume.Amp.Pulse (ℝ × World T) ℝ (2*fn A.B.a m v),Hits (f:=drum H) (zipB T) x P:=by
   have ht':∀ᶠ y in 𝓝 x,∀ z:ℝ × (Home T), ‖z‖≤1/4 → Scout (q/4) (fun t:ℝ=>World.ready (reading H hp (y+t • z))) (2*d) ∧ Scout (q/4) (fun t:ℝ=>drum H (y+t • z)) (2*fn A.B.a m v):=by
     filter_upwards [Metric.closedBall_mem_nhds x (by norm_num: (0:ℝ)<1/8)] with y hy; intro z hz; rw [Metric.mem_closedBall,dist_eq_norm] at hy
     have hβ:=Pass.samples ht h' (show |y.1-x.1| ≤2 from ((norm_fst_le (y-x)).trans hy).trans (by norm_num)); have hV:‖y.2‖ ≤1/4:= by
       have h:= norm_snd_le (y-x)|>.trans hy; change ‖y.2-x.2‖≤ _ at h; linarith [norm_sub_norm_le y.2 x.2]
     have hW(i:sun) : ‖(y+i.val • z).2‖≤1:=by
        change ‖y.2+i.val • z.2‖ ≤ _; apply (norm_add_le ..).trans; rw [norm_smul]; exact (add_le_add hV ( (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr i.2)).trans ((norm_snd_le z).trans hz))).trans (by norm_num)
     obtain ⟨hu,ha⟩:= income g H h hq hp ht y z hβ (((norm_fst_le z).trans hz).trans (by norm_num)) hW
     have hq:= hC.1; exact ⟨roundTrip _ hu hC.1,roundTrip _ ⟨by linarith, ha.nonneg,fun w i hz=>ha.beam _ _ (stripe_down hz (by linarith: (0:ℝ)<q/2) (by linarith))⟩ hC.1⟩
   have hz:= zipped T
   exact ⟨exitP (zipB T) x hC hz.1 hz.2 hd ⟨by norm_num,ht'.mono fun y hh z h=> (hh z h).1⟩,exitP (zipB T) x hC hz.1 hz.2 le_rfl ⟨by norm_num,ht'.mono fun y hh z h=>(hh z h).2⟩⟩
-- whole-band. d ≤glint/2; both A norm ≤1/8. lips real all!
lemma ticket (hC: choir q)(hd:2*d≤ FullVolume.Amp.glint) (h':mild Ω x.1)(hv:‖x.2‖≤ 1/8)(y:ℝ×Home T)(hs:mild Ω y.1)(hu:‖y.2‖≤1/8) : ‖reading H hp y-reading H hp x‖ ≤ 8*FullVolume.Amp.glint*‖y-x‖ ∧ ‖drum H y-drum H x‖≤8*fn A.B.a m v*‖y-x‖:=by
   have hx := termsN g H h hq hp ht hC h' (show ‖x.2‖≤1 by linarith); have hy:= termsN g H h hq hp ht hC hs (show ‖y.2‖≤1 by linarith); have hx':0≤ fn A.B.a m v:=(norm_nonneg _).trans hx.2
   by_cases hb:‖y-x‖≤1/4
   · obtain ⟨⟨P,hP⟩,⟨Q,hQ⟩⟩:= incomeP g H h hq hp ht hC hd h' hv
     refine ⟨?_, (hQ.wave hb (zipped T).1).trans (mul_le_mul_of_nonneg_right (by linarith [hx']) (norm_nonneg _))⟩
     change ‖World.ready (Pass.reading H hp y)-World.ready (Pass.reading H hp x)‖≤ _
     exact (hP.wave hb (zipped T).1).trans (mul_le_mul_of_nonneg_right (by norm_num [FullVolume.Amp.glint]) (norm_nonneg _))
   push Not at hb; constructor
   · apply (norm_sub_le (Pass.reading H hp y) _).trans; nlinarith [FullVolume.Amp.tintP.1,hx.1,hy.1]
   apply (norm_sub_le (drum H y) _).trans; nlinarith [hx.2,hy.2]
end step
end YM.PhysicalNext.Repeat.Muse
