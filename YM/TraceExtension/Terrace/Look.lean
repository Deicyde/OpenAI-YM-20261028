import YM.TraceExtension.Terrace.Knob
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
section scale
open PhysicalNext.Repeat.Quince
def AgeK (A:Levels G)(a:ℝ)(i:ℕ):= Wave a (A.clock.hatBeta i)
def part (A:Levels G)(i:ℕ):= AgeK A (-(2/5:ℝ)) i
variable (A:Levels G)
lemma mono_age (i:ℕ)(h:1 ≤ Lyra A i) {j:ℕ} (hi : i≤j)(hG:G.Simple)(a:ℝ)(hp: 0 ≤ a): AgeK A a i ≤ AgeK A a j:=by
    unfold AgeK Wave; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ hp
    unfold RLog; exact pow_le_pow_left₀ (Real.log_nonneg h) (Real.log_le_log (lira A i) (lypos A hG hi)) _
lemma cameo_age (i:ℕ): cameo A i=AgeK A (1/2:ℝ) i:=by rw [cameo,Real.sqrt_eq_rpow]; set x:= A.clock.hatBeta i; rw [show A.clock.monitor i=Wave 1 x from by simp only [Wave, one_mul, RLog, Calendar.monitor];rfl,wring,one_mul];rfl
lemma part_pos(k:ℕ) :0 < part A k:=wake ..
lemma downWave (a:ℝ)(h:a<0) : Tendsto (Wave a) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (Zn.arc.const_mul_atTop_of_neg h)
lemma parts_rate (h:G.Simple): Tendsto (part A) atTop (𝓝 0):=(downWave _ (by norm_num)).comp (hrate A h)
lemma Age_rate {a:ℝ}(ha:a<0)(h:G.Simple): Tendsto (AgeK A a) atTop (𝓝 0):= (downWave _ ha).comp (hrate A h)
lemma AgeK_mul(a b:ℝ)(j:ℕ): AgeK A a j * AgeK A b j=AgeK A (a+b) j:=walt ..
lemma rounder (h:G.Simple)(θ:PostT A): ∀ᶠ i:ℕ in atTop,(part A i ≤ 1 ∧ ∀ j:ℕ,i ≤ j→ j < summit A i→
      gearK A j ≤ part A i/(2*(summit A i-i:ℕ))) :=by
   have hh : ∀ᶠ x:ℝ in atTop,(8*(1+2*Real.log x))*(4*Gate x)≤ Wave ((1:ℝ)/10) x:=
       ((((mass zero_le_one).gather (logC.times 2 (by norm_num))).times 8 (by positivity)).cop ((logC.crop 48).times 4 (by positivity)) _ (by norm_num)|>.mono fun x h=> h.2)
   filter_upwards [back_gate A h θ,bond A h θ,(hrate A h).eventually hh,(parts_rate A h).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),(lrate A h).eventually_ge_atTop 1] with i hQ hZ hx hp hi
   let t:= summit A i; let L:= (t-i:ℕ); have hL:0<L:=Nat.sub_pos_of_lt (stellar ..)
   let x:=A.clock.hatBeta i; let y:= Lyra A i; have hz:0<y:=lira A i; let V:= part A i; refine ⟨hp,fun j hj ht=>?_⟩
   let p:=(A.params (j+1)).columns
   have hP:p ≤ 2*y:= (θ.share _).trans ((lypos A h ht).trans hZ.2.1); have he:1≤p:= (A.params _).columns_ge
   have hY: (L:ℝ) ≤ 2*Gate x:=(bound_gap A (stellar A i|>.le)).trans hQ
   let B:= cameo A (j+1); have hb:0<B:=cameo_pos ..;
   have hw: Wave ((1:ℝ)/10) x ≤ V*B:=by
       rw [show Wave ((1:ℝ)/10) x=part A i*cameo A i by rw[cameo_age]; unfold part; rw [AgeK_mul]; norm_num [AgeK];ring_nf;rfl];
       have hs: cameo A i≤ B:= by unfold B; simp_rw [cameo_age]; exact mono_age A i hi (hj.trans j.le_succ) h _ (by norm_num)
       exact mul_le_mul_of_nonneg_left hs (part_pos ..|>.le)
   change 4*(2*(1+p)/B) ≤ V/(2* (L:ℝ))
   rw[←mul_div_assoc]; apply (div_le_div_iff₀ (b:=B) (d:=2*(L:ℝ)) hb (by positivity)).mpr
   exact (mul_le_mul (b:=8*(1+2*y)) (by linarith only [hP]) (d:=4*Gate x) (by linarith only[hY]) (by positivity) (by positivity)).trans (hx.trans hw)
end scale

private lemma casc {d:ℕ} (F:Frame G d)(v:ℕ→F.Coeff) {i k:ℕ} (h:i<k) (x:ℝ)(hp:0 <x)(hx:x≤1)
    (H: ∀ j:ℕ,i≤j→ j<k→ F.coeffSize (v j-v (j+1)) ≤ x/(2*(k-i:ℕ))* F.coeffSize (v (j+1))): ∀ j:ℕ,i≤j → j ≤ k→ F.coeffSize (v j-v k) ≤ x* F.coeffSize (v k):=by
    intro j hj he; let K:= F.coeffSize (v k); have hK:0≤K:=Work.G08.size_nonneg ..; let P:=k-i; have hP:0<(P:ℝ):=Nat.cast_pos.mpr (Nat.sub_pos_of_lt h);
    let a:= x/(P:ℝ); have ha:0 ≤a:= div_nonneg hp.le hP.le;have heq: a/2=x/(2*(P:ℝ)):=by unfold a;ring
    have hp' (j:ℕ)(hh:i≤j)(he:j ≤ k): a * (↑(k-j):ℝ) ≤ x:=by
        rw [← show a*(↑P:ℝ)=x from div_mul_cancel₀ _ hP.ne']; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by unfold P;omega)) ha
    have he' : F.coeffSize (v j-v k) ≤ a* (↑(k-j):ℝ)*K:=by
        induction he using Nat.decreasingInduction with
        | self=> simp[Frame.coeffSize]
        | of_succ j hh IH=>
           have hp := hp' (j+1) (hj.trans j.le_succ) hh; have ht := IH (hj.trans j.le_succ)
           have hu : F.coeffSize (v (j+1)) ≤ 2*K:= by
               linarith only [Work.G08.size_triangle F (v (j+1)) (v k),ht,mul_le_mul_of_nonneg_right (hp.trans hx) hK]
           have hv:= H j hj hh; change _ ≤ x/(2*(P:ℝ))*_ at hv; rw [← heq] at hv
           rw [show v j-v k=(v j-v (j+1))+(v (j+1)-v k) by abel]; apply (Size.add ..).trans
           rw [show k-j=k-(j+1)+1 by omega]; push_cast; linarith only [ht,hv,mul_le_mul_of_nonneg_left hu (show 0 ≤ a/2 by linarith)]
    exact he'.trans (mul_le_mul_of_nonneg_right (hp' j hj he) hK)
variable (C:Family G) (K:Bid.Worth)(hG:G.Simple)(θ:PostT C.path.levels)
set_option quotPrecheck false
local notation "A"=> C.path.levels
include hG θ
lemma spine_pitch (D:Sceptre C K)(d:ℕ)(hd:d≤5):∀ᶠ i:ℕ in atTop,let F:=C.labels.level d; let k:= summit C.path.levels i
    ∀ᶠ p:ℕ in atTop,∀ N:ℕ,k ≤ N→∀ v:C.label d,(∀ j:ℕ,i≤j→j ≤ k→ Cgrade F (Cturn C d j N p v))→∀ j:ℕ,i≤j → j ≤ k→ F.coeffSize (spine C d j N p v-spine C d k N p v) ≤ part A i* F.coeffSize (spine C d k N p v):=by
   filter_upwards [rounder _ hG θ,eventually_ge_atTop (C.ref d)] with i hi ht; intro F k
   filter_upwards [(Finset.Ico i k).eventually_all.mpr (fun j h=>readStep _ D (ht.trans (Finset.mem_Ico.mp h).1) hG hd)] with p hp N hn v hv
   refine casc F (fun j=> spine C d j N p v) (stellar ..) _ (part_pos ..) hi.1 ?_
   intro j hj hK; apply (hp _ (Finset.mem_Ico.mpr ⟨hj,hK⟩) _ (hK.trans_le hn) v (hv _ (hj.trans j.le_succ) hK)).trans; exact mul_le_mul_of_nonneg_right (hi.2 _ hj hK) (Work.G08.size_nonneg ..)
end YM.Trace.Terrace
