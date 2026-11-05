import YM.Next.RANK.Radian.Incipient
import YM.Next.RANK.Radian.Reliquary

/-!
# Applying multiplier estimates after all step weights

Costs below C kernel derivative estimates (symbol at a pair of coordinates!
NOT on any continuation already applied to Xi). Still require Patrė's Fourier
estimates on this metric. No coherence assertions about multiplier value extension
at the window not on grid. Unit-at-origin Δ^i is literal; its integral never gets
reinterpreted as derivative in a canonical connection-coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer Finset
open Atlas Normal Perch Wall CellsInt Function RG
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
variable {E : Type*} {P : Schedule} {n j d k R : ℕ} {f g h q : E4→ℂ} {b A : ℝ} {H : Gauge}
local notation "ℑ" => Complex.I

lemma Cast.weaker (h : Cast f n d A b) (hp : k≤n) : Cast f k d A b:= ⟨h.positive,h.hills.of_le (by exact_mod_cast hp),fun i hi=> h.altar i (hi.trans hp)⟩

lemma Cast.cutZero (h : eventP R f) (x : E4) (hx : (R:ℝ)<‖x‖) : f=ᶠ[𝓝 x]0:= continuous_norm.continuousAt.eventually (lt_mem_nhds hx)|>.mono fun i hi=> h i hi
lemma Cast.lips (h : Cast f n 0 R b) (he : eventP R f) (ht : 1≤n) (hv : ‖f 0‖≤b) : Lip f R b:= by
  have hp x (hx:x∈away):ContDiffAt ℝ 1 f x:= (h.hills.of_le (by exact_mod_cast ht : ↑(1:ℕ) ≤ (↑n:WithTop ℕ∞)) x hx).contDiffAt (open_away.mem_nhds hx)
  refine ⟨he,fun i=> ?_,fun i hx=> (hp _ hx).differentiableAt (by simp),fun i hi=> ?_⟩
  · rcases eq_or_ne i 0 with g|g; exact g.symm ▸ hv
    by_cases ht : R < ‖i‖; rw [he i ht,norm_zero]; exact h.positive
    simpa only [norm_iteratedFDeriv_zero, pow_zero,mul_one] using h.altar 0 (Nat.zero_le _) i g (le_of_not_gt ht)
  by_cases hz : ‖i‖ ≤R
  · simpa only [pow_one,norm_iteratedFDeriv_one,pow_zero,mul_one] using! h.altar 1 ht i hi hz
  have hvf:fderiv ℝ f i=fderiv ℝ (0:E4→ℂ) i:= ((Cast.cutZero he i (lt_of_not_ge hz)).fderiv).eq_of_nhds
  rw [hvf]; simp;exact h.positive
lemma Lip.int (p : Measurable f) (h : Lip f R b) : Integrable f:= by
  let t:=Metric.closedBall (0:E4) (R:ℝ)
  let A:= t.indicator (fun _=>b)
  refine (show Integrable A from (integrable_indicator_iff isClosed_closedBall.measurableSet).2 (integrableOn_const (hs:=(isCompact_closedBall _ _).measure_lt_top.ne))).mono' p.aestronglyMeasurable (Eventually.of_forall fun x=>?_)
  by_cases he:x∈t; rw [show A x=b from indicator_of_mem he _]; exact h.norm x
  rw [show A x=0 from indicator_of_notMem he _,h.event _ (by simpa only [t,mem_closedBall,dist_zero_right,not_le] using he),norm_zero]

private theorem clear (T :ℕ) (L B : Degree H) {t : ℝ} (h : 0<t): ∃ C : ℝ,1≤C∧∀ i≤T,∀x:E4,1 ≤ ‖x‖→ ‖iteratedFDeriv ℝ i (HeatP t L B) x‖ ≤ C/‖x‖^5:= by
  choose c hc hp using fun i : Fin (T+1)=> (looks h L B|>.2 i.val 5)
  let C:= ∑ i,c i
  refine ⟨1+C,le_add_of_nonneg_right (sum_nonneg fun i _=>hc i),fun i hi x hx=>?_⟩;apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hx) _)).2; rw [mul_comm]; let l :Fin (T+1):=⟨i,by omega⟩; exact (hp l x hx).trans ((single_le_sum (f:=c) (fun i _=>hc i) (mem_univ l)).trans (le_add_of_nonneg_left zero_le_one))

-- conventional symbol root test at unspecialized degree-zero pole. n may depend station, producer calls. `C` pre.
structure Window (F : E4→ℂ) (R : ℕ) (C : ℝ) (n : ℕ) (b : ℝ) (D L : Degree H) : Prop where
  nonneg : 0 ≤ C
  event : eventP R F
  coast : ‖F 0‖ ≤ C
  meas : Measurable F
  cast : Cast F n 0 R C
  crest : Cast (F-HeatP b (origin D) (origin L)) n 1 1 C


theorem intended (R : ℕ) (h : 1≤R) (D L : Degree H) {t : ℝ} (ht : 0<t) (n : ℕ) (hn : D.degree+L.degree+6 ≤ n) : ∃ c : ℝ,0≤ c ∧ ∀ F B C,
    1≤B→Window F R B n t D L → B*c≤C → Integrable (parade D L F) ∧
      Mist (parade D L F-HeatP t D L) (D.degree+L.degree) C ∧ Lip (parade D L F) R C:= by
  let K:=reel D L;let v:=D.degree+L.degree; let p:=staccato K; let q:=peck K; let l:=HeatP t (origin D) (origin L)
  obtain ⟨⟨a,ha⟩,⟨hH,hS⟩,u,hu⟩:=messages K n; have hw:K.length=v:= by simp [K,v,reel]
  rw [hw] at ha hS hu
  obtain ⟨z,hZ⟩:=epithet p (starlight _) R n; obtain ⟨r,hr,hL⟩:=clear n D L ht; let T:=2^n*z+‖p 0‖
  let F':=2^n*(u+hH);let c:=T+(R:ℝ)^5*T + F' +r
  have hp:= hu.positive;have hx:=hS.positive; have he:=hZ.positive; have hT:0≤T:=by unfold T; positivity
  have hP:0 ≤ F':= by unfold F'; positivity
  refine ⟨c,by dsimp only [c]; positivity,?_⟩; intro F B C hB hv hC
  have hy:= zero_le_one.trans hB; let g:=parade D L F
  have hs:g=p*F:=dizzy D L F
  have hy' : g-HeatP t D L= (p-q)*F+q*(F-l):= by rw [hs,augments];unfold p q K l;ring
  have hh : Cast g n 0 R (B*T):= by rw [hs]; apply Cast.coin (hZ.multiply hv.cast);unfold T;nlinarith only [mul_nonneg hy (norm_nonneg (p 0))]
  have hJ : eventP R g:= by intro x h; rw [hs,Pi.mul_apply,hv.event x h,mul_zero]
  have hvX : ‖g 0‖ ≤ B*T:= by rw [hs,Pi.mul_apply,norm_mul,mul_comm]; apply (mul_le_mul_of_nonneg_right hv.coast (norm_nonneg _)).trans; apply mul_le_mul_of_nonneg_left _ hy; exact le_add_of_nonneg_left (by positivity)
  have hC₁:B*T≤ C:= by unfold c at hC; nlinarith only [hC,mul_nonneg hy hP,mul_nonneg hy (zero_le_one.trans hr),mul_nonneg hy (show 0≤ (R:ℝ)^5*T by positivity)]
  let Y:=(hh.coin hC₁).lips hJ (show 1 ≤ n by omega) (hvX.trans hC₁)
  refine ⟨Y.int (show Measurable g by rw [hs]; exact (starlight _).continuous.measurable.mul hv.meas),?_,Y⟩
  have ht' : Cast (g-HeatP t D L) (v+6) (v+1) 1 C:= by
    have hX:= hu.multiply (hv.cast.range (show (1:ℝ) ≤ R by exact_mod_cast h)); rw [Nat.add_zero] at hX; rw [hy']
    apply ((hX.join (hS.multiply hv.crest)).weaker (by omega : v+6≤n)).coin
    apply le_trans (b:= F'*B) (le_of_eq (by unfold F';ring)); unfold c at hC; have he':0≤B*r:= mul_nonneg hy (zero_le_one.trans hr); linarith only [hC,he',mul_nonneg hy hT,mul_nonneg (show 0≤(R:ℝ)^5*T from by positivity) hy]
  refine ⟨ht'.hills,ht'.altar,fun i hi x hx'=> ?_⟩; have h:n≤n:=le_rfl
  have hw:0<‖x‖:=zero_lt_one.trans_le hx';have hp:x∈away:=norm_pos_iff.mp hw; have heU: i ≤n:=by omega
  have h₀: ‖iteratedFDeriv ℝ i g x‖ ≤ ((R:ℝ)^5*(B*T))/‖x‖^5:= by
    by_cases h:‖x‖ ≤ R
    · have hk:= hh.altar i heU x hp h; rw [pow_zero,mul_one] at hk
      rw [le_div_iff₀ (by positivity)]
      have hx : ‖iteratedFDeriv ℝ i g x‖ ≤ B*T:= le_trans (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hx')) hk
      exact (mul_le_mul hx (pow_le_pow_left₀ hw.le h 5) (pow_nonneg hw.le 5) (mul_nonneg hy hT)).trans_eq (mul_comm ..)
    rw [((Cast.cutZero hJ x (lt_of_not_ge h)).iteratedFDeriv ℝ i).eq_of_nhds]; simp; positivity
  change ‖iteratedFDeriv ℝ i (g-_) x‖≤_
  rw [iteratedFDeriv_sub_apply ((hh.hills.of_le (by exact_mod_cast heU : (↑i:WithTop ℕ∞) ≤ ↑n) x hp).contDiffAt (open_away.mem_nhds hp)) (((looks ht D L).1 _ hp).of_le (WithTop.coe_le_coe.mpr le_top))]
  apply (norm_sub_le ..).trans; apply (add_le_add h₀ (hL i heU _ hx')).trans
  rw [← add_div]; refine div_le_div_of_nonneg_right ?_ (by positivity); unfold c at hC; linarith only [hC,(le_mul_of_one_le_left (zero_le_one.trans hr) hB),mul_nonneg hy hT,mul_nonneg hy hP]
end YM.Next.Rank.Radian
