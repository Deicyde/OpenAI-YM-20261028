import YM.Next.RANK.Flux.Petitions
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pricetags

/-!
# Cost chimes FOR the marked budget alone, on EACH pre-charged arc

Check payment only after fixed constants (Pre-L vs post-L explicit).
Multiple Mark copies at width from Canvas even for early purchase.
No physical estimate on outputs for these numbers asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open MeasureTheory Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Thirst Filter
open scoped Topology BigOperators Classical

def fuel (S : Era) (g u : ℝ) (z : ℝ) := Line S g z u * salary (load S) * z + (salary (load S)*Perch.bill (-4) u+salary (load S)*Perch.bill (-4) u)
lemma fuel_nn (S : Era) (g u : ℝ) (z : ℝ) (h : 0≤z) : 0≤ fuel S g u z:= by unfold fuel; exact add_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (show 1 ≤ Line .. from le_max_left ..)) (Real.exp_pos _).le) h) (add_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
lemma late_fee (S : Era) (φ : ℝ) (h : 8*salary (load S)≤S.α): ∀ᶠ u in atTop, ∀ z : ℝ, 0≤z → z ≤ Perch.bill (-4) u → fuel S φ u z ≤ firstN u/2 := by
  let Y:= salary (load S); have hY:0≤Y:=(Real.exp_pos _).le
  filter_upwards [Paint.absorb (-4) (-3) (by norm_num) (8*Y)] with u hu z hz he
  let P:= firstN u; let W:= Line S φ z u; let Q:=fareP S φ z u
  have hp : 0<P:= Real.exp_pos _
  have hk : S.α*z < Q:= lt_add_of_pos_right _ (Real.exp_pos _)
  have hh : 0<Q:= lt_of_le_of_lt (mul_nonneg (zero_le_one.trans S.pay) hz) hk
  have hW : 8*(W*Y*z) ≤ P:= by
    rw [show 8*(W*Y*z)= Line S φ z u*(8*Y*z) by ring]; unfold Line
    rcases le_total 1 (P/Q) with h1|h1
    · rw [max_eq_right (show 1 ≤ firstN _/fareP .. from h1)]; change P/Q* _ ≤ _; rw [div_mul_eq_mul_div, div_le_iff₀ hh]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right h hz).trans hk.le) hp.le
    rw [max_eq_left (show firstN _/fareP ..≤1 from h1),one_mul]; exact (mul_le_mul_of_nonneg_left he (by positivity)).trans hu
  change W*Y*z+(Y* _+Y*_)≤ P/2; change 8*Y*_ ≤ P at hu
  linarith only [hW,hu,hp]
lemma noInflate (S : Era) (g x z : ℝ) (h : 0≤z) : Line S g z x ≤ Line S g 0 x:= by
  unfold Line; apply max_le_max le_rfl; apply div_le_div_of_nonneg_left (Real.exp_pos _).le
  exact add_pos_of_nonneg_of_pos (by rw [mul_zero]) (Real.exp_pos _); apply add_le_add _ le_rfl; rw [mul_zero]; exact mul_nonneg (zero_le_one.trans S.pay) h
lemma pass_line (S : Era) (g : ℝ) : ∀ᶠ s : ℝ in atTop,∀ t∈ Set.Icc (s/2) s,
    Line S g 0 s * t^(-(1:ℝ)) ≤ 1:= by
  filter_upwards [long_pay (g-3) 1 zero_lt_one, Perch.half.eventually_ge_atTop 1] with s h hs t ht
  have hx : 1 ≤ t:= hs.trans ht.1
  have he:Line S g 0 s=max 1 (bill (g-3) s) := by unfold Line fareP firstN Perch.bill; rw [mul_zero,zero_add,← Real.exp_sub]; congr 2;ring
  rw [he]
  rcases le_total 1 (bill (g-3) s) with hq|hq
  · rw [max_eq_right hq]; exact (mul_le_mul_of_nonneg_left (h t ht) (show 0 ≤ bill (g-3) s from (Real.exp_pos _).le)).trans (by rw [overlap]; simp [bill])
  rw [max_eq_left hq,one_mul]; exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

-- slight tightening of Orchid cover: no factor 64 needed for these projections.
private lemma veer : ∀ᶠ s in atTop, walls s ≤ 2*walls (s/2):= by
  filter_upwards [(Real.tendsto_log_atTop.comp Perch.half).eventually_ge_atTop (12:ℝ),eventually_gt_atTop (0:ℝ)] with s ht hp
  let t:= Real.log (s/2); let u:=Real.log 2
  have he : Real.log s=t+u:= by rw [show t=Real.log s-Real.log 2 from Real.log_div (by positivity) (by norm_num)]; ring
  have hb : u ≤ 1:= by have hh:= Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ)); linarith
  have hv: 0≤u:=Real.log_nonneg (by norm_num); change 12 ≤ t at ht
  have hc:3*(M s:ℝ)≤4*M (s/2):= by
    have h : (M s:ℝ)< (t+u)^2+1:=Nat.ceil_lt_add_one (show 0≤Real.log s^2 from sq_nonneg _)|>.trans_le (by rw [he])
    have hz:t+u ≤ t+1:= by linarith
    have ht': t^2 ≤ (M (s/2):ℝ):=Nat.le_ceil _
    nlinarith only [h,ht,hv,ht',pow_le_pow_left₀ (by linarith : 0 ≤ t+u) hz 2]
  unfold walls
  exact_mod_cast (show (M s:ℝ)^2≤2*(M (s/2):ℝ)^2 by nlinarith only [sq_nonneg (M (s/2) : ℝ),pow_le_pow_left₀ (show 0 ≤ 3*(M s:ℝ) by positivity) hc 2])
/-- Terms to know at admission (pre L multiplier loan & extent;
Gauges consumes Lift AFTER L set). -/
structure Tab (L : Side) (e : ℝ) : Prop where
  tallies : 0 ≤ e
  lift : 10*(15:ℝ)^4 * Docking.increment e ≤ L.val*e

def naos (B : ℕ) (L : Side) (e y k : ℝ) (n : ℕ) (u v : ℝ) := u/16+wilt B*((Fintype.card (Site L):ℝ)*(salary e*y))+wilt B*((n:ℝ)*k)≤ v
-- δ,K fixed

structure TimeBand (S : Era) (g : ℝ) (L : Side) (P Q : BudgetPoint) (x y t : ℝ) (n : ℕ): Prop where
  lower : Tailprice L P Q S.coast.e
  upper : Tailprice L P Q (load S)
  lamp : 25*radiusB (retime x)+30 ≤ Q.B
  day k (h : 0 ≤ k) (hv : k ≤ Perch.bill (-4) t):
    naos Q.B L (load S) (Perch.gas S.coast y) (fuel S g t k) n (kinetics t) (kinetics t/4) ∧ salary (load S)*Perch.gas S.coast y+fuel S g t k ≤ firstN t
  night k (h : 0 ≤ k) (hv : k ≤ Perch.bill (-1/2) t):
    naos Q.B L S.coast.e (k*w y) (1*salary S.coast.e*k) n (kinetics t) (kinetics t/4) ∧ salary S.coast.e*(k*w y)+(1*salary S.coast.e)*k ≤ ((S.α*k+Perch.bill (1/2) t*k^2)/2)
  tempo : Risible Q.B (kinetics t/4)
  cadence : Real.exp (kinetics t/4)-1+(kinetics t/4) ≤ kinetics t
  infl : Line S g 0 t * x^(-(1:ℝ)) ≤1
lemma risibleQ : ∀ᶠ s in atTop, ∀ (Q : BudgetPoint) x, Q.B=walls x → x ∈ Set.Icc (s/2) s → 25*radiusB (retime x)+30 ≤ Q.B ∧ Risible Q.B (kinetics s/4) ∧ Real.exp (kinetics s/4)-1+(kinetics s/4) ≤kinetics s:= by
  obtain ⟨t,ht'⟩:= eventually_atTop.mp brims
  filter_upwards [Flux.timing, (bill_hi (show (-1/8:ℝ)<0 by norm_num)).eventually (ge_mem_nhds zero_lt_one), Perch.half.eventually_ge_atTop 1,(many.comp Perch.half).eventually_ge_atTop 128,Perch.half.eventually_ge_atTop t] with s h ht hu hv hM Q x hQ hx
  have hs : 1 ≤ x:=hu.trans hx.1
  have hp : Q.B≤walls s:= hQ.trans_le (wall_mono hs (hs.trans hx.2) hx.2)
  let t:=kinetics s
  have hh:=h Q hp
  change t ≤ 1 at ht
  have hh' : M (retime x)≤4*M x:= (ht' x (hM.trans hx.1)).2
  have hx : 128 ≤ M x:= hv.trans (Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_nonneg hu) (Real.log_le_log (zero_lt_one.trans_le hu) hx.1) 2))
  constructor
  · rw [hQ]; change 25*M (retime x)+30≤ M x^2; nlinarith only [hx,hh']
  have hc : 0≤ t:= (Real.exp_pos _).le
  have ha := Real.abs_exp_sub_one_le (by rw [abs_of_nonneg]; all_goals linarith : |t/4|≤1)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity))),abs_of_nonneg (by positivity : 0 ≤ t/4)] at ha
  let W : ℝ:=Q.B+Q.B+1
  refine ⟨⟨?_,?_⟩,?_⟩
  exact div_nonneg hc (by norm_num)
  exact (mul_le_mul_of_nonneg_left (show t/4≤t by linarith only [hc]) (by positivity)).trans hh.1.2
  change _+t/4 ≤ t; change Real.exp (t/4)-1+t/4≤ t; linarith only [ha,hc]

private lemma fandango (D : ℝ) (hD : 0≤D) : ∀ᶠ s in atTop, ∀ x ∈ Set.Icc (s/2) s, wilt (walls x)*(D*bill (-1/2) s) ≤ kinetics s/16 := by
  let C:=(33:ℝ)^4*∑' i, welter i
  have h : 0≤C:=mul_nonneg (by positivity) (tsum_nonneg fun _=>by unfold welter; positivity)
  filter_upwards [Perch.half.eventually_ge_atTop 1, Paint.q_power 4 (1/4) (by norm_num), Paint.absorb (1/4 + -1/2) (-1/8) (by norm_num) (16*C*D)] with s hs hW hv x hx
  have he:wilt (walls x) ≤ C * bill (1/4) s:= by
    rw [show wilt (walls x)=C*(walls x:ℝ)^4 by unfold wilt C;ring]
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (wall_mono (hs.trans hx.1) (hs.trans (hx.1.trans hx.2)) hx.2)) 4).trans hW) h
  unfold kinetics; rw [← overlap] at hv
  linarith only [hv,mul_le_mul_of_nonneg_right he (mul_nonneg hD (show 0 ≤ bill (-1/2) s from (Real.exp_pos _).le))]

/-- post L: numeric receipts for this stage and both energy variants. Before actually choosing a pillar. -/
theorem pedestals (S : Era) (g : ℝ) (L : Side) {e : ℕ} (hU : Tab L (load S)) (hd : Tab L S.coast.e) (hS : 8*salary (load S)≤ S.α) (hα : 8*salary S.coast.e≤ S.α) :
    ∀ᶠ s in atTop, ∀ (n : ℕ), n ≤ e → ∀ x∈Set.Icc (s/2) s, ∀ y∈Set.Icc (s/2) s,∀ (P Q : BudgetPoint),P.B=walls y → Q.B=walls x → TimeBand S g L P Q x y s n:= by
  let b:=salary S.coast.e; let c:=salary (load S)
  have hb:0 ≤ b:=(Real.exp_pos _).le; have hc: 0 ≤ c:=(Real.exp_pos _).le
  let H:ℝ:=Fintype.card (Site L); have hH:0 ≤ H:=by unfold H; positivity
  filter_upwards [Perch.force S.coast.posA 4 0 le_rfl (by norm_num), pass_line S g,late_fee S g hS,risibleQ,Perch.half.eventually_ge_atTop 1,veer,
     fandango (H*c) (by positivity),fandango (e : ℝ) (by positivity),fandango (H*b) (by positivity),fandango ((e:ℝ)*b) (by positivity),Paint.absorb (-4) (-3) (by linarith) (2*c)] with s h hP hF hr ha hV h1 h2 h3 h4 hG n hn x hx y hy P Q hp' hq
  have ht : P.B ≤ 2*Q.B := by
    rw [hq,hp']; apply ((wall_mono (ha.trans hy.1) (ha.trans (hy.1.trans hy.2)) hy.2).trans hV).trans; exact Nat.mul_le_mul_left _ (wall_mono ha (ha.trans hx.1) hx.1)
  obtain ⟨hh,hA,hB⟩:=hr Q x hq hx
  let K:=kinetics s/16; have hk:0≤K:=div_nonneg (Real.exp_pos _).le (by norm_num)
  have hW:= wilty Q.B
  let M' := gas S.coast y; let F:=bill (-1/2) s
  have hv : M' ≤ bill (-4) s:= by unfold M' gas bill; apply Real.exp_monotone; linarith only [h y hy]
  have hZ : (n:ℝ) ≤ e:= Nat.cast_le.mpr hn
  refine ⟨⟨ht,hd.1,hd.2⟩,⟨ht,hU.1,hU.2⟩,hh,fun k hj he=> ?_,fun k hj he=> ?_,hA,hB,hP x hx⟩
  · let m:=fuel S g s k; let v:=firstN s; have h:= hF k hj he
    have h0:c*M' ≤ v/2:= by
      have ha:= mul_le_mul_of_nonneg_left hv hc; change 2*c*_ ≤ v at hG; linarith only [ha,hG]
    change m ≤ v/2 at h
    refine ⟨?_, show c*M'+m≤v by linarith only [h0,h]⟩
    have hg : 0≤v:= (Real.exp_pos _).le
    have ha:v/2 ≤ F:= (show v/2≤v by linarith only [hg]).trans (Glimmer.billed s (by norm_num : (-3:ℝ) ≤ -1/2))
    -- price H*c term initially; need hv→F by hv
    have hL:H*(c*M') ≤ H*c*F:= by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hv.trans (Glimmer.billed s (show (-4:ℝ) ≤ -1/2 by norm_num))) hc) hH
    have hl : n*m ≤ ((e:ℝ)*F):=mul_le_mul hZ (h.trans ha) (fuel_nn _ _ _ _ hj) (by positivity)
    have hu : wilt Q.B*(H*(c*M')) ≤ K:= (mul_le_mul_of_nonneg_left hL hW).trans (hq.symm ▸ h1 x hx)
    have hz : wilt Q.B*(↑n*m) ≤ K:= (mul_le_mul_of_nonneg_left hl hW).trans (hq.symm ▸ h2 x hx)
    change K+ _+wilt Q.B*(↑n*m)≤_; change K+wilt Q.B*(H*(c*M'))+_≤_; unfold K at *; linarith only [hu,hz,hk]
  let t:= 1*b*k
  have Hx:t=b*k:= by rw [show t=1*b*k from rfl,one_mul]
  have he' : k*w y ≤ k:= by simpa only [mul_one] using mul_le_mul_of_nonneg_left (Perch.strong y) hj
  refine ⟨?_,?_⟩
  · have hu: H*(b*(k*w y)) ≤ H*b*F:= by rw [mul_assoc];exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he'.trans he) hb) hH
    have hh : ↑n * t ≤ ↑e*b*F := by rw [Hx, mul_assoc]; exact mul_le_mul hZ (mul_le_mul_of_nonneg_left he hb) (mul_nonneg hb hj) (by positivity)
    have ht : wilt Q.B*(H*(b*(k*w y))) ≤ K:= (mul_le_mul_of_nonneg_left hu hW).trans (hq.symm ▸ h3 x hx)
    have hx : wilt Q.B*((n:ℝ)*t)≤ K:= (mul_le_mul_of_nonneg_left hh hW).trans (hq.symm ▸ h4 x hx)
    change K+wilt Q.B*(H*(b*(k*w y)))+wilt Q.B*(↑n*t) ≤ _; unfold K at *; linarith only [ht,hx,hk]
  change b*(k*w y)+t≤ _; rw [Hx]
  change 8*b ≤ _ at hα
  linarith only [mul_nonneg hb hj,mul_le_mul_of_nonneg_right hα hj, mul_le_mul_of_nonneg_left he' hb, mul_nonneg (show 0≤bill (1/2) s from (Real.exp_pos _).le) (sq_nonneg k)]
end YM.PhysicalNext.InteractingRank.Display.Docking
