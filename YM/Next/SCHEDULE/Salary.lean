import YM.Next.SCHEDULE.Dues

/-! BandGate affordability: no trajectory in these proofs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Lattice Real Clock Instrument
open scoped Topology

local notation "p₀" => plain.P

namespace Postage
variable (A : Postage)

private def bill (x : ℝ) := A.H*(7*p₀ x)^A.D

-- Put all terms on the same coarse center using Alike.
private def coal (M : Instrument) (x : ℝ) :=
    let v := Clock.gap x
    let B : ℝ := Clock.cover x
    A.bill x*((4*v*p₀ x)^ (3:ℕ) + (4/v)^A.D*(Real.exp (-A.rate*B)+
      Real.exp (-(A.rate/4)*M.P x^ (2:ℕ)/(1+B)^((M.bulk+1)*A.D))))

set_option maxHeartbeats 600000 in
private lemma coal_rate (M : Instrument) :
    Tendsto (fun x => A.coal M x/δE x) atTop (𝓝 0) := by
  let p : ℝ := 11/5
  let k : ℝ := -((A.D:ℝ)+p+1)
  have hs := shadows k A.rate A.pos
  have hl : Tendsto (fun x => p₀ x^ (A.D+3)*Clock.gap x^((3:ℝ)-p)) atTop (𝓝 0) := by
    simpa only [Instrument.plain,Instrument.P,Real.rpow_natCast, Real.rpow_one] using light 2 ((A.D+3:ℕ):ℝ) (3-p) (by norm_num [p])
  have hg : Tendsto (fun x => p₀ x^A.D*Clock.gap x) atTop (𝓝 0) := by
    simpa only [Instrument.plain,Instrument.P,Real.rpow_natCast, Real.rpow_one] using light 2 (A.D:ℝ) 1 (by norm_num)
  let B (x : ℝ) : ℝ := Clock.cover x
  have ht : Tendsto (fun x => Clock.gap x ^ k * Real.exp (-(A.rate/4)*M.P x^ (2:ℕ)/(1+B x)^((M.bulk+1)*A.D))) atTop (𝓝 0) := by
    simpa [Instrument.P,B] using incinerate k (A.rate/4) M.center 0 ((M.bulk+1)*A.D) (div_pos A.pos (by norm_num)) M.above
  have h := (hl.const_mul (A.H*7^A.D*4^ (3:ℕ))).add ((hg.mul (hs.add ht)).const_mul (A.H*7^A.D*4^A.D))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hp := gp hx
  unfold coal bill; dsimp only [δE,B,k,p]
  rw [Real.rpow_sub hp,Real.rpow_neg hp.le,Real.rpow_add hp,Real.rpow_add hp,Real.rpow_natCast]
  have he : 0 < gap x^((11:ℝ)/5) := Real.rpow_pos_of_pos hp _
  simp only [rpow_one,pow_add, div_pow,mul_pow]; norm_num
  field_simp

private lemma body_bound (M : Instrument) {x : ℝ} (h : 0 < Clock.cover x) :
    1+(M.body x:ℝ) ≤ (1+(Clock.cover x:ℝ))^(M.bulk+1) := by
  let B : ℝ := Clock.cover x
  have hp : 0 < B := by unfold B; exact_mod_cast h
  have hl : 1 ≤ B := by unfold B; exact_mod_cast (show 1 ≤ cover x from h)
  have he : (1:ℝ) ≤ (1+B)^M.bulk := one_le_pow₀ (by linarith)
  unfold Instrument.body; rw [pow_succ]; push_cast
  have hu : B^M.bulk ≤ (1+B)^M.bulk := by gcongr; linarith
  change 1+B^_≤ _ * (1+B); nlinarith

private lemma body_low (M : Instrument) {x : ℝ} (h : 0 < Clock.cover x) :
    Clock.cover x ≤ M.body x := by
  have hn := M.buys; unfold Instrument.body; nth_rw 1 [show Clock.cover x = Clock.cover x^ (1:ℕ) by rw [pow_one]]
  exact pow_le_pow_right₀ h hn

private lemma subset (M : Instrument) : ∀ᶠ x : ℝ in atTop,
    0 < Clock.cover x ∧ 1+(M.body x:ℝ) ≤ M.P x ∧ 1 ≤ M.P x ∧ M.P x ≤ p₀ x := by
  filter_upwards [counting.eventually (eventually_gt_atTop 0), clock.eventually (eventually_ge_atTop (1:ℝ)),
    (ceiling_cheaper M.center 1 (M.bulk+1) M.above zero_lt_one).eventually (ge_mem_nhds zero_lt_one),
    (growing (show 0<M.center from lt_trans zero_lt_one M.above)).eventually_ge_atTop 1] with x ha hb hc he
  refine ⟨ha, (body_bound M ha).trans ?_, he, Real.exp_monotone (Real.rpow_le_rpow_of_exponent_le hb M.below)⟩
  simpa [P] using (div_le_iff₀ (Real.rpow_pos_of_pos (wp _ _) 1)).1 hc

set_option maxHeartbeats 800000 in
/-- All recurrent band residues fit into arbitrarily small fractions of δ at
fixed stage. Need similar adjacent ratios, not necessarily `y=x+c`. -/
lemma heat (M : Instrument) (θ ε : ℝ) (ht : θ ≤ 1) (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ y, Clock.near x y → Alike M x y 2 →
      A.bundle M θ x y * (M.t x) ^ (3:ℕ) ≤ ε*δE x ∧
      ∀ g, gap x/4 ≤ g → g ≤ 4*gap x → A.residual M θ x y g ≤ ε*δE x := by
  filter_upwards [(A.coal_rate M).eventually (ge_mem_nhds hε),advance (subset M),eventually_gt_atTop (0:ℝ)] with x hx ha hh
  intro y hY he
  let X := p₀ x
  let v := Clock.gap x
  have hv := gp hh
  have hP : 0 < M.P x := wp _ _; have hQ : 0 < M.P y:=wp _ _
  have hA : 0 < A.H := lt_of_lt_of_le zero_lt_one A.h_ge
  have hC := (div_le_iff₀ (show 0 < δE x from rpow_pos_of_pos hv _)).mp (show A.coal M x / δE x ≤ ε from hx)
  obtain ⟨hb,hbX,hG,hxX⟩:=ha _ (Clock.same x)
  obtain ⟨-, -,hy,hyX⟩:=ha _ hY
  have hy0 : LevelCost θ y ≤ (2:ℝ)*X :=
    le_trans ((Real.rpow_le_rpow_of_exponent_le (hy.trans hyX) ht).trans (Real.rpow_one _).le) he.direct.2
  have hpy : M.P y ≤ 2*X := hyX.trans he.direct.2
  have hB : A.bundle M θ x y ≤ A.bill x := by
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ A.D) hA.le
    · have hh : 0<LevelCost θ y := rpow_pos_of_pos (wp _ _) _; positivity
    change _ ≤ 7*X
    change _ ≤ X at hxX
    linarith
  have hB':0 ≤ A.bill x := by unfold bill; have hh : 0<p₀ x:=wp _ _; positivity
  unfold coal at hC
  dsimp only at hC
  have hw : 0 ≤ (4/gap x)^A.D := by positivity
  have hLP : (gap x)*(M.P x) ≤ 4*gap x*p₀ x := by
    gcongr
    linarith
  constructor
  · refine le_trans ?_ hC
    refine mul_le_mul hB (le_trans ?_ (le_add_of_nonneg_right (mul_nonneg hw (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))))) ?_ hB'
    · exact pow_le_pow_left₀ (by positivity) hLP 3
    unfold Instrument.t; positivity
  intro g hgl hgr
  apply le_trans ?_ hC
  unfold Postage.residual
  have hgg : 0 < g := lt_of_lt_of_le (div_pos hv (by norm_num)) hgl
  have hI : g⁻¹^A.D ≤ (4/gap x)^A.D := by
    gcongr
    simp only [← one_div]; apply (div_le_div_iff₀ hgg hv).2; linarith
  refine mul_le_mul hB (add_le_add ?_ (mul_le_mul hI (add_le_add ?_ ?_) ?_ hw)) ?_ hB'
  · have hz := hG.trans hxX
    exact pow_le_pow_left₀ hgg.le (hgr.trans (le_mul_of_one_le_right (by positivity) hz)) _
  · have hb1 := body_low M hb
    exact Real.exp_monotone (mul_le_mul_of_nonpos_left (by exact_mod_cast hb1) (by have := A.pos; linarith))
  · apply Real.exp_monotone
    have hAA := A.pos
    have hT := body_bound M hb
    let B := Clock.cover x; let b := M.body x
    have hj : (1+(b:ℝ))^A.D ≤ (1+(B:ℝ))^((M.bulk+1)*A.D) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hT A.D
    have hr : M.P x/2 ≤ M.P y := by have := he.peek.1; linarith
    have he : A.rate/4 * M.P x^ (2:ℕ) ≤ A.rate * M.P y^ (2:ℕ) := by
      have ht := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr 2) hAA.le
      linarith
    have hz : (A.rate/4 * M.P x^ (2:ℕ))/(1+(B:ℝ))^((M.bulk+1)*A.D) ≤
        A.rate*M.P y^ (2:ℕ)/(1+(b:ℝ))^A.D := by gcongr
    simp only [neg_mul,neg_div]; apply neg_le_neg hz
  · positivity
  positivity
/-- Additional gate for psrec. -/
lemma coordinates (M : Instrument) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x in atTop, ∀ y, Alike M x y 2 →
    ∀ g : ℝ, 0 < g → g ≤ 4*gap x → A.H*(1+(M.body x:ℝ))^A.D/M.P y+g^A.power ≤ ε := by
  have ht : Tendsto (fun x : ℝ => (4*gap x)^A.power) atTop (𝓝 0) := by
    have h := A.pos_p
    simpa [h.ne'] using ((checks_gauge.const_mul (4:ℝ)).rpow_const (p:=A.power) (.inr h.le))
  have hB : Tendsto (fun x => (2*A.H)*((1+(Clock.cover x:ℝ))^((M.bulk+1)*A.D)/(M.P x))) atTop (𝓝 0) := by
    simpa [Instrument.P] using (ceiling_cheaper M.center 1 ((M.bulk+1)*A.D) M.above zero_lt_one).const_mul (2*A.H)
  filter_upwards [ht.eventually (ge_mem_nhds (half_pos hε)), hB.eventually (ge_mem_nhds (half_pos hε)), counting.eventually (eventually_gt_atTop 0)] with x hx hh hL y he g hg hgl
  have hy := Real.rpow_le_rpow hg.le hgl A.pos_p.le
  have hp : 0 < M.P x := wp _ _; have hQ : 0 < M.P y:=wp _ _
  have hA : 0 < A.H := lt_of_lt_of_le zero_lt_one A.h_ge
  have h : A.H*(1+(M.body x:ℝ))^A.D/M.P y ≤ ε/2 := by
    refine le_trans ?_ hh
    have hJ : (1+(M.body x:ℝ))^A.D ≤ (1+(Clock.cover x:ℝ))^((M.bulk+1)*A.D) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (body_bound M hL) A.D
    calc
      _ ≤ A.H*(1+(Clock.cover x:ℝ))^((M.bulk+1)*A.D)/(M.P x/2) := by
        have := he.peek.1; gcongr; linarith
      _ = _ := by ring
  change _ ≤ ε/2 at hx; linarith

/-- Prepare to pass `.Move.forced` rather than just w; retain separately
if also working at changed profile. -/
lemma postforce (M : Instrument) (d : ℝ) (_hd : 0 < d) (hh : d ≤ A.rate/8) :
    ∀ᶠ y : ℝ in atTop, ∀ g, 0 < g → g ≤ 2*gap y →
      A.H*Real.exp (-A.rate*(M.t y/g)^ (2:ℕ)) ≤ Real.exp (-d*(M.P y)^ (2:ℕ)) := by
  have h := A.pos
  have ht : Tendsto (fun y => A.rate/8*(M.P y)^ (2:ℕ)) atTop atTop := by
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact (tendsto_pow_atTop (by norm_num)).comp (growing (lt_trans zero_lt_one M.above))
  filter_upwards [ht.eventually_ge_atTop (Real.log A.H), eventually_gt_atTop (0:ℝ)] with y hy hz g hg hb
  have hq : 0 < M.P y:=wp _ _
  nth_rw 1 [← Real.exp_log (lt_of_lt_of_le zero_lt_one A.h_ge)]
  rw [← Real.exp_add]; apply Real.exp_monotone
  have hx : M.P y/2 ≤ M.t y/g := by
    apply (le_div_iff₀ hg).2; unfold Instrument.t; nlinarith only [hb,hq]
  have hv := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx 2) h.le
  have he := mul_le_mul_of_nonneg_right hh (show 0 ≤ (M.P y)^ (2:ℕ) by positivity)
  change log A.H ≤ _ at hy; linarith

-- for startup where measuring w_N
lemma saved (M : Instrument) (d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop, ∀ x, Alike M x y 2 → Real.exp (-d*(M.P y)^ (2:ℕ)) ≤ M.w x := by
  have hr := growing (lt_trans zero_lt_one M.above)
  have hk : Tendsto (fun y => d*M.P y) atTop atTop := Tendsto.const_mul_atTop hd hr
  filter_upwards [hk.eventually_ge_atTop 2,hr.eventually_ge_atTop 1] with y hy hz x hx
  apply Real.exp_monotone
  have hp := hx.peek.1
  have hq : 0 < M.P x := wp _ _
  have ht : (M.P x)^((1:ℝ)/5) ≤ 2*M.P y := by
    apply le_trans (Real.rpow_le_rpow hq.le hp (by norm_num))
    have hi : 1 ≤ 2*M.P y := by change 1 ≤ M.P y at hz; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hi (show (1:ℝ)/5 ≤ 1 by norm_num)
  change 2 ≤ d*M.P y at hy
  have he : 0 < M.P y := wp _ _; nlinarith
end Postage

lemma just_near (c : ℝ) : ∀ᶠ x in atTop, near x (x+c) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop |c|] with x hx
  simpa [near] using hx

lemma Instrument.pitched (M : Instrument) : ∀ᶠ x in atTop,
    1 < x ∧ 9 ≤ M.body x ∧ 1 ≤ M.P x ∧ M.t x ≤ 1 := by
  have ht : Tendsto M.t atTop (𝓝 0) := by simpa [t,Instrument.P,mul_comm] using! light M.center 1 1 (by norm_num)
  have hp := growing (lt_trans zero_lt_one M.above)
  filter_upwards [eventually_gt_atTop (1:ℝ),counting.eventually_ge_atTop 9,hp.eventually_ge_atTop 1,
    ht.eventually (ge_mem_nhds zero_lt_one)] with x hh hb hg he
  exact ⟨hh,hb.trans (Postage.body_low M (by change 9≤Clock.cover x at hb; omega)),hg, he⟩

variable {G : Gauge} {s : Survey G} {q : Quote} {e : Exchange} {M : Instrument} {A : Postage}

set_option maxHeartbeats 800000 in
/-- Explicit BandGate issued on *all* entrants sufficiently deep,
applicable any time in the given stage. -/
lemma BandGate.authorize (j i : ℕ) (L θ θ' d c : ℝ) (h : Buy s q e j i L) (ht : 0 < θ)
    (hy : θ ≤ θ') (hθ : θ ≤ 1) (hd : 0 < d) (hg : d ≤ A.rate/8) :
    ∀ᶠ x in atTop, BandGate s q e M A j i L θ θ' d c x := by
  let C := e.cost; have hC : 1 ≤ C := e.ok.2.2.1; have hpC : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hL : 0<L := lt_of_lt_of_le (by norm_num) h.block
  have hp := growing (d:=plain.center) (by norm_num [plain])
  have hu : Tendsto (LevelCost θ') atTop atTop := (tendsto_rpow_atTop (lt_of_lt_of_le ht hy)).comp hp
  have hA : Similar (LevelCost θ) := similar_watch_power 2 θ
  have hD : Similar δE := similar_gap_power ((11:ℝ)/5)
  let η := 1/(8*C); have hη : 0<η := by dsimp only [η]; positivity
  filter_upwards [advance (M.pitched.and <| (checks_gauge.eventually (ge_mem_nhds zero_lt_one)).and <|
      (A.postforce M d hd hg).and <| (Postage.saved M d hd).and (hp.eventually_ge_atTop 1)),
    M.support 2 (by norm_num),just_near c,hA 2 (by norm_num),hD 2 (by norm_num),
    hu.eventually_ge_atTop (q.finish.loop j i * L^ (4:ℕ)),
    A.coordinates M (1/L^((2:ℝ)/5)) (by positivity), A.heat M θ η hθ hη] with x hX hP hx hz hn hr hf he
  let y := x+c
  obtain ⟨⟨htx,hkx,hpx,hex⟩,hc,-,-,hm⟩:=hX x (same x)
  obtain ⟨⟨hty,hky,hpy,hey⟩,-,hyF,hs,-⟩:=hX y hx
  have hs0 : Alike M x y 2 := hP x y (same x) hx
  refine ⟨⟨htx,hty⟩,⟨hkx,hky⟩,⟨hpx,hpy⟩,⟨hex,hey⟩,hs0,hr,?_ ,hs x hs0,?_⟩
  · exact (hz y x hx (same x)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm hy) (by norm_num))
  intro β hb y' g C'
  have hxx := lt_trans zero_lt_one htx; have hyy : 0<y := lt_trans zero_lt_one hty
  have hβ := gp (lt_of_lt_of_le (show 0 < y/4 by positivity) hb.1)
  obtain ⟨hx',hy'⟩:=band_gap y β hyy hb
  have hg1 : gap x/4 ≤ g := by have := hs0.gap.1; change gap x ≤ 2*gap y at this; unfold g; linarith
  have hg2 : g ≤ 4*gap x := by have := hs0.gap.2; change gap y ≤ 2*gap x at this; unfold g; linarith
  refine ⟨?_,?_,hyF _ hβ hy',hf _ hs0 _ hβ hg2⟩
  all_goals
    let S := A.switch M C L θ x y g
    have hq : C*(C/L+1/(16*C)) ≤ 1/8 := by
      have hz : C*(C/L+1/(16*C))=C^ (2:ℕ)/L+1/16 := by field_simp
      rw [hz]; have hu : C^ (2:ℕ)/L ≤ 1/16 := h.shrink; linarith
    obtain ⟨h1,h2⟩:=he y hx hs0
    have hc1 := h2 g hg1 hg2
    have hd1 : 0 < δE x := rpow_pos_of_pos (gp hxx) _
    have hd2 : δE y ≤ 2*δE x:= hn y x hx (same x)
    have hδ : C*S ≤ (1/2)*δE x := by
      calc
        _ ≤ 1/8*δE y + C*(η*δE x) := by
          unfold S Postage.switch; rw [mul_add,← mul_assoc]
          exact add_le_add (mul_le_mul_of_nonneg_right hq (Real.rpow_pos_of_pos (gp hyy) _).le)
            (mul_le_mul_of_nonneg_left hc1 hpC.le)
        _ ≤ 1/8*(2*δE x)+1/8*δE x := by
          rw [show C*(η*δE x)=(1/8)*δE x by unfold η; field_simp]; gcongr
        _ ≤ _ := by linarith
  · have hη0 : η ≤ 1/8 := by unfold η; gcongr; linarith
    have hK := h1.trans (mul_le_mul_of_nonneg_right hη0 hd1.le)
    change C*S+_ < _; linarith
  apply hδ.trans
  have hh := gp hxx
  change gap x ≤ 1 at hc
  have hb1 := Real.rpow_le_rpow_of_exponent_ge hh hc (show (2:ℝ) ≤ (11:ℝ)/5 by norm_num)
  have hE : δE x ≤ gap x^ (2:ℕ) := by simpa [δE,rpow_two] using hb1
  calc
    _ ≤ δE x := by linarith
    _ ≤ gap x^ (2:ℕ) := hE
    _ ≤ _ := pow_le_pow_left₀ hh.le (le_mul_of_one_le_right hh.le hpx) _
end YM.Next.Scheduling
