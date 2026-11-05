import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Bind
import YM.Work.H02




/-! # Post-noise/pre-reset coefficient economics.
Tilt κ for the merger not used anywhere in the input `KBound` by retuning the
K values. Includes the `Valid` receipt on the FINAL alphabet with exact
label moves through the same numbers. This file does not require anything
like ∆ coinciding with any tested ratio. Cost at the realized budget,
pre/post scheduling obligations remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson Ovens Ovens.Pipes Next.Scheduling Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {n : Side}

structure Earnings (b : BudgetPoint) (R : Activities G n) (H₀ w : ℝ) : Prop where
  core : Profiled R (boost b) H₀
  branches : R.ForcedFamily b
  swamp : R.KBound (boost b) w

variable {P : PathData G} {p : Clip} {b : BudgetPoint} {α ε σ C Λ H₀ w : ℝ} {R : Activities G n}

-- anchor receipts from the SAME width. Raw durations explicit; especially
-- clip in every failed-flag term. schedule buys inequalities on these numbers
private lemma sealed_add {ι : Type} {x : ι→RegularAddress n} {f g : ι→ℝ} {a d : ℝ} (h : Sealed b x f a) (he : Sealed b x g d) :
    Sealed b x (fun i=> f i+g i) (a+d) := by
  intro y; convert budget_plus (h y) (he y) using 2
  next i => split_ifs <;> simp [BudgetPoint.mass,mul_add]
private lemma sealed_scale {ι : Type} {x : ι→RegularAddress n} {f : ι→ℝ} {a d : ℝ} (hd : 0 ≤ d) (h : Sealed b x f a) :
    Sealed b x (fun i=> d*f i) (d*a) := by
  intro y; convert budget_scale hd (h y) using 2
  next i => split_ifs <;> simp [BudgetPoint.mass,mul_left_comm]

lemma shallow {f : Config G n → ℝ} {b : BudgetPoint} {X : Support n} (h : (boost b).Regular X f) : b.Regular X f :=
  ⟨h.sites,h.borel,h.symmetry,h.smooth,h.hasDerivs⟩

/-- Earnings pre-L sensitive to amplification of HRGv. -/
def grantE (G : Gauge) (p : Clip) (B : BudgetPoint) (H₀ σ C α ε : ℝ) := let b:=boost B
    (Real.exp b.supportExponent*paysLive G b)*H₀ +
      (|ε| * (stapleY G p b σ C+stapleT G p b C) +
        (|α+ε| *Post.full G 3 b σ C + |α+ε| * Post.full G 4 b σ C))

def grantLog (G : Gauge) (p : Clip) (B : BudgetPoint) (H₀ σ C α ε : ℝ) := let b:=boost B
    (Real.exp b.supportExponent*paysAttach G b)*H₀ +
      (|α+ε| *(stapleC p b C+stapleY G p b σ C)+|ε| *(2*stapleT G p b C))

/-- local shape-packet output and normal bills before multiplier-merging. -/
lemma taps (hD : P.Bounds p σ C Λ) (hg : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w) (α ε : ℝ) :
    let d:=ink P p b R α ε; let X:=ward P b R
    X.Digests d b (grantE G p b H₀ σ C α ε) w ∧
      ∃ c, Sealed (boost b) X.reg c (grantLog G p b H₀ σ C α ε) ∧ ∀ i,0 ≤ c i ∧ ∀ U,‖d.logarithm i U‖ ≤ c i := by
  intro d X
  let B:=boost b
  let V := corners P b R; let F:= arrange P p R α ε; let L:=hooks P p b R α ε; let J:=wheel n
  let gE := grantE G p b H₀ σ C α ε; let gL:=grantLog G p b H₀ σ C α ε
  obtain ⟨c,hc,hC⟩:= hr.core.bound
  have ht (i) := hints R B hs (by omega) i (hr.core.smooth i) (hc i)
  have ht₁ i := (hD.invariant i).2.1; have ht₂ i := (hD.invariant i).2.2
  let β (k : ℕ) {n} (F : ℕ→Atom G k) (i : Post n) := |-(α+ε)| *Post.hairpin F B i.token
  let money : Scroll n→ℝ := sorting (fun i=>paysLive G B*c i) (fun i=>skeletonCharge P p B ε i.token)
    (β 3 P.cubic) (β 4 P.quartic)
  let salary : Scroll n → ℝ := sorting (fun i=>paysAttach G B*c i) (fun i=>coverCharge P p B α ε i.token) (fun _=>0) (fun _=>0)
  have he (i) : B.Regular (V i).support (F i) ∧ B.supBounds (V i).site (V i).support (F i) (money i) ∧
      F i 1=0 ∧ (Nonwrapping (V i).support (V i).site → ∀ A C, IsAffineDirection (V i).site A → IsAffineDirection (V i).site C →
        logHessian (F i) A C=0) := by
    rcases i with i|(j|i|i)
    · exact ⟨(ht i).1,(ht i).2.1,(ht i).2.2.1,(ht i).2.2.2.1⟩
    · exact anchorsPay P p B hs (by omega) ε j
    · obtain ⟨h₁,h₂⟩:= Post.active P.cubic B ht₁ i; obtain ⟨h₃,h₄⟩ := Post.wont (k:=0) B P.cubic hs ht₁ i
      refine ⟨reg_scale _ h₁,sup_scale _ h₂,?_,fun _ A C _ _ => ?_⟩
      · change -(α+ε) • Post.fee P.cubic i (1:Config G n)=0; rw [h₃,smul_zero]
      rw [log_eq_H]; change H (_ • _) A C=0
      rw [scalar_jet h₁,← log_eq_H, h₄, mul_zero]
    obtain ⟨h₁,h₂⟩:= Post.active P.quartic B ht₂ i; obtain ⟨h₃,h₄⟩ := Post.wont (k:=1) B P.quartic hs ht₂ i
    refine ⟨reg_scale _ h₁,sup_scale _ h₂,?_,fun _ A C _ _ => ?_⟩
    · change -(α+ε) • Post.fee P.quartic i (1:Config G n)=0; rw [h₃,smul_zero]
    rw [log_eq_H]; change H (_ • _) A C=0
    rw [scalar_jet h₁,← log_eq_H, h₄, mul_zero]
  have hm : Sealed B V money gE := by
    intro x
    have hh (k : ℕ) (F : ℕ→Atom G k) (h : SumBudget (fun i=> (F i).budget σ) C) :
        Sealed B (n:=n) (Post.park F) (β k F) (|α+ε| *Post.full G k B σ C) := by
      have h := sealed_scale (abs_nonneg (-(α+ε))) (Post.earned (n:=n) hD.width hg.2 h)
      simpa only [β, abs_neg] using! h
    apply countTypes (h:= boost_stamp R B _ (paysLive_pos ..|>.le) hC (fun i=>(hc i).1) x)
    apply countTypes (h:= sealed_scale (abs_nonneg ε) (sealed_add (shelfY (n:=n) hD hg) (shelfT hD hg)) x)
    exact countTypes (hh 3 _ hD.three x) (hh 4 _ hD.four x)
  have h₁ (i : Scroll n) : ∀ U, L i U≠0 → ¬Healthy b.threshold (V i).support U := by
    rintro U hu hw; apply hu; rcases i with i|(j|i|i)
    · exact for_cover R b i U hw
    · exact refund_visits P p b hv U j hw α ε
    · rfl
    rfl
  have h₂ (i : Scroll n) : GaugeInvariant (L i) ∧ Measurable (L i) ∧ UsesFinal b.threshold (V i).support (L i) ∧
      ∀ U : Config G n, ‖L i U‖ ≤ salary i := by
    rcases i with i|(j|i|i)
    · exact (ht i).2.2.2.2
    · obtain ⟨h₁,h₂,h₃⟩:=respects P p b hv α ε j
      exact ⟨h₁,h₂,h₃,fun U => refund_cost P p B α ε j U⟩
    · exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _=>norm_zero.le⟩
    exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _=>norm_zero.le⟩
  have hP (i) : 0 ≤ salary i := (norm_nonneg _).trans ((h₂ i).2.2.2 1)
  have hl : Sealed B X.reg (salary ∘ J) gL := by
    intro x
    apply budget_pull J J.injective (w:=fun i=> if (V i).site=x then B.mass (V i).support (salary i) else 0)
    apply countTypes (h:= boost_stamp R B _ (paysAttach_pos ..|>.le) hC (fun i=>(hc i).1) x)
    let Q := sealed_add (sealed_scale (abs_nonneg (α+ε)) (sealed_add (shelfClip (n:=n) hD hg) (shelfY hD hg)))
      (sealed_scale (abs_nonneg ε) (sealed_scale (by norm_num : (0:ℝ) ≤ 2) (shelfT hD hg)))
    let a := |α+ε| *(stapleC p B C+stapleY G p B σ C)+|ε| *(2*stapleT G p B C)
    refine budget_loosen (countTypes (a:=a) (b:=(0:ℝ)+(0:ℝ)) (?_) (countTypes ?_ ?_)) (by simp [B,a])
    · exact Q x
    all_goals change SumBudget (fun i : Post n=> if (V _).site=x then B.mass _ 0 else 0) 0; simp [BudgetPoint.mass,SumBudget]
  refine ⟨?_,_,hl,fun i=>⟨hP _,(h₂ (J i)).2.2.2⟩⟩
  have hM s z := noted_spin P p b R hn hs α ε hr.core s z
  refine ⟨⟨⟨fun i=>shallow (he (J i)).1,fun i=>(he (J i)).2.2.1,fun i=>(he (J i)).2.2.2⟩,?_,fun s z => (hM s z).1,?_,?_⟩,
    fun i=>h₁ (J i),⟨_, (totalBooked (fun i=>hP (J i)) hl).2.1, fun i => (h₂ (J i)).2.2.2⟩, fun i=>(h₂ (J i)).1,
    fun i=>(h₂ (J i)).2.2.1,fun i=>(h₂ (J i)).2.1,fun s z=> (hM s z).2⟩
  · obtain ⟨a,c,u,v,g,h,m⟩:=hr.branches; exact ⟨a,c,u,v,g,h,m⟩
  · refine ⟨money ∘ J,fun i=>(he (J i)).2.1,fun x => budget_pull J J.injective
      (budget_mono (hm x) (g:=fun i=> if (V i).site=x then b.mass (V i).support (money i) else 0) ?_ ?_)⟩
    · intro i; split
      · exact mul_nonneg (Real.exp_pos _).le (he i).2.1.1
      rfl
    intro i; split_ifs
    · exact tighter _ (he i).2.1.1
    rfl
  obtain ⟨a,hA,ha⟩:=hr.swamp; refine ⟨a,hA,fun x => budget_mono (ha x) (g:=fun i=> if x∈(R.forced i).support then b.mass (R.forced i).support (a i) else 0) ?_ ?_⟩
  · intro i; split
    · exact mul_nonneg (Real.exp_pos _).le (hA i).1
    rfl
  intro i; split_ifs
  · exact tighter _ (hA i).1
  rfl

/-- Post-L/station reserve. Don't manufacture output energies from the
*final* gas on the LHS of this test. -/
structure Reserve (p : Clip) (b : BudgetPoint) (G : Gauge) (H₀ σ C w α ε κ γ : ℝ) : Prop where
  radius : 0≤γ
  till : 0≤κ
  capacity : ((b.B+b.B+1)^4:ℕ)*γ≤1
  localLog : grantLog G p b H₀ σ C α ε ≤ 1
  yieldBudget : Real.exp κ*w+2*(fare b*grantLog G p b H₀ σ C α ε)≤γ

variable {κ γ : ℝ}

lemma flowing (hD : P.Bounds p σ C Λ) (hg : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w)
    (he : Reserve p b G H₀ σ C w α ε κ γ) : (ward P b R).Buys (ink P p b R α ε) b κ γ := by
  let X:=ward P b R; let d:=ink P p b R α ε
  obtain ⟨_,c,hc,h⟩:= taps hD hg hv hs hn hr α ε
  obtain ⟨k,hk,hK⟩:=hr.swamp
  let f : Ovens.Label → ℝ := Sum.elim (fun l=>Real.exp κ * k l) (fun l=> 2*c l)
  refine ⟨⟨he.radius,he.till,?_⟩,f,?_,?_,?_⟩
  · exact_mod_cast he.capacity
  · rintro (l | l)
    · exact mul_nonneg (Real.exp_pos _).le (hk l).1
    exact mul_nonneg zero_le_two (h l).1
  · rintro (l | l) U
    · change |R.K l U| ≤ Real.exp (-κ)*(Real.exp κ*k l)
      rw [← mul_assoc, ←Real.exp_add, neg_add_cancel,Real.exp_zero,one_mul]; exact (hk l).2 _
    change |Real.exp (d.logarithm l U) - 1| ≤ 1*(2*c l); rw [one_mul]
    have hl : |d.logarithm l U| ≤ c l := (h l).2 _
    apply le_trans (Real.abs_exp_sub_one_le (hl.trans ?_)) (mul_le_mul_of_nonneg_left hl zero_le_two)
    have hq := budget_single (hc (X.reg l).site) l
    rw [if_pos rfl] at hq; exact ((boost b).loMass _ _ (h l).1).trans (hq.trans he.localLog)
  intro x
  have hq := budget_scale (by norm_num : (0:ℝ) ≤ 2) (turnToHit (fun i=> (h i).1) hc x)
  refine budget_loosen (countTypes (a:=Real.exp κ*w) (b:=2*(fare b*grantLog G p b H₀ σ C α ε)) ?_ ?_) he.yieldBudget
  · let y (i : ℕ) := coverNumber b.B (R.forced i).support
    apply budget_mono (budget_scale (Real.exp_pos κ).le (hK x)) ?_ ?_
    · intro i; dsimp only [Function.comp_apply]; split <;> first | exact le_rfl | exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (hk _).1) (Real.exp_pos _).le
    intro i; change (if x∈(R.forced i).support then Real.exp κ*k i*Real.exp ((b.supportExponent+1)*y i) else 0) ≤ _
    split_ifs <;> try simp
    change _≤Real.exp κ*(Real.exp ((b.supportExponent+2)*y i)*_); rw [mul_assoc, mul_comm (Real.exp ((b.supportExponent+2)*_))]
    have ht:= (hk i).1; gcongr; linarith
  change SumBudget (fun i=> if x∈ (X.reg i).support then 2*c i*Real.exp ((b.supportExponent+1)*coverNumber b.B (X.reg i).support) else 0) _
  convert hq using 2
  next i => split_ifs <;> simp only [X,mul_zero,mul_assoc]

lemma valid_output (hD : P.Bounds p σ C Λ) (hg : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w)
    (he : Reserve p b G H₀ σ C w α ε κ γ) : (written P p b R α ε).Valid b (grantE G p b H₀ σ C α ε) (Bid.quote κ γ) := by
  have hh := flowing hD hg hv hs hn hr he
  have hp := (taps hD hg hv hs hn hr α ε).1
  let e:=pelletKey (ward P b R)
  obtain ⟨hx,hm⟩:= Work.H03.answer _ _ _ _ e _ _ _ hp
  exact ⟨⟨hp.stamp.regular.smooth,hp.stamp.regular.at_flat,hp.stamp.regular.vanish⟩,hx,hm,hp.stamp.boundE,
    Work.H02.answer _ _ _ _ e _ _ _ _ _ _ le_rfl hp hh⟩
end YM.AnalyticBridge.CouplingShape
