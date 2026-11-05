import YM.AnalyticBridge.VERIFIED_RESET_STEP.Currency
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Payment
import YM.Extra.ITERATION_NO_LOSS.Pre

/-! Purchase points on the actual transition as a monotone late gate.
Room for recipe batch prices *and* actual Move.forcing; the latter still
needs a suitable F/postCost rate agreement. Buy the former from LOCAL E,K
bounds not arbitrary coupling returns at the loose Echarge price (which
needn't itself be ≤ allowance on an arbitrary issued schedule). -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Time
open Filter Function Set Lattice Wilson RG Precision Collection Next.Scheduling Clock Instrument UVNext.CouplingReset Progress.DirectedRecipe
open Input Supply Push.PriceCompiler Shoot
open scoped Topology BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}

lemma late_force (d c : ℝ) (hd : 0 < d) : ∀ᶠ x : ℝ in atTop, ∀ F : Postage, d ≤ F.rate/4 → ∀ β : ℝ, inBand (x+c) β →
    let y := x+c; let r := Real.exp (-Payments.Pairing.kGoal F y β)
    r ≤ Real.exp (-d*plain.P y ^ (2:ℕ)) ∧ r ≤ plain.w x := by
  have h : Tendsto (fun x : ℝ => x+c) atTop atTop := tendsto_atTop_add_const_right atTop _ tendsto_id
  filter_upwards [h.eventually (eventually_gt_atTop (0:ℝ)),plain.support 2 one_lt_two, just_near c,h.eventually (Postage.saved plain d hd)] with x hx hw he hS F hF β hβ y r
  have hsaved := hS x (hw x y (same x) he)
  suffices h : r ≤ Real.exp (-d*plain.P y ^ (2:ℕ)) from ⟨h,h.trans hsaved⟩
  apply Real.exp_le_exp.mpr
  obtain ⟨hl,hu⟩ := band_gap _ _ hx hβ
  have hg : 0 < gap β := (half_pos (gp hx)).trans_le hl
  have hy : 0 < plain.P y := wp _ _
  have ht : plain.P y ≤ (plain.t y / gap β)*2 := by
    unfold Instrument.t; dsimp [y] at *; rw [div_mul_eq_mul_div, le_div_iff₀ hg]; nlinarith [wp plain.center (x+c)]
  unfold Payments.Pairing.kGoal; nlinarith [mul_le_mul_of_nonneg_left (sq_le_sq₀ hy.le (hy.le.trans ht) |>.2 ht) hd.le,
    mul_le_mul_of_nonneg_right hF (sq_nonneg (plain.t y / gap β))]

abbrev Scouts {F : ℕ → ℕ → Postage} := ∀ i j, Forecast (F i j)
def shop {D : Rolls s} (P : PostCost D) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) (j i : ℕ) (x : ℝ) :=
    let y := x+G.slopeConstant*Real.log (D.L j).val; let S := s.profile i; let H := credit G S * δE x
    ∀ p : BudgetPoint, Same S p → p.B=cover x → p.threshold=plain.t x → (S.clip.direct≤1 → WilsonStartup.Decent S.clip p) ∧ Geo.Width p S.clip S.width ∧
      ∀ e : Exchange, ∀ α θ β : ℝ, |α| ≤ alphaBound D j → Next.Scheduling.inBand y β →
        let L := ((D.L j).val:ℝ); let f:=F j i; let port := e.cost * f.switch plain e.cost L θ x y (gap β)
        let δ := δE x / 32; let γ := Real.exp (-Payments.Pairing.kGoal f y β)
        H ≤ port ∧ δ ≤ port + f.bundle plain θ x y * (plain.t x)^3 ∧ Fees G p S.clip S.width S.paths α H ((A j i).pair.strong y β) δ γ ∧
        (P.g j ≤ f.rate/4 → γ ≤ Real.exp (-(P.g j)*plain.P y ^ (2:ℕ)) ∧ γ ≤ plain.w x)

abbrev Opened (W : Delays Θ) (P : PostCost D) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) : Prop :=
    ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → shop P A j i x

lemma late (P : PostCost D) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) (g : G.Simple) (j : ℕ) :
    ∀ᶠ x in atTop, ∀ i, StepStages j i → shop P A j i x := by
  apply eventually_transitions; intro i _
  let c := G.slopeConstant * Real.log (D.L j).val
  have hL : 1 ≤ ((D.L j).val:ℝ) := by exact_mod_cast (D.L j).pos
  have hu : 0 ≤ alphaBound D j := add_nonneg (s.profile _).drift_ge (abs_nonneg _)
  have h := cash G (s.profile i) (A j i) _ hu c (mul_nonneg (Gauge.slopeConstant_pos g).le (Real.log_nonneg hL))
  filter_upwards [h,late_force (P.g j) c (P.posG j)] with x h1 h2
  intro p hp hb ht
  obtain ⟨hd,hW,hK⟩ := h1 p hp hb ht; exact ⟨hd,hW,fun e α θ β hα hβ =>
    let he := hK e _ (zero_lt_one.trans_le hL) α θ β hα hβ
    ⟨he.1,he.2.1,he.2.2,fun hv => h2 _ hv _ hβ⟩⟩

/-- Operate on a proposed W BEFORE Bar/Wait or choosing levels. -/
lemma open_shop (g : G.Simple) (P : PostCost D) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) (V : Delays Θ) :
    ∃ X : Delays Θ, Boost V X ∧ ∀ W' : Delays Θ, Boost X W' → Opened W' P A := by
  obtain ⟨v,_,he,hv⟩ := collect_upper V.betaEntry _ (late P A g)
  exact ⟨{V with betaEntry := v},⟨he, le_rfl, le_rfl, le_rfl⟩,fun W' hw j x hx => hv j x ((hw.beta j).trans hx)⟩

def forecastK (a : Levels G) (m : ℕ) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) (β : ℝ) :=
    (A (a.clock.J (m+1)) (a.clock.J m)).pair.strong (a.clock.hatBeta (m+1)) β
def forecastE (a : Levels G) (m : ℕ) := credit G (a.params m) * a.clock.allowance m
def fraction (a : Levels G) (m : ℕ) := a.clock.allowance m / 32
def quoteHard (a : Levels G) (m : ℕ) (F : ℕ → ℕ → Postage) (β : ℝ) :=
    Real.exp (-Payments.Pairing.kGoal (F (a.clock.J (m+1)) (a.clock.J m)) (a.clock.hatBeta (m+1)) β)
lemma quoteHard_le (a : Levels G) (m : ℕ) (F : ℕ → ℕ → Postage) (β : ℝ) : quoteHard a m F β ≤ Kcharge F a m β := by
  unfold quoteHard Payments.Pairing.kGoal Kcharge; simp only [neg_mul,← (Deployment.clock_eqns a.clock (m+1)).2.2.2.2.2.2]
  exact le_mul_of_one_le_left (Real.exp_nonneg _) (F _ _).h_ge

lemma E_rises {n : Side} {p : BudgetPoint} {A : Activities G n} {a b : ℝ} (h : A.EBound p a) (he : a ≤ b) : A.EBound p b := by
  obtain ⟨u,h,h'⟩ := h; exact ⟨_,h,fun x => Push.AbsoluteSums.budget_loosen (h' x) he⟩
lemma K_rises {n : Side} {p : BudgetPoint} {A : Activities G n} {a b : ℝ} (h : A.KBound p a) (he : a ≤ b) : A.KBound p b := by
  obtain ⟨u,h,h'⟩ := h; exact ⟨_,h,fun x => Push.AbsoluteSums.budget_loosen (h' x) he⟩

variable (B : Directed G I Z K P) {q : ResetPrices} {N m p : ℕ} {Q : In B.a m p} {s' : Set ℝ}

lemma now (hm : m<N) {F : ℕ → ℕ → Postage} {A : Scouts (F:=F)} (h : Opened W P A) (hf : P.g (B.a.clock.J (m+1)) ≤ (F (B.a.clock.J (m+1)) (B.a.clock.J m)).rate/4)
    (hq : credit G (B.a.params m) ≤ q.cost (B.a.clock.J (m+1)) (B.a.clock.J m) / 4) (E : ℕ → ℕ → Exchange)
    (hC : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x)
    (hb : ∀ x∈s',(Q x).beta ∈ band B.a (m+1)) : let a:=B.a
    let H := forecastE a m; let w x := forecastK a m A (Q x).beta; let δ := fraction a m; let γ x := quoteHard a m F (Q x).beta
    Return.Prices B N m p q s' (fun _ => H) w (fun _ => δ) γ ∧ ∀ x∈s', H ≤ portion E F a m (Q x).beta ∧ δ ≤ Echarge E F a m (Q x).beta := by
  let a:=B.a; let r:=a.budget m; let j:=a.clock.J (m+1); let i:=a.clock.J m; let u:=a.clock.hatBeta m; let y:=a.clock.hatBeta (m+1)
  obtain ⟨ho,_,_,he,hE,_,ht⟩ := Deployment.clock_eqns a.clock m
  have h' := h _ _ (B.valid.pays m) _ (step_paid a m)
  have hu : y=u+G.slopeConstant*Real.log (D.L j).val := by rw [← block_eq B.valid]; exact (Deployment.hat m).symm
  have hp : r.B = cover u := rfl
  have hs : s.profile i = a.params m := (params_eq B.valid m).symm
  have ha : Same (a.params m) r := ⟨rfl,rfl,rfl⟩
  obtain ⟨hD,hW,hK⟩ := h' r (hs.symm ▸ ha) hp ht
  have hide := (B.support.cap N m hm.le).metric
  have hM x (hx : x∈s') := hK (E j i) (B.kin.alpha N m) (a.clock.theta j) (Q x).beta (within_alpha hm) (hu ▸ trial_in (hb x hx))
  have hX : 0 ≤ a.clock.allowance m := Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  dsimp only []
  refine ⟨⟨hs ▸ hD (hs ▸ Canonical.direct_le_one hide), hs ▸ hW,fun _ _ => ?_, hC,fun x hx => ?_,fun x hx v hv => ?_⟩,fun x hx => ?_⟩
  · exact (mul_le_mul_of_nonneg_right hq hX).trans_eq (by unfold funds; ring)
  · have he := hM x hx |>.2.2.1
    change Fees G r _ _ _ _ _ _ _ _
    rw [hs, ← hu] at he
    change Fees G r _ _ _ _ (forecastE a m) ..
    unfold forecastE fraction; rw [‹a.clock.allowance m = _›]; exact he
  · have hK := (hM x hx).2.2.2 hf
    obtain ⟨_,hP,_⟩ := Deployment.clock_eqns a.clock (m+1)
    refine ⟨{ hv with
      boundE := E_rises hv.boundE (show fraction a m ≤ a.clock.allowance m by unfold fraction; linarith),
      boundK := K_rises hv.boundK ?_ }, K_rises hv.boundK ?_⟩
    · dsimp only [quoteHard]; rw [hE]; simpa only [a,j,i,y,u,← hu] using! hK.2
    dsimp only [quoteHard,Return.forcing]; rw [show B.a.clock.monitor (m+1) = _ from hP]
    rw [← hu] at hK; exact hK.1
  have h1 := (hM x hx).1; have h2 := (hM x hx).2.1
  change forecastE a m ≤ portion .. ∧ fraction a m ≤ Echarge ..
  unfold forecastE fraction Echarge portion; dsimp only []; rw [he,block_eq B.valid,ht]; rw [hs] at h1; rw [← hu] at h1 h2; exact ⟨h1,h2⟩
end YM.AnalyticBridge.VerifiedReset.Time
