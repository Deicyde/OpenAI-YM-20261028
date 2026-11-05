import YM.Extra.MULTISOURCE_BOUNDS.Corrections
import YM.Extra.MULTISOURCE_BOUNDS.Forks

/-!
# Pricing projection / log / extraction & restoration procedure

Alternative towards `Raw`. The depth-indexed unmarked and packet estimates
below are tested through the exponents in `System` (on the actual alphabets);
NOT implied by stability/positivity of the kernel. Here we grant thresholds
for any given per-plateau positive-power decay exponent and projection-degree
asks; must also be joined with sufficient physics prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.System
open Function Filter Lattice RG RG.Supply Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Germs Merger Pressure Precision Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {C : Family G} {m : ℕ}

lemma overheadAt_one {H : Hol G} {F : Frames G} {S : Stage} {j μ B : ℕ} : 1 ≤ overheadAt H F S j μ B := by
  have h := sum_nonneg (fun i (_:i∈ Finset.range (j+1)) => (zero_le_one.trans (lens_ge H F i)))
  change 0 ≤ upper H F j at h
  have he := S.columns_ge
  have hc := S.price_pos
  apply one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) (Real.one_le_exp (by linarith)))
    (le_add_of_nonneg_right (by unfold siteFactor; positivity))

def logBudget (S : Stage) (B : ℕ) := (((4*B+2:ℝ)^S.power)^S.order)*book S.power S.order

lemma logBudget_one {S : Stage} {B : ℕ} : 1≤logBudget S B :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_pow₀ (by have : (0:ℝ) ≤ B := (by positivity); linarith)))
    ((exp_absorbs _ _ zero_lt_one).choose_spec.1)

def bank (H : Hol G) (F : Frames G) (P : Stage) (j μ B : ℕ) :=
    256*((B+B+1:ℕ):ℝ)^4*logBudget P B * overheadAt H F P j μ B

lemma bank_pos {H : Hol G} {F : Frames G} {P : Stage} {j μ B : ℕ} : 0 < bank H F P j μ B := by
  unfold bank; have := logBudget_one (S:=P) (B:=B); have := overheadAt_one (H:=H) (F:=F) (S:=P) (j:=j) (B:=B) (μ:=μ); positivity

def ticket (P Q : Stage) (r B μ k : ℕ) := (1+μ*siteFactor B)*pad (P.supportExponent+7) Q.supportExponent r k

def extra (t : Tariff) : Tariff := { t with power := fun i => t.power i + 1 }

abbrev tollCap (s : Scope) (C : Family G) (m : ℕ) :=
    (bank C.params C.labels (C.path.levels.params m) (year C m) (s.markers (year C m)) (point C m).B)⁻¹

structure Certified (s : Scope) (loss : Tariff) (d : ℕ → ℕ) (ζ : ℕ → ℝ) (H : Hol G) (F : Frames G) (a : Levels G) : Prop where
  cost m : let i := a.clock.J m; let j := a.clock.J (m+1)
    let x := a.clock.hatBeta m; let y := a.clock.hatBeta (m+1); let B := a.clock.coverSize m
    let ε := (bank H F (a.params m) i (s.markers i) B)⁻¹
    ticket (a.params m) (a.params (m+1)) (s.expand j) B (s.markers i) (d j) * fee loss j y / fee (extra loss) j y ≤ ε/2 ∧
      x^(-ζ j) ≤ ε/2

section Numerics

private def Soft (f : ℝ → ℝ) := ∃ C : ℝ, 0<C ∧ ∃ n : ℕ, ∀ᶠ x in atTop, 0 ≤ f x ∧ f x ≤ C*(Real.log x)^n
variable {f g : ℝ → ℝ}

private lemma Soft.constant {a : ℝ} (ha : 0 ≤ a) : Soft fun _ => a :=
    ⟨a+1,by linarith,0,Eventually.of_forall fun _ => ⟨ha,by simp⟩⟩

private lemma Soft.sum (he : Soft f) (hh : Soft g) : Soft fun x => f x+g x := by
  obtain ⟨C,hC,n,hn⟩ := he; obtain ⟨D,hD,m,hm⟩ := hh
  refine ⟨C+D,by linarith,n+m,?_⟩; filter_upwards [hn,hm,Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hn hm hx
  refine ⟨by linarith,?_⟩; rw [add_mul]; apply (add_le_add hn.2 hm.2).trans; gcongr <;> omega

private lemma Soft.prod (he : Soft f) (hh : Soft g) : Soft fun x => f x*g x := by
  obtain ⟨C,hC,n,hn⟩ := he; obtain ⟨D,hD,m,hm⟩ := hh
  refine ⟨C*D,mul_pos hC hD,n+m,?_⟩; filter_upwards [hn,hm] with x hn hm
  exact ⟨mul_nonneg hn.1 hm.1,(mul_le_mul hn.2 hm.2 hm.1 (hn.1.trans hn.2)).trans_eq (by rw [pow_add]; ring)⟩

private lemma Soft.pow (he : Soft f) (n : ℕ) : Soft fun x => f x^n := by
  induction n with
  | zero => simpa using! Soft.constant zero_le_one
  | succ n ih => simpa only [pow_succ] using ih.prod he

private lemma baseSoft : Soft fun x => (Stock.scaleB x:ℝ) := by
  refine ⟨2,by positivity,2,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
  exact ⟨by positivity,(Nat.ceil_lt_add_one (sq_nonneg _)).le.trans (by nlinarith)⟩

private lemma Soft.pays {a : ℝ} (h : Soft f) (ha : 0<a) : ∀ᶠ x : ℝ in atTop, f x ≤ x^a := by
  obtain ⟨C,hC,n,he⟩ := h
  have ht := (isLittleO_log_rpow_rpow_atTop (n:ℝ) ha).const_mul_left C |>.def zero_lt_one
  filter_upwards [he,ht,eventually_gt_atTop (1:ℝ)] with i hi hx he
  exact hi.2.trans ((Real.le_norm_self _).trans (by simpa [Real.norm_of_nonneg (le_of_lt (Real.rpow_pos_of_pos (zero_lt_one.trans he) _))] using hx))

private lemma sitesSoft : Soft fun x => siteFactor (Stock.scaleB x) := ((Soft.constant (Real.exp_pos _).le).prod
    (((Soft.constant (by positivity)).prod (((Soft.constant (by positivity)).prod baseSoft).sum (Soft.constant (by positivity)))).pow _))

private lemma logSoft (P : Stage) : Soft fun x => logBudget P (Stock.scaleB x) := by
  have he : 1≤book P.power P.order := (exp_absorbs _ _ zero_lt_one).choose_spec.1
  exact (((((Soft.constant (by positivity)).prod baseSoft).sum (Soft.constant (by positivity))).pow _).pow _).prod
    (Soft.constant (zero_le_one.trans he))

private lemma bankSoft (H : Hol G) (F : Frames G) (P : Stage) (i μ : ℕ) : Soft fun x => bank H F P i μ (Stock.scaleB x) := by
  have h := P.columns_ge
  have hu := sum_nonneg (fun j (_:j∈ Finset.range (i+1)) => (zero_le_one.trans (lens_ge H F j)))
  change 0 ≤ upper H F i at hu
  have hi : Soft fun x => overheadAt H F P i μ (Stock.scaleB x) :=
    (Soft.constant (by positivity)).prod ((Soft.constant zero_le_one).sum ((Soft.constant (by positivity)).prod sitesSoft))
  unfold bank; push_cast
  exact (((Soft.constant (by positivity)).prod (((baseSoft.sum baseSoft).sum (Soft.constant zero_le_one)).pow _)).prod (logSoft _)).prod hi



def post (k : ℕ) (c : ℝ) (x : ℝ) := c*(1 + (Stock.scaleB x:ℝ) + YM.Vac.Numbers.P x)^k



private lemma funds_late (H : Hol G) (F : Frames G) (s : Scope) (P Q : Stage) (k i j : ℕ)
    (t : Tariff) {z : ℝ} (hz : 0 < z) : ∀ᶠ x : ℝ in atTop, ∀ y ≥ x,
    let B := Stock.scaleB x; let μ := s.markers i
    let ε := (bank H F P i μ B)⁻¹
    ticket P Q (s.expand j) B μ k * fee t j y / fee (extra t) j y ≤ ε/2 ∧ x^(-z) ≤ ε/2 := by
  let A := fun x => ticket P Q (s.expand j) (Stock.scaleB x) (s.markers i) k
  have ht : Soft A := by
    have hc := P.price_pos
    have he := pad_ge (r:=s.expand j) (A:=Q.supportExponent) (k:=k) (show 0 ≤ P.supportExponent+7 by linarith)
    exact ((Soft.constant zero_le_one).sum ((Soft.constant (by positivity)).prod sitesSoft)).prod (Soft.constant (zero_le_one.trans he))
  let Z := fun x => bank H F P i (s.markers i) (Stock.scaleB x)
  have he : Soft fun x => 2*Z x := (Soft.constant (by positivity)).prod (bankSoft ..)
  filter_upwards [(ht.prod he).pays zero_lt_one,he.pays hz,eventually_gt_atTop (0:ℝ)] with x h₁ h₂ h₃ y hy
  change A x * fee t j y / fee (extra t) j y ≤ (Z x)⁻¹/2 ∧ x^(-z) ≤ (Z x)⁻¹/2
  have hw : 0 < Z x := bank_pos
  have hg : 0 < t.factor j := zero_lt_one.trans_le (t.factor_ge _)
  constructor
  · have : A x * fee t j y / fee (extra t) j y = A x / y := by have := h₃.trans_le hy; unfold fee extra; dsimp only; rw [pow_succ]; field_simp
    rw [this, Real.rpow_one] at *; apply (div_le_iff₀ (by linarith)).mpr
    field_simp; linarith
  rw [Real.rpow_neg h₃.le]; have hp := Real.rpow_pos_of_pos h₃ z
  field_simp; linarith

-- `W'` here only carries extra numerical thresholds. Follow by `pricing`
-- which keeps them. Other bids of V are exposed and retained by the combined
-- pricing lemma below; no assumption of a physical solution.
private lemma precharge (H : Hol G) (F : Frames G) (h : G.Simple) (s : Scope) {p : Sheet G} {D : Rolls p} {T : Protection D}
    (V : Delays T) (t : Tariff) (d : ℕ→ℕ) (ζ : ℕ→ℝ) (hζ : ∀ j, 0 < ζ j) : ∃ W' : Delays T,
      V.betaEntry ≤ W'.betaEntry ∧ W'.scaleEntry=V.scaleEntry ∧ W'.shells=V.shells ∧ W'.growth=V.growth ∧
      ∀ W : Delays T,W'.betaEntry ≤ W.betaEntry → ∀ (Y : Bar W) (I : Wait Y) (a : Levels G), Paid I a →
        Certified s t d ζ H F a := by
  choose b hb using fun i j => eventually_atTop.mp (funds_late H F s (p.profile i) (p.profile j) (d j) i j t (hζ j))
  let W' := { V with betaEntry := fun j => max (V.betaEntry j) (max (b j j) (b (j-1) j)) : Delays T }
  refine ⟨W',fun _ => le_max_left ..,rfl,rfl,rfl,fun W hW Y I a ha => ⟨fun m => ?_⟩⟩
  let J := a.clock.J
  have H₁ := a.fits.stepSlow m; have H₂ := a.fits.mono m.le_succ; change J (m+1) ≤ J m + 1 at H₁; change J m ≤ J (m+1) at H₂
  have ht : b (J m) (J (m+1)) ≤ W'.betaEntry (J (m+1)) := by
    unfold W'; dsimp only; apply le_max_of_le_right
    rcases H₂.eq_or_lt with hh|hh
    · rw [hh]; exact le_max_left ..
    rw [show J m=J (m+1)-1 by omega]; exact le_max_right ..
  have hy : a.clock.hatBeta m ≤ a.clock.hatBeta (m+1) := by
    unfold Calendar.hatBeta; rw [Schedule.scale_succ]; gcongr
    · exact (Gauge.slopeConstant_pos h).le
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (a.S.block m).property : 1≤ ((a.S.block m).val:ℝ)))
  simp only [Levels.params,Calendar.params,ha.stage]; apply hb (J m) (J (m+1)) _ (ht.trans ((hW _).trans (ha.pays m))) _ hy

/-- Extra thresholds for the optional primitive system below. Raw remains
an analytic question. This does not use any `Family`; choose the exact
parameters H F T in advance (or prices for the same), not another set when
creating the vacuum and fitting labels. In this example raise Tariff once for
ALL applications, after the one-step projected-vertex loss `loss` supplied
post-L; BEFORE commissioning the actual trajectories. -/
theorem price (hG : G.Simple) (s : Scope) (H : Hol G) (F : Frames G) (T : Sections F) (p : Sheet G) (K : MapPrices)
    (hfact : ∀ j : ℕ,((p.profile j).order.factorial:ℝ) ≤ (p.profile j).columns) :
    ∃ k : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ i,k i ≤ n i) → ∀ D : Rolls {p with floorL := n},
    ∀ (loss : Tariff) (d : ℕ→ℕ) (ζ : ℕ→ℝ), (∀ j,0 < ζ j) →
    ∀ m ≥ (0:ℝ), ∀ Θ : Protection D, ∀ V : Delays Θ, ∃ W : Delays Θ,
      W.shells=V.shells ∧ W.growth=V.growth ∧ V.scaleEntry ≤ W.scaleEntry ∧ V.betaEntry ≤ W.betaEntry ∧
        ∃ U : ℕ → ℕ → ℝ, Testing.Ringing K U W ∧ (∀ i j,U i j ≥ m) ∧
        ∀ (Y : Bar W) (I : Wait Y) (a : Levels G), Paid I a → Prepared s (extra loss) T a ∧ Certified s loss d ζ H F a := by
  obtain ⟨k,hk⟩ := pricing s T hG p K hfact
  refine ⟨k,fun n hn D loss d ζ hζ m hm Θ V => ?_⟩
  obtain ⟨W',he,h1,h2,h3,hw⟩ := precharge H F hG s V loss d ζ hζ
  obtain ⟨W',hh,hg,ht,h₄,U,hU,hu,h₅⟩ := hk n hn D (extra loss) m hm Θ W'
  exact ⟨W',hh.trans h2,hg.trans h3,h1 ▸ ht,he.trans h₄,U,hU,hu,fun Y I a h => ⟨h₅ Y I a h,hw _ h₄ Y I a h⟩⟩

end Numerics
end YM.Extra.Multi.System
