import YM.Push.CORRECTED_COLUMNS.Program
/-!
# Purchasing the last-torus order of magnitude

Pay from the indicated restarted Leg with hats on the GIVEN levels/costs.
No power replaced in the limit. Prove numerical feasibility of these gates,
including after summing over the number of possible *slots per test*, not
indices in full array. They can also be obtained for the untouched path
(γ=β and old Rep) without restart. No suggestion that *marked* estimates
work at the old thresholds (E changes thresholds for a reason).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Last
open Set Function Filter Lattice Wilson MeasureTheory RG RG.Supply
open Cells Overlay
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev rate (P : Stage) := P.clip.linear/16
def vacancy (G : Gauge) (P : Stage) (m : ℕ) (x : ℝ) :=
  let A := P.paths
  let l := rate P
  2*(1+(8*A+1))+Fintype.card PlaqAxes*(4*l)+1+(m:ℝ)*x+
    2*(Fintype.card PlaqAxes*(P.clip.direct+A^2)) + 3*Real.log (multiplier G l)

structure Affords (G : Gauge) (P : Stage) (m : ℕ) (x η β : ℝ) : Prop where
  rough : 1≤Real.log β
  power₁ : β*(YM.Vac.Numbers.theta β)^3≤1 ∧ β*(YM.Vac.Numbers.theta β)^4≤1
  power₂ : ∀ v : ℝ, v≤1 → 2*(YM.Vac.Numbers.P β)^v * (YM.Vac.Numbers.theta β)^2 ≤ 1
  overhead : vacancy G P m x ≤ η*Real.log (Zone.Demand.cal β)

lemma progress (G : Gauge) (P : Stage) (m : ℕ) (x η : ℝ) (hη : 0 < η) :
    ∀ᶠ β : ℝ in atTop, Affords G P m x η β := by
  have he : Tendsto (fun β => η*Real.log (Zone.Demand.cal β)) atTop atTop := by
    simp_rw [Zone.Demand.cal,Real.log_exp]
    exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).const_mul_atTop hη
  filter_upwards [he.eventually_ge_atTop (vacancy G P m x), YM.Vac.Numbers.uniform_loop,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with β hb he hx
  exact ⟨hx,⟨he.2.1,he.2.2.1⟩,he.2.2.2,hb⟩

section Price
variable {p : Sheet G} {w : Rolls p} {T : Protection w}
-- Includes post-L anticipations in `v`; enlarge at the same fixed stage as needed.
def OnPage (U : Delays T) (η : ℝ) (m : ℕ) (v : ℕ → ℝ) :=
    ∀ j : ℕ, ∀ β : ℝ, U.betaEntry j ≤ β → Affords G (p.profile j) m (v j) η β
lemma delay (U : Delays T) (m : ℕ) (v : ℕ → ℝ) {η : ℝ} (hη : 0<η) :
    ∃ W : Delays T, (∀ j, U.betaEntry j ≤ W.betaEntry j) ∧
      W.scaleEntry=U.scaleEntry ∧ W.shells=U.shells ∧ W.growth=U.growth ∧ OnPage W η m v := by
  choose b H using fun i => eventually_atTop.1 (progress G (p.profile i) m (v i) η hη)
  exact ⟨{ U with betaEntry := fun i => max (U.betaEntry i) (b i) },fun i => le_max_left ..,
    rfl, rfl,rfl,fun j β h => H j _ ((le_max_right ..).trans h)⟩
end Price

section Fees
variable (A : Levels G)

lemma sPos (m) : 0<A.clock.hatCoupling m := inv_pos.mpr <| Real.sqrt_pos.2 <|
    lt_trans zero_lt_one (A.fits.delayed _)
lemma sSq (m) : A.clock.hatBeta m*A.clock.hatCoupling m^2=1 := by
  unfold Calendar.hatCoupling; rw [inv_pow, Real.sq_sqrt (zero_le_one.trans (A.fits.delayed m).le), mul_inv_cancel₀
    (ne_of_gt (lt_trans zero_lt_one (A.fits.delayed _)))]
lemma sLe (m) : A.clock.hatCoupling m ≤ A.clock.threshold m :=
  le_mul_of_one_le_right (sPos A m).le (Real.one_le_exp (sq_nonneg _))
lemma aperture (m) : A.clock.hatCoupling m ≤ 1 := (sLe A m).trans (A.fits.smallField m)
lemma band_le (h : G.Simple) : Monotone A.clock.hatBeta := by
  apply monotone_nat_of_le_succ
  intro i; unfold Calendar.hatBeta; rw [Schedule.scale_succ]; gcongr
  · exact (G.slopeConstant_pos h).le
  exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (show 1 ≤ (A.S.block i).val from (A.S.block i).property)))
lemma from_page (v : ℕ → ℝ) (m i : ℕ) {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} {X : Bar W}
    {U : Wait X} (h : G.Simple) (hp : Paid U A) (η : ℝ) (H : OnPage W η m v) :
    Affords G (A.params i) m (v (A.clock.J i)) η (A.clock.hatBeta i) := by
  change Affords G (A.clock.stage _) m _ _ _
  rw [hp.stage]
  apply H
  cases i with
  | zero =>
    rw [hp.firstZero]
    have he := hp.pays 0; rw [hp.firstOne] at he; exact he
  | succ i => exact (hp.pays i).trans (band_le A h (Nat.le_succ i))
end Fees

section Scales
variable {C : Family G} {N p m : ℕ}

-- Input bounds at the new coupling. Width and A use SAME stage cost.
structure Comparable (C : Family G) (R : Rep G (C.side m p)) (κ : ℝ) : Prop where
  cap1 : (lvl C).clock.hatBeta m/4 ≤ R.beta
  cap2 : R.beta≤4*(lvl C).clock.hatBeta m
  clip : R.clip=((lvl C).params m).clip
  low : (lvl C).clock.hatCoupling m≤ R.p.threshold
  high : R.p.threshold ≤ ((lvl C).budget m).threshold
  terms : R.Lawful ((lvl C).params m).width ((lvl C).params m).paths ((lvl C).clock.loopCap m) ((lvl C).clock.allowance m) κ
  budget : κ ≤ 1

variable {R : Rep G (C.side m p)}


def natural (h : C.Makes) (r k N p : ℕ) : Wire C r k N p :=
    ⟨fun i => C.path.β N p i,fun _ _ _ => rfl, fun _ _ hn => Overlay.beta_positive h.wilson hn⟩
lemma same (h : C.Makes) {m : ℕ} (B k N p : ℕ) (hm : m ≤ N) :
    (natural h B k N p).vacuum m hm=(C.path.rep N p m).eval := by
  unfold Wire.vacuum
  induction hm using Nat.decreasingInduction with
  | self => rw [Wire.own,(h.wilson.starts ..).2]
  | of_succ i hi ih => rw [Wire.pushes _ _ _ hi,ih,(h.wilson.steps _ _ _ hi).1]; rfl

variable {κ : ℝ} (h : Comparable C (m:=m) R κ)

lemma Comparable.trueL {k} (h : Comparable C (m:=m) R κ) (B : Wire C m k N p) (hm : m≤N)
    (ht : R.eval = B.vacuum m hm) (hc : R.beta=B.cost m) :
    let A := lvl C
    Endpoint.Resolved B hm R (A.clock.hatCoupling m) (rate (A.params m)) (A.params m).width (A.params m).paths (A.clock.loopCap m)
      (A.clock.allowance m) κ := by
  intro A
  have hp := (A.params m).clip.tail_pos
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.cap1 hp.le) (sq_nonneg (A.clock.hatCoupling m))
  refine ⟨ht,h.terms,hc,h.low,sPos A m,?_⟩
  rw [h.clip]
  apply le_trans ?_ he
  apply le_of_eq
  have hh := sSq A m
  change 4*((A.params m).clip.linear/16) = A.clock.hatBeta m/4 * _ * A.clock.hatCoupling m^2
  linear_combination (norm:=ring) -((A.params m).clip.linear/4)*hh

lemma Comparable.invoiced (h : Comparable C (m:=m) R κ) {x η : ℝ} {j : ℕ}
    (hq : Affords G ((lvl C).params m) j x η ((lvl C).clock.hatBeta m)) {u b c : ℝ} {i : ℕ}
    (hi : i≤j) (hi' : u+b+c ≤ x) (hx : 0 ≤ x) :
    let L := (lvl C).clock
    let A := (lvl C).params m
    Endpoint.underPrice (C:=C) (r:=m) (p:=p) R (L.hatCoupling m) A.paths (L.loopCap m) (L.allowance m)+Endpoint.outerPrice R
      (rate A) A.paths (L.loopCap m) (L.allowance m) κ u b c i + 3*Real.log (multiplier G (rate A)) ≤ η * Real.log (L.monitor m) := by
  intro L A
  have he := (lvl C).fits
  let s := L.hatBeta m
  let t := L.threshold m
  have hp : 1<s := he.delayed m
  have h₁ : R.p.threshold≤ t := h.high
  have h₂ : 0 < R.p.threshold := R.p.threshold_pos
  have hs : 0 < s := lt_trans zero_lt_one hp
  have hl : R.beta ≤ 4*s := h.cap2
  have hu := (lvl C).fits.thetaRange m
  have hv := A.paths_pos
  have hE : PathData.loopsPrice R.p R.beta A.paths (L.loopCap m) ≤ 8*A.paths+1 := by
    unfold PathData.loopsPrice
    apply add_le_add
    · have he : R.beta*(A.paths*R.p.threshold^3+A.paths*R.p.threshold^4) ≤ 4*s*(A.paths*t^3+A.paths*t^4) := by gcongr
      apply he.trans
      have ha : s*t^3≤1 := hq.power₁.1
      have hb : s*t^4≤1 := hq.power₁.2
      -- 3 and 4 natural powers (guard)
      linarith only [mul_le_mul_of_nonneg_left ha hv.le,mul_le_mul_of_nonneg_left hb hv.le]
    have ht : L.theta (L.J m) ≤ 1 := hu.2.trans (inv_le_one_of_one_le₀
      (show (1:ℝ) ≤ L.J m from Nat.one_le_cast.mpr (Nat.le_trans (by norm_num) (L.adm _))))
    have hw : L.loopCap m*t^2≤1 := hq.power₂ _ ht
    apply le_trans ?_ hw
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₂.le h₁ _) (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hX : L.allowance m≤1 := Real.rpow_le_one (sPos _ _|>.le) (aperture (lvl C) m) (by norm_num)
  have hh := add_le_add hX hE
  have hV : R.clip=A.clip := h.clip
  have hY : R.beta*baseBudget R.clip A.paths (L.hatCoupling m) ≤ 2*(Fintype.card PlaqAxes*(A.clip.direct+A.paths^2)) := by
    rw [hV]
    have hD : 0 ≤ baseBudget A.clip A.paths (L.hatCoupling m) := by
      unfold baseBudget; have := A.clip.quadratic_pos; positivity
    apply (mul_le_mul_of_nonneg_right hl hD).trans_eq
    unfold baseBudget
    linear_combination (norm:=ring)
      2*(Fintype.card PlaqAxes:ℝ)*(A.clip.direct+A.paths^2)*sSq (lvl C) m
  apply le_trans ?_ hq.overhead
  unfold Endpoint.outerPrice Endpoint.underPrice vacancy
  dsimp only
  change R.exCost A.paths (L.loopCap m) (L.allowance m)+_+(_+_+κ+i*_) +_≤
    2*(1+(8*A.paths+1))+Fintype.card PlaqAxes*(4*rate A)+_+_+2*((Fintype.card PlaqAxes:ℝ)*_)+3*Real.log (multiplier G _)
  have hv : R.exCost A.paths (L.loopCap m) (L.allowance m)≤1+(8*A.paths+1) := hh
  have hN : (i:ℝ)*(u+b+c) ≤ (j:ℝ)*x := (mul_le_mul_of_nonneg_left hi' (by positivity)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hx)
  linarith only [hY,h.budget,hN,hv]
end Scales

section Clients
variable {C : Family G}

def prices (B : Series C) (h : G.Simple) (γ η : ℝ) (hη : 0<η) (hγ : η < γ) : Prices :=
  let p k := (lvl C).clock.monitor (B.depth k)
  let A k := (lvl C).params (B.side k)
  let hp (k : ℕ) : 1 ≤ p k := Real.one_le_exp (sq_nonneg _)
  let V k := (lvl C).clock.hatCoupling (B.side k)
  { since := V
    rate := fun k => rate (A k)
    Q := fun k => η*Real.log (p k)
    W := fun k => p k ^ γ
    tiny k := sPos _ _
    little k := aperture ..
    weight k := Real.one_le_rpow (hp k) (by linarith)
    margin k := div_pos (A k|>.clip.tail_pos) (by norm_num)
    runs := by
      have he : Tendsto p atTop atTop := (Zone.rising (lvl C) h).comp B.depth.cofinal
      have ht : Tendsto (fun k => (η-γ)*Real.log (p k)) atTop atBot :=
        (Real.tendsto_log_atTop.comp he).const_mul_atTop_of_neg (by linarith : η-γ<0)
      refine (Real.tendsto_exp_atBot.comp ht).congr fun k => ?_
      dsimp only [comp_apply]
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one (hp k)), ← Real.exp_sub]; congr 1; ring }

lemma dimension {d : ℕ} {S : Table C.book} (X : Columns C S d) (i : Row X) : Fintype.card (Mark X i) ≤ 2 := by
  dsimp only [Mark]; rw [Fintype.card_fin]; exact Nat.add_le_add_right (X.row i).cap 1

/-- Marked producer can now try to pay just the last local **atom** caps
(here even amounts of arbitrary cost per stage α>=0), with `R` picked to
be either restarted or original.

All before integration.

Width input controls
`clock.loopCap r` also if using restart.

That cap is not assumed small versus
check powers (cf.

Even if exponent preservation only proven at the actual trajectory one may
use this as an alternative attack (not claiming feasible). -/
theorem page {S : Table C.book} {d : ℕ} {X : Columns C S d} (Y : Tests X)
    {q : Sheet G} {w : Rolls q} {T : Protection w} {W : Delays T} {v : Bar W} {U : Wait v}
    (hp : Paid U (lvl C)) (f : Extraction.Order) {α} {γ η : ℝ} (h : G.Simple) (hη : 0<η) (hγ : η < γ)
    (ha : OnPage W η 2 α) (hα : ∀ j,0≤α j)
    (he : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ∀ᶠ i : ℕ in atTop, ∀ c, ‖Y.tune k (f.mesh i) p c‖ ≤ D)
    (hh : ∀ k, f.late fun N p =>
      let r := Y.B.side k
      let m := Y.B.depth k
      let L := (lvl C).clock
      ∃ (hn : m≤N) (B : Wire C r m N p) (R : Rep G (C.side r p)) (κ : ℝ), Comparable C (m:=r) R κ ∧
        R.eval=B.vacuum r ((Y.B.side_le k).trans hn) ∧ R.beta=B.cost r ∧ ∀ (i : Row X) (c),
        ∃ (M : Bands (Marks.all (Site (C.side r p) × Mark X i)) R), ∃ u b C',
          u+b+C' ≤ α (L.J r) ∧ Endpoint.Value M (fun _ => L.monitor m ^ γ) u b C' ∧
          (∀ z K, Marks.part (M.density K) z=B.term ((Y.B.side_le k).trans hn) (Y.pattern k N p i c) z K) ∧
          ∀ t, M.origins t=t.1) : Tests.Offer Y (prices Y.B h γ η hη hγ) f := by
  refine ⟨he,fun k => ?_⟩
  apply Filter.Eventually.mono (hh k); intro i hi; apply hi.mono
  rintro N ⟨hn,B,R,j,hc,hv,hx,hB⟩
  let r := Y.B.side k
  let L := lvl C
  let Q := L.clock
  refine ⟨hn,B,R,Q.hatCoupling r,(L.params r).width,(L.params r).paths,Q.loopCap r,Q.allowance r,j,
    le_rfl, hc.trueL B ((Y.B.side_le k).trans hn) hv hx,fun i t => ?_⟩
  obtain ⟨M,u,b,C',he,H,hM,hp'⟩ := hB i t
  have hQ := from_page L α 2 r h hp η ha
  refine ⟨M,u,b,C',⟨H,hM,?_⟩,hp'⟩
  refine (hc.invoiced hQ (dimension X i) he (hα _)).trans ?_
  let s := Y.B.depth k
  change η*Real.log (Q.monitor r) ≤ η*Real.log (Q.monitor s)
  have hw : Q.hatBeta r ≤ Q.hatBeta s := band_le _ h (Y.B.side_le k)
  have hm : 1 < Q.hatBeta r := L.fits.delayed _
  have hg : 1 ≤ Real.log (Q.hatBeta r) := hQ.rough
  unfold Calendar.monitor; rw [Real.log_exp,Real.log_exp]
  gcongr; exact Real.log_nonneg hg
end Clients
end YM.Push.Corrected.Last
