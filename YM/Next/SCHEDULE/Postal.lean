import YM.Next.SCHEDULE.Post

/-!
# Some further source scheduling gates

JLTH, Jenv/Jmixcl. Keep PRE-vs-POST distinction even
for adjacent powers outside a weak stretch. Test that actual `width`
schedule in Mix has enough fiscal room for provisional mark radii AND
successor radii on same supports (ancestor progress ∀ steps). Supports and
activeness, fStep responses, translated families etc NOT inferred. `Radial`
is a final bill (accepted I02 can spend factorial on it); here we do not
shrink by a factorial in *each* handoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Pressure Precision Lattice Source Clock Instrument
open scoped Topology BigOperators

/-- Provisional radius
`width fine / (L^j H*(7*P x)^D)`, exposing those post-L powers as one
post-L bill (may choose ANY fixed such powers before delay).

Covers use e.g.

`(1+B+p+Λ)^D`, not g powers from Λ ambiguously hidden.

Requires r>0
(pre-L exponents should include it, e.g.

`e.extra` positive).

Keep slack
in support-exchange payment for recursive transfers needing smallness, 128
versus I02's 64.

`log^+` expressed with same H stamps all t. -/
def inflation (A : Postage) (x : ℝ) := A.H * (7*plain.P x)^A.D

structure MarkGate (r L C C' : ℝ) (A : Postage) (k j : ℕ) (x y : ℝ) : Prop where
  quote : C'^ (2:ℕ)/C ≤ Real.exp (r*(Clock.cover x)/256)
  burn : inflation A x*Real.exp (-(r/128)*(Clock.cover x)) ≤ (gap x)^k/8
  next (b : ℕ) : b ≤ k → (gap x/gap y)^b*(C'^ (2:ℕ)/C)*L^j*inflation A x ≤ Real.exp (r*(Clock.cover x)/128)
  extra (θ : ℝ) : 0 < θ → θ ≤ 1 → A.bundle plain θ x y ≤ inflation A x

open Real in
lemma MarkGate.late (r L C C' : ℝ) (hr : 0 < r) (hL : 0 < L) (hc : 0<C) (A : Postage) (c : ℝ) (k j : ℕ) :
    ∀ᶠ x in atTop, MarkGate r L C C' A k j x (x+c) := by
  have hh : Tendsto (fun x => inflation A x*gap x) atTop (𝓝 0) := by
    simpa [inflation,P,plain,mul_pow,mul_assoc] using (light 2 (A.D:ℝ) 1 (by norm_num)).const_mul (A.H*7^A.D)
  have hz (k : ℕ) : Tendsto (fun x => (inflation A x*exp (-(r/128)*(Clock.cover x)))/(gap x)^k) atTop (𝓝 0) := by
    have hw := hh.mul (shadows (-((k:ℝ)+1)) (r/128) (by positivity))
    rw [mul_zero] at hw
    apply hw.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hp:=gp hx
    rw [Real.rpow_neg hp.le,Real.rpow_add hp]; simp only [Real.rpow_natCast,rpow_one]; field_simp
  have hw := (hz 0).const_mul (2^k*(C'^ (2:ℕ)/C)*L^j)
  simp only [mul_zero,pow_zero,div_one] at hw
  have ht : Tendsto (fun x : ℝ => exp (r*(Clock.cover x)/256)) atTop atTop := by
    apply tendsto_exp_atTop.comp
    have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp counting
    simp_rw [div_eq_mul_inv]
    exact (hh.const_mul_atTop hr).atTop_mul_const (by norm_num)
  have hA : Similar gap := by simpa using similar_gap_power 1
  have hP : Similar plain.P := by simpa only [Instrument.P,Instrument.plain,Real.rpow_one] using similar_watch_power 2 1
  filter_upwards [ht.eventually_ge_atTop (C'^ (2:ℕ)/C),
    (hz k).eventually (ge_mem_nhds (show 0 < (1/8:ℝ) by norm_num)),hw.eventually (ge_mem_nhds zero_lt_one),
    hA _ (one_lt_two), hP _ one_lt_two, just_near c, advance (eventually_gt_atTop (0:ℝ)),
    (ceiling_cheaper 2 1 1 one_lt_two zero_lt_one).eventually (ge_mem_nhds zero_lt_one),
    advance ((growing (d:=2) (by norm_num)).eventually_ge_atTop 1)] with x ht he hs hv hp hc0 hx hM hu
  let y:=x+c
  have hg0:=gp (hx _ (Clock.same x)); have hg:=gp (hx _ hc0)
  have hh0 := (div_le_iff₀ (pow_pos hg0 k)).1 (show _ / (gap x)^k ≤ 1/8 from he)
  have hHP := hv _ _ (Clock.same x) hc0
  have hI : 0 ≤ inflation A x := by unfold inflation; have hh := lt_of_lt_of_le zero_lt_one A.h_ge; have hp' : 0<plain.P x := wp _ _; positivity
  refine ⟨ht,by linarith,fun b hb => ?_,fun θ hxθ hθ => ?_⟩
  · calc
      _ ≤ 2^k*(C'^ (2:ℕ)/C)*L^j*inflation A x := by
        gcongr; exact (pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hg).2 hHP) b).trans (pow_le_pow_right₀ (by norm_num) hb)
      _ ≤ _ := by
        have he : exp (-(r/128)*(Clock.cover x)) = (exp (r*(Clock.cover x)/128))⁻¹ := by
          rw [← exp_neg]; congr 1; ring
        change 2^k*(C'^ (2:ℕ)/C)*L^j*(inflation A x*_) ≤ 1 at hs
        rw [he,← mul_assoc,← div_eq_mul_inv] at hs; simpa using (div_le_iff₀ (exp_pos _)).1 hs
  unfold Postage.bundle inflation
  let Y:=plain.P
  have HH : LevelCost θ y ≤ Y y := by
    have hR : 1 ≤ Y y := hu _ hc0
    exact (Real.rpow_le_rpow_of_exponent_le hR hθ).trans_eq (Real.rpow_one _)
  have hhY : 0 < LevelCost θ (x+c) := Real.rpow_pos_of_pos (wp _ _) _
  have hpY : 0 < Y x:=wp _ _; have hsY:0<Y (x+c):=wp _ _
  have hm : 1+(plain.body x:ℝ) ≤ Y x := by
    simp only [rpow_one,pow_one] at hM
    simpa only [Instrument.body,Instrument.P,Y,plain,pow_one,one_mul] using (div_le_iff₀ hpY).1 hM
  have hxY : Y y ≤ 2*Y x := hp _ _ hc0 (Clock.same x)
  change _*(1+_+Y _+_)^_ ≤ _*(7*Y x)^_
  apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one A.h_ge)
  apply pow_le_pow_left₀ (by positivity); unfold y at *; linarith

variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D}

/-- Activate if actually requested reserve in pre shape. `k` maximum k in
use at stage, arbitrary itinerary. -/
def Marked (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (k : ℕ → ℕ) (V : Delays Θ) :=
    ∀ j i, Adj j i → 0 < (e j i).extra → ∀ x ≥ V.betaEntry j,
      let L:ℝ := (D.L j).val
      MarkGate (e j i).extra L (s.melt q i).columns (s.melt q j).columns (F j i) (k j) j x
        (x+G.slopeConstant*Real.log L)

lemma Marked.raise (F) (k : ℕ → ℕ) (V : Delays Θ) (e) : ∃ W : Delays Θ, Boost V W ∧ Marked e F k W := by
  let U j : ℝ := (D.L j).val
  have hx j i : ∀ᶠ x in atTop, 0 < (e j i).extra → MarkGate (e j i).extra (U j) (s.melt q i).columns (s.melt q j).columns (F j i) (k j) j x (x+G.slopeConstant*Real.log (U j)) := by
    by_cases ht : 0 < (e j i).extra
    · have he : 0 < U j := by unfold U; exact_mod_cast (D.L j).property
      exact (MarkGate.late _ _ _ _ ht he (lt_of_lt_of_le zero_lt_one (s.melt q i).columns_ge) _ _ (k j) j).mono fun _ h _ => h
    exact Eventually.of_forall fun _ h => (ht h).elim
  choose c hc using fun i => eventually_atTop.1 <| (hx i i).and (hx i (i-1))
  let W : Delays Θ := { V with betaEntry := fun i => max (V.betaEntry i) (c i) }
  refine ⟨W,⟨fun i => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun j i hx he b hh => ?_⟩
  have hp := hc j b (le_trans (le_max_right ..) hh)
  rcases hx.cases_back with h|h <;> subst i
  · exact hp.1 he
  exact hp.2 he

lemma Marked.carry {V W : Delays Θ} {F : ℕ → ℕ → Postage} {k} (h : Boost V W) (p : Marked e F k V) : Marked e F k W :=
    fun j i hi he b hh => p j i hi he b ((h.beta j).trans hh)

namespace Deployment
open Mix
variable {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {B : Beam K D} {F : ℕ → ℕ → Postage}





end Deployment

open Marker RG Lattice Wilson Overlay Mix Finset
variable {n : Side} {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {X : Rep G n} {Ψ : Bands R X}


namespace Deployment
variable {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G} {B : Beam K D} {F : ℕ → ℕ → Postage}






end Deployment
end YM.Next.Scheduling
