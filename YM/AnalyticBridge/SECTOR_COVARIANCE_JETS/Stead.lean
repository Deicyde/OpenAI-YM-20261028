import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Quote
import YM.Push.FREE_RESOLVENT.BlockRate
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur



set_option warningAsError false

/-! Uniform bundle price *before* inverse, real chart costs (post-L).
No stationary/exponential kernel assumptions beyond the genuine row input of
SectorChange. Counting norms later; Frobenius topology for Bundle.smooth.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost tagPrice)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ}

-- Estimate from either index's endpoint. Even covers order zero.
abbrev RatesPaid {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → Site c) (q : κ → Site c) (d : ℝ)
    (C : ℝ) (k : ℕ) (A : Directions G c → Matrix ι κ ℝ) (B : Directions G c) :=
    Bundle atom (meterMark G c d) (native c) p q A B k d C

lemma less_rates {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c} {d s t C M : ℝ}
    {l : List (Atom G c)} {A : Matrix ι κ ℝ} (h : FreeResolvent.Mark.Rates (meterMark G c d) (native c) p q l s C A)
    (he : t≤d) (ht : C ≤ M) : FreeResolvent.Mark.Rates (meterMark G c t) (native c) p q l s M A := by
  constructor; intro i; apply le_trans _ ((h.rows i).trans ht)
  apply mul_le_mul_of_nonneg_right (cheaper _ _ he)
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))
lemma less_bundle {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c} {d s t C M : ℝ}
    {A : Directions G c → Matrix ι κ ℝ} {B : Directions G c}
    (h : Bundle atom (meterMark G c d) (native c) p q A B k s C)
    (he : t≤d) (ht : C ≤ M) : Bundle atom (meterMark G c t) (native c) p q A B k s M := by
  constructor
  · exact h.smooth
  intro l hl
  exact ⟨less_rates (h.bound l hl).1 he ht, less_rates (h.bound l hl).2 he ht⟩

lemma reducePay {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c} {d s C M : ℝ}
    {A : Directions G c → Matrix ι κ ℝ} {B : Directions G c} (h : RatesPaid p q d C k A B)
    (he : s≤d) (ht : C ≤ M) {n : ℕ} (hn : n ≤ k) : RatesPaid p q s M n A B := by
  have hv := Bundle.mono (less_bundle h he ht) he le_rfl
  exact ⟨smooth_of_le hv.smooth hn,fun l hl => hv.bound l (hl.trans hn)⟩

def geography (P : Patch) (G : Gauge) (σ : ℝ) :=
  max (((Fintype.card G.ColorIndex:ℝ) * (Fintype.card (Site P.L) * Fintype.card Axis)) * Tier.wealth σ)
    (Fintype.card G.ColorIndex * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site P.L) * Tier.wealth σ)+
      Fintype.card Axis * Tier.wealth σ)))
lemma geography_nn (P : Patch) (G : Gauge) (σ : ℝ) : 0≤geography P G σ := le_max_of_le_left (mul_nonneg (by positivity) (Tier.wealth_nn _))
lemma terraced (S : StepData c f) (G : Gauge) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (σ : ℝ) (hs : 0<σ) :
    (native c).Volume (front (G:=G) A F (x:=x)) σ (geography S.patch G σ) ∧
    (native c).Volume (down (G:=G) S) σ (geography S.patch G σ) :=
  ⟨(volume_in σ hs G A F x).le (le_max_left ..),(volume_downwards σ hs S G).le (le_max_right ..)⟩

def BillBefore (G : Gauge) (p : Teller G) (P : Patch) (x C r : ℝ) (k : ℕ) (σ : ℝ) :=
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
    100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
      A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
        RatesPaid (down S) (front A F) σ C k (scroll T A F t x V) B ∧
          RatesPaid (front A F) (front A F) σ C k (pilot T A F t x V) B

lemma entry_to_paid {P : Patch} {G : Gauge} {p : Teller G} (x kC r d : ℝ) (hC : 0 ≤ kC) (hd : 0<d)
    (h : Entry x kC r P G p k (2*d)) :
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
    100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
      A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
        RatesPaid (down S) (front A F) d (geography P G d*kC) k (scroll T A F t x V) B := by
  intro c f S T hS hT hg V t A F he B hB
  let Q := scroll T A F t x V
  have hx i j := h S T hS hT hg V t A F he B hB i j
  obtain ⟨hp,hq⟩ := terraced S G A F x d hd
  have hl : Bundle atom (meterMark G c (2*d)) (native c) (down S) (front A F) Q B k d (geography P G d * kC) := by
    have hv : ContDiffAt ℝ k Q B := rectangle_smooth (fun i j => (hx i j).smooth)
    constructor
    · exact hv
    intro l hl; apply Bill.of_entry (σ:=2*d) ?_ ?_ hC
    · intro i j; rw [← entry atom _ (smooth_of_le hv hl)]
      exact (hx i j).row l hl
    · intro i j; rw [← entry atom _ (smooth_of_le hv hl)]
      exact (hx i j).col l hl
    · rw [← hS, show 2*d-d=d from by ring]; exact hp
    rw [← hS, show 2*d-d=d from by ring]; exact hq
  exact less_bundle hl (by linarith) le_rfl

/-- Produces constant/σ quoted strictly before choosing the orbit/trees and
volume, post-L. A REAL genuine Bundle currency. No flat bound on other patches
used in the pricing. -/
lemma bought (P : Patch) (G : Gauge) (p : Teller G) (hb : P.Branches p.bind G) (k : ℕ) :
    ∃ C r d : ℝ, 0≤C ∧ 0<r ∧ 0<d ∧ ∀ᶠ x : ℝ in atTop, BillBefore G p P x C r k d := by
  let σ := p.top.width
  have hs : 0 < σ := p.top.width_pos
  let z : ℝ := 1+2*k
  let d := (σ/4) / z
  have hz : 0<z := by unfold z; positivity
  have hd : 0<d := by unfold d; positivity
  have he : z*(2*d) ≤ σ/2 := by unfold d; field_simp; norm_num
  obtain ⟨C,r,hC,hr,h⟩ := entries P G p k (2*d) (by positivity) he hb
  let u : ℝ := d / (1+k)
  let M := geography P G d * C
  let Z := tagPrice 1 k M M
  have hm : 0≤M := mul_nonneg (geography_nn ..) hC
  have hu : 0<u := by unfold u; positivity
  have hx : u + k*u ≤ d := by unfold u; field_simp; simp
  have hu' : u≤d := le_trans (le_add_of_nonneg_right (by positivity)) hx
  refine ⟨max M Z,r,u,hm.trans (le_max_left ..),hr,hu,?_⟩
  filter_upwards [h] with x hh
  intro c f S T hS hT hc V t A F hA B hB
  have hy := entry_to_paid x C r d hC hd hh S T hS hT hc V t A F hA B hB
  refine ⟨reducePay hy hu' (le_max_left ..) le_rfl,?_⟩
  have ht := less_bundle hy hu' le_rfl
  exact Bundle.mono ((Bundle.transpose ht).multiply ht (position_move _ _ hu.le) hu.le le_rfl hm hm hu.le hx) le_rfl (le_max_right ..)

-- Connection Schur/Wisps vs FreeResolvent.native cost
lemma poured {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c} {d C : ℝ} {A : Matrix ι κ ℝ}
    (h : (native c).Schur p q d C A) (hp : 0 ≤ C) : Pours A p q d C := by
  refine ⟨hp,h.rows.bound,?_⟩
  intro j; simp_rw [separation_comm _ (q _)]; exact h.cols.bound j
lemma pay_pours {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c} {d C : ℝ}
    {A : Directions G c → Matrix ι κ ℝ} {B : Directions G c}
    (h : RatesPaid p q d C k A B) (hp : 0 ≤ C) : Pours (A B) p q d C := by
  have hx := Bill.reclaim (h.bound [] (by simp))
  rw [zeroth] at hx; exact poured hx hp

-- Gap TestD type + transfer
lemma debut {ι : Type} [Fintype ι] {A : Matrix ι ι ℝ} {u : ℝ} (h : Gapped A u) : FreeResolvent.Gap A u := by
  constructor; intro x
  have hx := h x; rw [sumSq_dot] at hx; exact hx
end YM.AnalyticBridge.Covariance
