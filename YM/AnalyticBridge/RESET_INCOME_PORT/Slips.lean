import YM.AnalyticBridge.RESET_INCOME_PORT.HeadGas
import YM.AnalyticBridge.RESET_INCOME_PORT.LogMotion

set_option warningAsError false

/-!
# Relative numerator tickets to quantitative `raw` log variations

At fixed V & dial pair. Needs the actual sleeve→components Balance
(BOTH d and d', includes true tag dependence etc), quote, and local
accounting test on their signed components. Expenditure is then per
label i. No comparison of two likelihood normalizations or ignoring
signed sector pieces. Nothing permits replacing the denominator by a
field-independent bound here: the test uses `flight`, with `Quote`
and the full (legitimately priced) determinants, chart ratios and
banker unchanged on dial comparison. It's okay to scale some columns to
q first and compare in those units. Report details directions of use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Finset Lattice Wilson RG Precision Exterior Tree MeasureTheory
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open SectorNext.Vacuum.ReLog LogMotion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {R : Rep G f} {V : Config G c} {κ u δ : ℝ}

private lemma integrate_chip {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ : ℝ} {s t m M : X → ℝ}
    (h : ∀ᵐ x ∂μ, Chip ρ (s x) (t x) (m x) (M x)) (hs : Integrable s μ) (ht : Integrable t μ) (hm : Integrable m μ)
    (hM : Integrable M μ) : Chip ρ (∫ x,s x ∂μ) (∫ x,t x ∂μ) (∫ x,m x ∂μ) (∫ x,M x ∂μ) := by
  have he {s t : X→ℝ} (hs : Integrable s μ) (ht : Integrable t μ) (h : ∀ᵐ x ∂μ, |s x| ≤ t x) :
      |∫ x,s x ∂μ| ≤ ∫ x,t x ∂μ := (norm_integral_le_integral_norm _).trans (integral_mono_ae hs.norm ht h)
  refine ⟨he hs hm (h.mono fun x hx=>hx.paidL),he ht hm (h.mono fun x hx=>hx.paidR),
    integral_mono_ae hm hM (h.mono fun x hx => hx.enrich),?_⟩
  rw [←integral_sub hs ht, ←integral_sub hM hm, ←integral_const_mul]; exact he (hs.sub ht) ((hM.sub hm).const_mul _) (h.mono
    fun x hx => hx.swing)

namespace HeadGas
variable (d d' : HeadGas e)

/-- Quoted first-occurrence probe. -/
def sight (q : Quote) (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices) (i : ℕ) (z : e.Sample A) :=
    Real.exp (q.assessment e R A - d.flight V) * d.slips A V k {i} z

lemma one_sight (q : Quote) {i : ℕ} {A : Stores S} (k : S.Choices) (hm : e.matched A V) :
    d.receive R A V k {i} = (∫ z, d.sight q R A V k i z ∂(e.law A V k)) * Real.exp (e.cost R A V k - q.assessment e R A) := by
  unfold receive sight; rw [if_pos hm,integral_const_mul]; rw [mul_right_comm,← Real.exp_add]; congr 2; ring

/-- Paired prices at the very same Haar and Gaussian charts. All numeric
meters fresh inputs. May be excessive to take absolute sizes for these
local numerator hypotheses at this level (would then need a more delicate
estimate `LogMotion.Chipped` already after lower resummation). -/
structure View (e : Plate G S) where
  tall : Stores S → S.Choices → ℕ → ℝ
  cost : Stores S → S.Choices → ℕ → ℝ
  probe : Stores S → S.Choices → ℕ → Quote
  pane : (A : Stores S) → S.Choices → ℕ → e.Sample A → ℝ
  wide : (A : Stores S) → S.Choices → ℕ → e.Sample A → ℝ
  meter : Token
  root : ℕ → ℝ

structure Supported (d d' : HeadGas e) (v : View e) (R : Rep G f) (V : Config G c) (ρ : ℝ) : Prop where
  pricing : e.Receipt R
  support : d'.reads=d.reads
  roster : d'.chosen=d.chosen
  roots i : (d.reads i).Nonempty
  balanceL : d.Balance R V
  balanceR : d'.Balance R V
  affix : Fund d.reads e.point.B v.meter.width v.meter.quota v.meter.rate v.meter.wages
  pair A k i : A∈d.chosen → e.matched A V → let q := v.probe A k i; let M := e.law A V k; let s := v.pane A k i; let m := v.wide A k i
    q.Pays e A V k ∧ Integrable s M ∧ Integrable m M ∧ (∀ᵐ z ∂M,
      Chip ρ (d.sight q R A V k i z) (d'.sight q R A V k i z) (s z) (m z)) ∧
      (∫ z,s z ∂M)*Real.exp q.tip ≤ v.cost A k i ∧
      ((∫ z,m z ∂M)-(∫ z,s z ∂M))*Real.exp q.tip ≤ v.tall A k i-v.cost A k i
  list i :
    Menu.columns e V (fun A k => v.cost A k i) d.chosen ≤ v.root i ∧
    Menu.columns e V (fun A k => v.tall A k i) d.chosen - Menu.columns e V (fun A k => v.cost A k i) d.chosen
      ≤ v.meter.wages i-v.root i

private lemma increase {ρ s t u U v V : ℝ} (h : Chip ρ s t u U) (hr : 0≤ρ) (hx : u≤v) (hy : U-u≤V-v) : Chip ρ s t v V :=
  ⟨h.paidL.trans hx,h.paidR.trans hx,sub_nonneg.mp ((sub_nonneg.mpr h.enrich).trans hy), h.swing.trans
    (mul_le_mul_of_nonneg_left hy hr)⟩

variable {d d'} {v : View e} {ρ : ℝ}
private lemma visits (h : Supported d d' v R V ρ) (i : ℕ) (hr : 0≤ρ) :
    Chip ρ (d.atoms i V) (d'.atoms i V) (v.root i) (v.meter.wages i) := by
  let u A k := if e.matched A V then v.cost A k i else 0; let m A k := if e.matched A V then v.tall A k i else 0
  have hh A k (hx : A∈d.chosen) : Chip ρ (d.receive R A V k {i}) (d'.receive R A V k {i}) (u A k) (m A k) := by
    unfold u m
    by_cases ha : e.matched A V; swap
    · simpa only [receive,if_neg ha] using Chip.zero ρ
    rw [if_pos ha,if_pos ha]
    let q := v.probe A k i
    obtain ⟨hQ,hp,hm,hV,hU,hZ⟩ := h.pair A k i hx ha
    let t := Real.exp (e.cost R A V k - q.assessment e R A)
    have he : t≤ Real.exp q.tip := Real.exp_monotone (le_of_abs_le (q.adjust _ _ _ _ _ hQ))
    rw [d.one_sight q k ha, d'.one_sight q k ha]
    have h0 := ((h.balanceL.leg A hx ha k).1 {i}).const_mul (Real.exp (q.assessment e R A - d.flight V))
    rw [←h.roster] at hx
    have h1 := ((h.balanceR.leg A hx ha k).1 {i}).const_mul (Real.exp (q.assessment e R A - d'.flight V))
    have hi := integrate_chip hV h0 h1 hp hm
    refine increase (hi.collect t (Real.exp_pos _).le) hr ?_ ?_
    · exact (mul_le_mul_of_nonneg_left he hi.nonneg).trans hU
    rw [←sub_mul]; exact (mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hi.enrich)).trans hZ
  have ht := Chip.sum d.chosen (a:=fun A => ∑ k, d.receive R A V k {i}) (fun A hA =>
    Chip.sum Finset.univ (fun k _ => hh A k hA))
  have he (d : HeadGas e) (hz : d.Balance R V) : ∑ A∈d.chosen, ∑ k, d.receive R A V k {i}=d.atoms i V := by
    rw [hz.enters {i}]; simp [note,allowed,accepted, SectorNext.Vacuum.ReLog.stays]
  have hK := increase ht hr (h.list i).1 (h.list i).2
  have hx := he d' h.balanceR
  rw [h.roster] at hx
  rwa [he d h.balanceL,hx] at hK

/-- Thus read quantitative weighted support variations on all subvolumes of
this plate, without any differentiability premise on probability likelihoods,
hard masks or anything else. Intended at all-good V, two actual allocation
component calculations feeding coefficients of the d-dependent template. On
other V would need to include flag reconstruction. Doesn't price Reading
itself, all-good identifications, d/dV derivatives or the gauges. `t.Paid`
at points away from this V does *not* follow from this Supported. -/
lemma inspected (h : Supported d d' v R V ρ) (hr : 0≤ρ) :
    let C := locker (fumes d.reads (-v.meter.wages))
    let b := native (n:=c) e.point.B v.meter.width
    let z := fumes d.reads (fun i => d.atoms i V)
    let y := fumes d'.reads (fun i => d'.atoms i V)
    (∀ i, 0 ≤ C i ∧ |raw d.reads d.atoms i V-raw d'.reads d'.atoms i V| ≤ ρ * C i) ∧
    Applied b z v.meter.quota C ∧ Applied b y v.meter.quota C := by
  intro C b z y
  obtain ⟨hx,ht,hv⟩ := LogMotion.atomic d.reads h.roots (permits d.reads _ h.affix) (fun i => visits h i hr) hr
  change _ ∧ Applied b _ _ C ∧ Applied b (fumes d'.reads _) _ C
  rw [h.support]
  refine ⟨fun i => ?_,ht,hv⟩
  exact ⟨(hx i).nonneg.trans (hx i).enrich,(hx i).swing.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (hx i).nonneg) hr)⟩
end HeadGas
end YM.AnalyticBridge.ResetIncome
