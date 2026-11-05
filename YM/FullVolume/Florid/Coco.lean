import YM.FullVolume.Sym.Stage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Solvent
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill  Eider   Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}


variable (M:Leaf R)(H:Cash W x μ L Q o C T R)
local notation "Q'"=> Empire.stella Q
local notation "B"=> radiusB x
local notation "cR"=> coverNumber R.p.B M.crest
include H
lemma azure : 0<(Q').goal L x:=by
  apply Real.rpow_pos_of_pos; have he:= H.laws.intake.height; rw [H.laws.data.funds.length_eq] at he; linarith
lemma scentL : 0<jewel M Q' L x ∧ 0 ≤ jewelDebt M Q' L x ∧ M.weight=jewelDebt M Q' L x*jewel M Q' L x:=by
  have h:=azure H; refine ⟨mul_pos h (Real.exp_pos _),div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le M.profit) (Real.exp_pos _).le) h.le,?_⟩
  unfold jewelDebt jewel BudgetPoint.mass; field_simp; rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel,Real.exp_zero,mul_one]
variable (hf:foam Q L)(hs:R.p.B≤2*(radiusB x))
include hf hs
lemma sustainsL : Ac.Hit H.birth B (Reserves.tariff (colly (n:=c) (fun _=>0) M Q' L x) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (ribbon Q' L x):=by
  let r:= (Empire.stella Q).goal L x / Q.goal L x; have ht:= arable H; have hv:=azure H; have hr:0<r:=div_pos hv ht
  intro i; let f:=fun j=> if i∈ H.birth j then Reserves.tariff (colly (n:=c) (fun _=>0) M (Q') L x) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε j*Real.exp (Q.relative*(coverNumber B (H.birth j))) else 0
  have h:= budget_scale hr.le (sustains M H hf hs i); change SumBudget f _
  convert! h using 1
  · ext j; unfold f; split
    next hh=>
      unfold colly Reserves.tariff; dsimp only; split
      next hg=> unfold r jewel; change (Q').goal L x*_ * _ *_ = _; field_simp
      next hg=> ring
    next hh=>rw [mul_zero]
  unfold r ribbon; field_simp; rw [mul_comm];rfl
lemma mashH (F:ConnectedActivityE6.Alphabet c f→ℝ)(G2: Pressure.Stores S→ℝ)
    (e : ℝ) (hp:Accounts S Q.halo B ((Q').costs L μ R.beta x e) H.birth F (ConnectedActivityE6.lengths T R) G2): Accounts S Q.halo B (Daisy.swing Q' L μ R.beta x e) H.birth (colly F M Q' L x) (ConnectedActivityE6.lengths T R) G2:=by
  have hh i: 0≤ colly F M Q' L x i:=by unfold colly; split; exact (scentL M H).1.le; exact hp.holds i
  refine ⟨hp.packetBound,hh,hp.extra,?_⟩
  intro y; refine budget_mono (budget_plus (hp.pays y) (sustainsL M H hf hs y)) ?_ ?_
  · intro i; split_ifs; exact mul_nonneg (mul_nonneg (hh _) (Real.exp_pos _).le) (Real.exp_pos _).le; rfl
  intro i
  have he : (Daisy.swing Q' L μ R.beta x e).head= Q.relative:=rfl
  have ht : ((Q').costs L μ R.beta x e).head= Q.relative:=rfl; rw [he,ht]; split_ifs
  · unfold Reserves.tariff colly; split
    next hz=> exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hp.holds i) (Real.exp_pos _).le) (Real.exp_pos _).le)
    next hx=> simp [swing] -- if hx same
  simp
end YM.PhysicalNext.Repeat.Daisy
