import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rose
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
include h
lemma captors (U : BudgetPoint)(y:Site c)(hy:y∈M.crest.image S.ratio.parent)(hU: U.threshold= Pressure.temp x)(hp : U.order=j)(ha: 0≤a)(k:Bikes Q L μ x a e B j n)(hf:foam Q L)(hk: Daisy.tailCost L Q μ x B e j n U.power ≤Daisy.poster Q L x)(Z:ℕ):
    ∃ f:H.fragrances→ℝ,(∀ i,0≤f i∧ U.supBounds y (locus M H y i) (matin M H i χ) (f i)) ∧ SumBudget (fun i:H.fragrances=> if Z< i.fst then f i else 0) ((1/2:ℝ)^Z*(R.p.mass M.crest M.weight* Real.exp (-Q.ε * coverNumber R.p.B M.crest)* Daisy.poster Q L x)):=by
    let P(i):= if speaks M H i then d0*oval M H N i*flareC (x:=x) (j:=j) U.power (H.bookFoot (.inr i)) else 0
    have he i : U.supBounds y (locus M H y i) (matin M H i χ) (P i):= aliveY M H N h U hy hU hp.le i; refine ⟨P,fun i=> ⟨(he i).1,he i⟩,?_⟩
    have hL:= H.laws.data.funds.length_eq; have hR : R.p.B ≤ 2*radiusB x:=by rw [H.laws.intake.sizes,hL]; exact k.covers
    have hv : a+e ≤ Q.exp:= (le_add_of_nonneg_right k.allow.le).trans k.win
    have hq:= raindance M H N hf k
    have ht:= roughS M H N hq (Z+1) U.power y hy
    have hd:0 ≤ d0:=(dew M H).2.1
    let B':= B*collars G e x j U.power*((swing Q L μ R.beta x q).ceiling 1 n 0 0)
    let p:=collars G e x j U.power*(pledgeA L Q μ x B j n*sailUp Q L x*(1-sailUp Q L x)⁻¹)
    have hp':0 ≤ d0*p:= mul_nonneg hd (by have hz:= budget_nonneg (roughS M H N hq 1 U.power y hy); rw [pow_one] at hz; exact hz)
    have hb:0≤ d0* B':= budget_nonneg (needleTail (a:=a) M H N hf hR (show (swing Q L μ R.beta x q).Buy S.patch.L Q.halo (radiusB x) from hL.symm ▸ k.rev R.beta q (hL ▸ N.conduit.lives)) y hy 1 U.power k.allow hv)
    let g i:= if (Z+1)≤ Sigma.fst i then P i else 0
    have hu'(i):g i≥0:=by unfold g; split; exact (he i).1; exact le_rfl
    have hz:(fun i:H.fragrances=> if Z< i.fst then P i else 0)=g:=by
       funext i; unfold g; congr 1
    rw [hz]; apply budget_loosen (budget_mono (budget_scale hd ht) hu' (fun i=>?_)) _; swap
    · dsimp only; split
      next hp=>
       have h:P i = d0*(oval M H N i*flareC (x:=x) (j:=j) U.power (locus M H y i)):=by unfold P locus; rw [if_pos hp.1,if_pos hp.1,mul_assoc]
       rw [show g i=P i from if_pos hp.2, ← mul_assoc, ← h]; exact le_mul_of_one_le_right (he i|>.1) (Real.one_le_exp (mul_nonneg ha (by positivity)))
      next h₀=>
       unfold g; split
       next hx=> rw [show P i=0 from if_neg (fun h=>h₀ ⟨h,hx⟩),mul_zero]
       next=>rw [mul_zero]
    let f:= R.p.mass M.crest M.weight* Real.exp (-Q.ε * coverNumber R.p.B M.crest); have hh:0≤ f:= mul_nonneg (M.profit.trans (R.p.loMass _ _ M.profit)) (Real.exp_pos _).le
    have hy: d0 * B'+d0*p=f*Daisy.tailCost L Q μ x B e j n U.power:=by unfold B' p f Daisy.tailCost jewelDebt; rw [show (swing Q L μ R.beta x q).ceiling 1 n 0 0=(swing Q L μ 1 x 0).ceiling 1 n 0 0 from rfl]; ring
    have hE:0 ≤ sailUp Q L x:= by -- inspect k
       unfold sailUp; apply Real.rpow_nonneg; exact k.paid.le -- paid?
    calc _ = (sailUp Q L x)^Z*(d0*p) :=by rw [pow_succ]; unfold p; ring
         _ ≤ (1/2:ℝ)^Z * (d0*p):= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE k.within _) hp'
         _ ≤ (1/2:ℝ)^Z * (f*Daisy.poster Q L x):= mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hb).trans (hy.trans_le (mul_le_mul_of_nonneg_left hk hh))) (by positivity)
end Charity
end YM.PhysicalNext.Repeat.Daisy
