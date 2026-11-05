import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Coasts
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
variable (ha:foam Q L) (hq:R.p.B ≤ 2*radiusB x) (hv:(swing Q L μ R.beta x q).Buy S.patch.L Q.halo (radiusB x)) (hw:(swing Q L μ R.beta x C).Buy S.patch.L Q.halo (radiusB x))
include ha hq hv
lemma la (z : ℝ) (hz : z ≤ Q.exp)(i m n':ℕ) : Ac.Hit H.smallAt (radiusB x) (fun p=> persona M H q N.conduit.flair i m n' p.val) z ((swing Q L μ R.beta x q).ceiling i m n' 0):=by
  intro x; have hx:=budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (premium_hit M H q N.conduit.flair N.conduit.fares ha hq hv N.conduit.accrues i m n' x)
  refine budget_mono hx (fun p=>?_) (fun i=>?_)
  · split; exact mul_nonneg (earned M H q _ N.conduit.fares ..) (Real.exp_pos _).le; exact le_rfl
  split
  next h=> dsimp only; rw [if_pos (show x∈H.unionP i.val from h)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) (earned M H q _ N.conduit.fares ..)
  next h=> exact hx.1 _

variable (y:Site c) (hy:y∈M.crest.image S.ratio.parent)
include hy
local notation "Z0" => locus M H y
lemma needleTail (i m : ℕ)(he:0 < e)(hz:a+e ≤ Q.exp):
    SumBudget (fun p:H.fragrances=> if p.fst=0 then pine M H N y m i p * Real.exp (a*coverNumber (radiusB x) (Z0 p)) else 0)
     (d0*(B*collars G e x j m*((swing Q L μ R.beta x q).ceiling i n 0 0))) :=by
  let f p:=if (p:H.fragrances).1=0 then pine M H N y m i p *Real.exp (a*coverNumber (radiusB x) (Z0 p)) else 0
  have H' := la M H N ha hq hv _ hz i n 0 y; let u (s:Molecule S):= persona M H q N.conduit.flair i n 0 s
  let v:= collars G e x j m; have he' : 0≤v:=by unfold v collars Reserves.polyPrice March.shiftG; positivity
  have hb:= budget_scale (f:=_) (mul_nonneg (dew M H|>.2.1) (mul_nonneg N.balance he')) H'
  have hk(p): 0 ≤ f p := by unfold f; split_ifs; exact mul_nonneg (quench ..) (Real.exp_pos _).le; rfl
  change SumBudget f _; rw [← mul_assoc (jewelDebt ..) (B*_)]; -- check
  have h0 (p:H.ThinP):0≤u p.val:= earned M H q _ N.conduit.fares ..
  have hp : LeftInverse (fun p:H.fragrances=>p.2 none) (chip H):= fun i=>rfl
  suffices h : SumBudget (f ∘ chip H) (d0*(B*v)*(swing Q L μ R.beta x q|>.ceiling i n 0 0)) by
    have hf (t) (ht:t∉ Set.range (chip H)) : f t=0:=if_neg fun h=> ht ⟨_,(single H t h).symm⟩
    have hv:= (hp.injective.hasSum_iff hf).mp h.2.1.hasSum
    exact ⟨hk,hv.summable,hv.tsum_eq.trans_le h.2.2⟩
  refine budget_mono hb (fun p=> hk (chip H p)) (fun p=>?_)
  let b:ℝ:=coverNumber (radiusB x) (H.smallAt p)
  unfold Function.comp f; rw [if_pos (show (chip H p).fst=0 from rfl)]
  by_cases hh:speaks M H (chip H p)
  swap; · unfold pine; rw [if_neg hh,zero_mul]; exact hb.1 _
  have ht:= seatY M H y hy (chip H p); unfold locus at ht; rw [if_pos hh,clipS] at ht
  unfold pine; rw [if_pos hh,if_pos (show (chip H p).fst=0 from rfl),locus,if_pos hh,clipS, potY,locus,if_pos hh,clipS,if_pos (show y∈H.smallAt p from ht)]
  unfold flareC; rw [mul_pow]
  change (shiftG x ^ _*(1+b)^_)*d0*(B*u p.val) *Real.exp (a*b)≤ _ * (u p.val * Real.exp ((a+e)*b))
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_cost he (show 0≤b from Nat.cast_nonneg _) _) (pow_nonneg (show 0≤ shiftG x from by unfold shiftG; positivity) _)) (dew M H|>.2.1)) (mul_nonneg N.balance (h0 _))) (Real.exp_pos _).le).trans_eq
  rw [add_mul a, Real.exp_add]; unfold v collars Reserves.polyPrice u; ring
lemma catchAll (i:ℕ)(k:Plating (b₁:=b₁) M H N a t g c₁ u κ' e)(hz:a+e ≤ Q.exp): SumBudget (fun p=> pine M H N y i 1 p *Real.exp (a*coverNumber (radiusB x) (Z0 p)))
  (d0* (B*collars G e x j i*((swing Q L μ R.beta x q).ceiling 1 n 0 0)+collars G e x j i*(t*g*(1-g)⁻¹))):=by
  have he:=roughS M H N k 1 i y hy; simp_rw [pow_one] at he
  have hh:= needleTail M H N ha hq hv y hy 1 i k.post hz
  rw [mul_add]
  apply Eq.mp (_:SumBudget _ _ = _ ) (budget_plus hh (budget_scale (dew M H|>.2.1) he));
  apply congr_arg (SumBudget · _); ext p
  simp only [pine,potY]; by_cases h:p.1=0; · simp [h]
  by_cases hh:speaks M H p <;> simp only [h, show 1 ≤ p.fst from Nat.one_le_iff_ne_zero.mpr h,hh, ↓reduceIte,and_true] <;> ring
end Charity
end YM.PhysicalNext.Repeat.Daisy
