import YM.MergeProof.Wreath
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rose

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "X'"=> swing Q L μ R.beta x C
local notation "dc"=> ConnectedActivityE6.lengths T R
local notation "kd"=> steamP S (Q.costs L μ R.beta x C)
structure Plot : Prop where
   pays : Accounts S Q.halo sx X' Y.birth (pitch M Y rA) dc kd
   live i : 0≤rA i

variable (hR:Plot M Y rA) {e d B:ℝ} {j k : ℕ} (hB: Bikes Q L μ x a e B j k)
set_option quotPrecheck false
include hR
local notation "p₀"=> fun i:Y.ThinP=> tune M Y rA 0 k i.val
local notation "p₁"=> fun i:Y.ThickP=> tune M Y rA 1 0 i.val
local notation "P₀"=> pledgeA L Q μ x B j k
local notation "P₁"=> Charity.daisD Q L μ x k
local notation "VQ" => pledgeQ L Q μ x B j k
local notation "E0" => Q.mark L μ x
local notation "ρ"=> sailUp Q L x

lemma aca (p : Y.ThinP) (k:ℕ): Switch.Paid (vote M Y χ rA p.val) (tune M Y rA 0 k p.val):= votes M Y χ rA hR.live _ _ _ (Nat.zero_le _)
lemma ack (p : Y.ThickP): Switch.Paid (vote M Y χ rA p.val) (tune M Y rA 1 0 p.val):= votes M Y χ rA hR.live _ _ _ (Cash.forced_cost p.val p.prop.2)
include hB
lemma accrued (m' k : ℕ) : Ac.Hit Y.unionP (radiusB x) (tune M Y rA m' k) Q.exp ((X').ceiling 0 k m' 0):= by
   have ht:= Y.laws.data.funds.length_eq; have he:=Y.laws.acquired
   have hp:(X').Buy S.patch.L Q.halo (radiusB x) := by rw [ht] at *; exact hB.rev _ _ he
   exact Mixed.mixed_hit S _ _ _ Y.birth _ dc kd hp hR.pays 0 k m' 0
include χ
lemma shrink (he:d≤Q.exp) : Ac.Hit Y.smallAt (radiusB x) p₀ d ((X').ceiling 0 k 0 0) ∧ Ac.Hit Y.largeAt (radiusB x) p₁ d ((X').ceiling 0 0 1 0) := by
   constructor
   · intro x
     have hz:=budget_pull (fun i:Y.ThinP=>Subtype.val i) Subtype.val_injective (accrued M Y rA hR hB 0 k x)
     refine budget_mono hz (fun i=> ?_) (fun i=> ?_)
     · split; exact mul_nonneg (Switch.Paid.rocket (aca M Y χ rA hR i k)) (Real.exp_pos _).le; exact le_rfl
     split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (Switch.Paid.rocket (aca M Y χ rA hR i k)) |>.trans_eq (if_pos (show x∈Y.unionP i.val from h)).symm -- if? fix
     next=> exact hz.1 i
   intro x
   have hz:=budget_pull (fun i:Y.ThickP=>Subtype.val i) Subtype.val_injective (accrued M Y rA hR hB 1 0 x)
   refine budget_mono hz (fun i=> ?_) (fun i=> ?_)
   · split; exact mul_nonneg (Switch.Paid.rocket (ack M Y χ rA hR i)) (Real.exp_pos _).le; exact le_rfl
   split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (Switch.Paid.rocket (ack M Y χ rA hR i))|>.trans_eq (if_pos (show x∈Y.unionP i.val from h)).symm
   next=> exact hz.1 i

-- only uses numeric B≥0
include χ
lemma field (hb:0≤B): Ready Y.smallAt (radiusB x) p₀ (a+e) P₀ e ρ ∧ Ac.Hit Y.largeAt (radiusB x) p₁ (a+e) P₁ ∧ 0≤E0∧0<VQ∧ 2*Real.exp E0*(1-1/2:ℝ)⁻¹*P₁+2*(1-1/2:ℝ)⁻¹*((P₀)*(1-ρ)⁻¹)≤VQ:=by
   let u0:=(X').ceiling 0 k 0 0; let v0:=(X').ceiling 0 0 0 0; let w0:= (X').ceiling 0 0 1 0
   have hH:= hB.win
   obtain ⟨h0,h1⟩:= shrink M Y χ rA hR hB hH; have hy : 0≤u0 := budget_nonneg (h0 0); have ht:0≤w0:=budget_nonneg (h1 0)
   have hp:w0=v0 * Real.exp (-E0):=by
     unfold w0 v0 Mixed.Costs.ceiling Reserves.extract; simp only [Nat.cast_one,Nat.cast_zero,mul_zero,mul_one,sub_zero]; change _*Real.exp (0-E0)*_= (_*Real.exp (0:ℝ)*_)*_; rw [zero_sub,Real.exp_zero]; ring
   have hv:0≤ v0:= nonneg_of_mul_nonneg_left (hp ▸ ht) (Real.exp_pos _)
   let E':=pledgeX L Q μ x k
   have he':0 < Q.overture L μ x k:= Q.overture_pos _ _ hB.paid
   have hP:P₀=(1+2^(j+2)*B)*(Q.overture L μ x k +2*u0):=rfl
   have hQ:E'= Q.overture L μ x k+2*v0:=rfl
   have hz: 0<P₀:= by rw [hP]; positivity
   have hw:0<E':=by rw [hQ]; positivity
   refine ⟨⟨hz,hB.allow,hB.push,hB.within.trans_lt (by norm_num),fun i=> Switch.Paid.rocket (aca M Y χ rA hR i k), fun i=>budget_loosen (h0 i) ?_⟩,?_,Y.laws.acquired.marked,(by change 0<10*((P₀)+E'); positivity),?_⟩
   · rw [hP]; change u0 ≤ _; apply le_trans (b:=Q.overture L μ x k+2*u0) (by linarith only [hy,he'])
     exact le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (by positivity))
   · have hi := shrink M Y χ rA hR hB ((le_add_of_nonneg_right hB.allow.le).trans hB.win); intro i
     refine budget_loosen (hi.2 i) ?_; change w0 ≤ E' *_; rw [hp,hQ]; exact mul_le_mul_of_nonneg_right (by linarith only [hv,he']) (Real.exp_pos _).le
   change 2*Real.exp (E0)*(1-1/2:ℝ)⁻¹*(E'*Real.exp (-E0))+2*_*(P₀*_)≤ 10*((P₀)+E')
   have he : Real.exp E0*(E'*Real.exp (-E0))=E':=by rw [mul_left_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
   have hp₀ : 1/2≤1-ρ:=by linarith [hB.within]
   have hp: (1-ρ)⁻¹≤ 2:=(inv_anti₀ (by norm_num) hp₀).trans (by norm_num)
   linarith only [he,mul_le_mul_of_nonneg_left hp hz.le,hz,hw]
end YM.Merge.Palette
