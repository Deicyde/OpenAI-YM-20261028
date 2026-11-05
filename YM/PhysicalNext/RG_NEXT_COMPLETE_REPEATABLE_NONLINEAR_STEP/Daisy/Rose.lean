import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Corral
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Tino
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
variable (hF:foam Q L) (hb:Bikes Q L μ x a e B j n)
def daisD (Q:ConnectedActivityE6.Target G P) (L : Side)(μ x:ℝ)(n:ℕ):= pledgeX L Q μ x n * Real.exp (-(Q.mark L μ x)) -- B and j unused
include hF hb
local notation "c0" => (radiusB x)
local notation "X0" => pledgeA L Q μ x B j n
local notation "VQ" => pledgeQ L Q μ x B j n
local notation "E0" => Q.mark L μ x
local notation "ΦQ" => daisD Q L μ x n -- change
lemma raindance : Plating (b₁:=e) M H N a X0 (sailUp Q L x) (ΦQ) VQ E0 e:=by
  let hℓ:=H.laws; have hx:= H.laws.data.funds.length_eq
  have hZ:=N.conduit.lives; rw [hx] at hZ; have hp:=(hb.rev _ _ hZ)
  have hW := hℓ.acquired; rw [hx] at hW; have hM:= hb.rev _ _ hW; have he : 0 < Real.exp (-E0):= Real.exp_pos _
  let f := (swing Q L μ R.beta x q).ceiling 0 n 0 0
  have hh:f = (swing Q L μ 1 x 0).ceiling 0 n 0 0:=rfl
  let p0 :=(swing Q L μ R.beta x C).ceiling 0 0 1 0
  have hV:p0=(swing Q L μ 1 x 0).ceiling 0 0 0 0*Real.exp (-E0):=by
    let c:=swing Q L μ 1 x 0; change c.ceiling 0 0 1 _=_; unfold Mixed.Costs.ceiling Reserves.extract; simp only [Nat.cast_one,Nat.cast_zero,mul_zero,mul_one,sub_zero]; change _*Real.exp (0-E0)*_= (_*Real.exp (0:ℝ)*_)*_; rw [zero_sub,Real.exp_zero]; ring
  have hz : H.faresP.ceiling 0 n 1 0=Q.overture L μ x n * Real.exp (-E0):=by have h:=Q.quantum_form L μ x 0 n 1 0; simp only [Nat.cast_one,mul_one] at h; exact h
  have hC:R.p.B ≤ 2*radiusB x:=by rw [H.laws.intake.sizes,hx]; exact hb.covers
  have hp' := Charity.la M H N hF hC (show (swing Q L μ R.beta x q).Buy S.patch.L Q.halo (radiusB x) from hx.symm ▸ hp) (a+e+e) hb.win 0 n 0 -- syntax
  have hQT :=premium_hit M H C _ H.positive hF hC (show (swing Q L μ R.beta x C).Buy S.patch.L Q.halo (radiusB x) from hx.symm ▸ hM) H.armed 0 0 1
  have hhf:0≤f:=budget_nonneg (hp' 0)
  let cZ:= (swing Q L μ 1 x 0).ceiling 0 0 0 0
  have ho : 0≤cZ:=nonneg_of_mul_nonneg_left (le_trans (b:=p0) (budget_nonneg (hQT 0)) hV.le) he
  have hey:= Q.overture_pos (L:=L) (μ:=μ) x n hb.paid
  have hB:=N.balance; have hz':0< X0:= by rw [pledgeA,←hh]; positivity
  have ha:0<pledgeX L Q μ x n := by unfold pledgeX cZ at *; positivity
  refine ⟨⟨hz',hb.allow,hb.push,hb.within.trans_lt (by norm_num),fun i=>Charity.rises ..,fun i=>?_⟩, fun i=> ?_,H.laws.acquired.marked,hb.posts,hb.allow,(by unfold pledgeQ; positivity),hb.gains,?_,hb.heat⟩
  · let v s:=N.conduit.meant s n
    have hy := budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (N.conduit.paid n i)
    have hr:= budget_scale hB (budget_plus hy (budget_scale zero_le_two (hp' i)))
    refine budget_loosen (budget_mono (budget_scale (show 0≤(2:ℝ)^(j+2) from by positivity) hr) (fun z=> ?_) (fun z=>?_)) ?_
    · split; exact mul_nonneg (Charity.rises ..) (Real.exp_pos _).le; rfl
    · dsimp only; split
      next h=>
        rw [if_pos (show i∈H.unionP z.val from h)]; unfold Charity.zoe Charity.sip Charity.momentS
        -- inequality expo.For both. do separately
        let t:= H.smallAt z; let k:= coverNumber c0 t
        let u:= Real.exp ((a+e+e)*k); have hz : u ≤ Real.exp (Q.exp * k):= Real.exp_monotone (mul_le_mul_of_nonneg_right hb.win (by positivity))
        have ht:= N.conduit.meant_nonneg n z.val
        change 2^(j+2)*(B*N.conduit.meant _ n+2*(B*_))*u≤ 2^(j+2)*(B*(N.conduit.meant _ n*Real.exp (Q.exp*k)+2*(_*Real.exp ((a+e+e)*k))))
        calc
          _ = 2^(j+2)*(B*( N.conduit.meant z.val n*u+2*(persona M H q N.conduit.flair 0 n 0 z.val*u))):=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hz ht) _) hB) (by positivity)
      next h=> rw [if_neg (show i∉ H.unionP z.val from h)]; simp
    rw [pledgeA,← hh]; let c :=(Q.overture L μ x n+2*f); change 2^(j+2)*(B*c) ≤ _*c; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by unfold c; positivity)
  · have hv : (a+e) ≤ Q.exp:= (le_add_of_nonneg_right hb.allow.le).trans hb.win
    have hk:= budget_pull (fun i:H.ThickP => i.val) Subtype.val_injective (hQT i)
    have ht := budget_plus (H.gross 0 n 1 0 hv i) (budget_scale zero_le_two hk)
    refine budget_loosen (budget_mono ht (fun v=> ?_) (fun v=> ?_)) ?_
    · split; exact mul_nonneg (Charity.rides ..) (Real.exp_pos _).le; rfl
    · dsimp only; split
      next h =>
        rw [if_pos (show i∈H.unionP _ from h)]
        let u:= Real.exp ((a+e)*coverNumber c0 (H.unionP v.val))
        have hf : u ≤ Real.exp (Q.exp *coverNumber c0 (H.unionP v.val)):= Real.exp_monotone (mul_le_mul_of_nonneg_right hv (by positivity))
        unfold Charity.za; rw [add_mul]
        apply add_le_add_right; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (earned M H _ _ H.positive ..)) zero_le_two
      next h=> rw [if_neg (show i∉ H.unionP v.val from h)]; simp
    apply le_of_eq; unfold daisD pledgeX; rw [hz, show (swing ..).ceiling .. =_ from hV]; ring
  unfold daisD; let V:=pledgeX L Q μ x n
  have hx : Real.exp E0*( V*Real.exp (-E0))=V:=by rw [mul_left_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  have hh : 1/2 ≤ 1-sailUp Q L x:=(by linarith [hb.within]); have hp: (1-sailUp Q L x)⁻¹ ≤ 2 := (inv_anti₀ (by norm_num) hh).trans (by norm_num)
  unfold pledgeQ; change _*(V*_)+_*(X0 * _ ) ≤ 10*(X0+V); linarith only [hx, ha,hz',mul_le_mul_of_nonneg_left hp hz'.le]
end Charity
end YM.PhysicalNext.Repeat.Daisy
