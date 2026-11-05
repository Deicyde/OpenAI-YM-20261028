import YM.UVExtension.Above.Facets
import YM.UVExtension.Whirl.Layer

/-! # Linear spaces of accepted real inputs. Permutations are fixed
    (don't assume you can add two functions with different invariances).
    Separate literal backing in some fixed layout; no closure assertion on raw
    arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tabernacle
open Function Set Filter Metric Lattice RG Precision Wilson Ovens
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset
open scoped Matrix.Norms.Frobenius Topology ContDiff Classical
variable {G : Gauge} {n : Side}

abbrev Field (G:Gauge)(n:Side) := Ovens.Code G n × Ovens.Code G n
variable (p : BudgetPoint)
def floor (u : Field G n): Activities G n:= ⟨(drawer G n).reg,Ovens.Pipes.addr (folio G n) p,u.1,u.2⟩
def rake (U:Field G n): Prop := ∃ a b, (floor p U).Valid p a b -- typo
structure Charm (G:Gauge) (p : BudgetPoint) (n:Side) where
   root : Field G n
   checks : rake p root
   run s b: (floor p root).Moves s b
variable (d:Charm G p n)
def copied (U:Field G n) := rake p U ∧ ∀ s b, ∃ F:(floor p U).Moves s b, Twins F (d.run s b)

variable (u w : Field G n){a b x y:ℝ}

lemma grown_s (c:ℝ)(h:copied p d u) : copied p d (c • u):= by
  obtain ⟨⟨a,A,h⟩,hp⟩:=h
  have hP(s b):∃ F:(floor p (c • u)).Moves s b,Twins F (d.run s b):=by
    obtain ⟨F,hF⟩:= hp s b; exact ⟨⟨F.ep,F.kp,F.reg_site,F.reg_support,F.forced_support,F.forced_inventory,F.forced_tests,fun i U=>congr_arg (c • ·) (F.valuesE i U),fun i U=> congr_arg (c • ·) (F.valuesK i U)⟩, hF⟩
  refine ⟨⟨‖c‖*a,‖c‖*A,⟨fun i=>WilsonStartup.Start.times_reg c (h.regular.smooth i),fun i=>?_,?_⟩,⟨fun i s b=> congr_arg (c • ·) (h.forced.sym i s b),h.forced.symtest,fun i=> (h.forced.meas i).const_mul _,h.forced.meas_test, fun i s b he hv=> congr_arg (c • ·) (h.forced.reads i s b he hv), h.forced.reads_test,fun i V hi=> h.forced.permit i V (right_ne_zero_of_mul hi)⟩, fun s b=>⟨(hP s b).choose⟩,?_,?_⟩,hP⟩
  · exact (congr_arg (c • ·) (h.regular.at_flat i)).trans (smul_zero ..)
  · intro i ht x y hx hy; let f: Config G n→ℝ:= (floor p u).E i; change (iteratedFDeriv ℝ 2 (c • germ f) 0) _= _
    rw [iteratedFDeriv_const_smul_apply (germ_diff (h.regular.smooth _))]; exact (congr_arg (c • ·) (h.regular.vanish i ht x y hx hy)).trans (smul_zero ..)
  · obtain ⟨f,hf,hb⟩:= h.boundE; refine ⟨fun i=>‖c‖*f i,fun i=> WilsonStartup.Start.times_bound c (hf i),fun i=>?_⟩
    have hx:= budget_scale (norm_nonneg c) (hb i); simpa only [mul_ite,mul_zero,BudgetPoint.mass, floor,mul_left_comm] using hx
  obtain ⟨f,hf,hb⟩:= h.boundK; refine ⟨fun i=>‖c‖*f i,fun i=>⟨mul_nonneg (norm_nonneg c) (hf i|>.1),fun U=>?_⟩,fun i=>?_⟩
  · change ‖c*((floor p u).K i U)‖ ≤ _; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((hf i).2 U) (norm_nonneg _)
  have hx:= budget_scale (norm_nonneg c) (hb i); simpa only [mul_ite,mul_zero,BudgetPoint.mass, floor,mul_left_comm] using hx

private lemma set_add (p:Prop)[Decidable p](x y:ℝ):(if p then x else 0)+(if p then y else 0)=if p then x+y else 0:= by split <;> simp_all
lemma grown_d (h:copied p d u)(hg:copied p d w): copied p d (u-w):=by
  obtain ⟨⟨a,A,h⟩,hp⟩:=h; obtain ⟨⟨b,B,hg⟩,hr⟩:=hg
  have he(s b):∃ F:(floor p (u-w)).Moves s b,Twins F (d.run s b):=by
    obtain ⟨F,hF⟩:=hp s b; obtain ⟨H,hH⟩:=hr s b; have he(i):F.ep i=H.ep i:= congr_fun (congr_arg DFunLike.coe (hF.1.trans hH.1.symm)) _
    have hv(i): F.kp i=H.kp i:= congr_fun (congr_arg DFunLike.coe (hF.2.trans hH.2.symm)) _
    exact ⟨⟨F.ep,F.kp,F.reg_site,F.reg_support,F.forced_support,F.forced_inventory,F.forced_tests, fun i v=> congr_arg₂ (·-·) (F.valuesE i v) (show (floor p w).E (F.ep i) v=_ from he i ▸ H.valuesE i v), fun i v=> congr_arg₂ (·-·) (F.valuesK i v) (show (floor p w).K (F.kp i) v= _ from hv i ▸ H.valuesK i v)⟩, hF⟩ -- equiv not Funlike?
  refine ⟨⟨a+b,A+B,⟨fun i=> reg_sub (h.regular.smooth i) (hg.regular.smooth i),fun i=> sub_eq_zero.mpr ((h.regular.at_flat i).trans (hg.regular.at_flat i).symm),fun i ht x y hx hy=> ?_⟩,⟨fun i s U=> congr_arg₂ (·-·) (h.forced.sym i s U) (hg.forced.sym i s U),h.forced.symtest,fun i=> (h.forced.meas i).sub (hg.forced.meas i),h.forced.meas_test,fun i s b he hv=> congr_arg₂ (·-·) (h.forced.reads i s b he hv) (hg.forced.reads i s b he hv),h.forced.reads_test, ?_⟩, fun s b=>⟨(he s b).choose⟩,?_,?_⟩,he⟩
  · exact (hessian_sub (h.regular.smooth i) (hg.regular.smooth i) x y).trans (sub_eq_zero.mpr ((h.regular.vanish i ht x y hx hy).trans (hg.regular.vanish i ht x y hx hy).symm))
  · intro i U hH; by_cases hx : (floor p u).K i U=0
    · change (floor p u).K i U-(floor p w).K i U ≠0 at hH; rw [hx,zero_sub] at hH; exact hg.forced.permit i U (neg_ne_zero.mp hH)
    exact h.forced.permit i U hx
  · obtain ⟨f,H,hF⟩:= h.boundE; obtain ⟨g,H',hG⟩:= hg.boundE; refine ⟨fun i=>f i+g i,fun i=> sup_sub (h.regular.smooth i) (hg.regular.smooth i) (H i) (H' i), fun i=>?_⟩
    simpa only [BudgetPoint.mass,floor,mul_add,set_add] using! budget_plus (hF i) (hG i)
  obtain ⟨f,H,hF⟩:= h.boundK; obtain ⟨g,H',hG⟩:= hg.boundK; refine ⟨fun i=>f i+g i,fun i=>⟨add_nonneg (H i|>.1) (H' i|>.1),fun U=> (norm_sub_le _ _).trans (add_le_add ((H _).2 _) ((H' _).2 _))⟩,fun i=>?_⟩
  simpa only [BudgetPoint.mass,floor,mul_add,set_add] using! budget_plus (hF i) (hG i)

namespace Charm
def Shed : Submodule ℝ (Field G n) where
    carrier:= copied p d
    zero_mem':= by
      have h:= grown_s p d d.root 0 ⟨d.checks,fun s b=> ⟨d.run s b,⟨rfl,rfl⟩⟩⟩; rw [zero_smul] at h; exact h
    smul_mem' _ x:= grown_s p d x _
    add_mem' {x y} hx hy := by rw [← sub_neg_eq_add,← neg_one_smul ℝ y]; exact grown_d p d x _ hx (grown_s p d y _ hy)
-- dispense numbers literal
lemma income (x:d.Shed p):copied p d x.val:=x.property
def maps (x:d.Shed p) (s:Signed)(b:Site n): (floor p x.val).Moves s b := ((d.income p x).2 s b).choose
lemma choice (x:d.Shed p)(s:Signed)(b:Site n): Twins (d.maps p x s b) (d.run s b):=((d.income p x).2 s b).choose_spec
end Charm
end YM.UVExtension.Tabernacle
