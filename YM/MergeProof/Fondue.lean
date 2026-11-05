import YM.MergeProof.Badlands
import YM.MergeProof.Platter
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d:ℕ}{F:Labels.Frame G d}{o:Site n}
lemma zest (B : BudgetPoint) (X:Support n) {u t:ℝ}(hv:0 < t)(ht:0 ≤ u)(hc:X.card*t ≤1) : mergePrice B t X u ≤ Real.sqrt t*(2*(X.card:ℝ)*Real.sqrt t*B.mass X u):=by
   have hp : 0 ≤ B.mass X u:=mul_nonneg (Real.exp_pos _).le ht
   unfold Local.mergePrice; have hs := Real.abs_exp_sub_one_le (by rwa [abs_of_nonneg (show 0 ≤ X.card*t from mul_nonneg (Nat.cast_nonneg _) hv.le)]: |(X.card:ℝ)*t| ≤ 1); rw [abs_of_nonneg (show 0 ≤ X.card*t from mul_nonneg (Nat.cast_nonneg _) hv.le)] at hs
   apply (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hs) hp).trans_eq
   have he:= Real.sq_sqrt hv.le; nth_rw 1 [← he]; ring
   -- need ring
lemma platter (R:Rep G n)(S:Keeper R.p R.activities)(A:Hol G) (T:SectionData F){D:Support n}{f y p:Config G n→ℂ}{x:F.Coeff}{v δ σ C Λ r h:ℝ} (hp:R.Lawful σ C Λ δ v)(hv:0 < v) (ht:D.card*v≤1)
    (hx: R.p.Regular D f)(hg:R.p.supBounds o D f r)(hu:f 1=0)(he:Nonwrapping D o→ A.PiVanish d o f)(hc:o∈D)
    (hy:Attaches R.p.threshold D p)(hh:0 ≤ h)(ha:∀ U,‖p U‖≤h)(hq:∀ U, part T o R U x+masked R.p.threshold D f U+p U = y U):
    ∃ P: Coefficient F n, P.x=x ∧ P.Format o A R ∧ (∀ U, P.density o T R U=(R.eval U:ℂ)*y U) ∧
      P.remBound o R (Real.sqrt v) (R.p.mass D r+ 2*(D.card:ℝ)*Real.sqrt v*R.p.mass D h) ∧ ∃ f',Attainment R.p o f' (reservedMass R.p D h) ∧ profile R.activities P.forced= hook R.activities R.p.threshold f' :=by
   let X:Unit→Support n:=fun _=>D; let s:= mergePrice R.p v D h
   obtain ⟨K,hK,hs,hf,hQ⟩:= garnish R hp (S.supply X) (t:=s) (f:=fun _:Unit=>p) (A:=fun _:Unit=>h) (fun _=>hc) (fun _=>hy) (fun _=>hh) (fun _=>ha) (show SumBudget (fun _:Unit=>s) s from ⟨fun _=>mergePrice_nonneg _ _ hv.le hh, Summable.of_finite,by rw [tsum_fintype,Fintype.sum_unique]⟩) Summable.of_finite -- edit
   let P:= kickoff x D f K; have hy0:X ()=D:=rfl
   refine ⟨P,rfl,?_,?_,?_,Pi.single D p,?_,?_⟩
   · refine ⟨?_,fun _=>hc,?_,?_,hK.forcing,hK.carried,hK.invariant,hK.supported,hK.borel⟩
     · intro i; change R.p.Regular D _; by_cases ht:i=0; rwa [show P.regular i=f by simp [P,kickoff,ht]]; rw [show P.regular i=0 by simp [P,kickoff,ht]]; simpa using regular_smul 0 hx
     · intro i; by_cases h : i=0<;>simp [P,kickoff,h,hu]
     intro l hw; by_cases H:l=0
     · rw [show P.regular l=f by simp [P,kickoff,H]]; exact he hw
     rw [show P.regular l=0 by simp [P,kickoff,H]]; exact fun J => ⟨contDiffAt_const,fun k hk => by change iteratedDeriv k (0:ℝ→ℂ) 0 = 0; simp⟩
   · intro U; have hi: ∀ j,P.marked R j U=gasMark R.p R.activities U j K:=fun _=>(gasMark_eq ..).symm
     have hg' (U): P.exponentialEntry o T R U=part T o R U x+ masked R.p.threshold D f U:= congr_arg _ (masks ..)
     unfold Coefficient.density; rw [hg']; simp_rw [hi,(hQ U).tsum_eq]; rw [tsum_fintype,Fintype.sum_unique,← hq,Rep.eval, Complex.ofReal_mul]; ring_nf
   · have hz:=zest R.p D hv hh ht; refine ⟨_,_,mul_nonneg (Real.exp_pos _).le hg.1,mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)) (mul_nonneg (Real.exp_pos _).le hh),le_rfl,Real.sqrt_pos.mpr hv,⟨fun j=> if j=0 then r else 0,?_,?_⟩,?_⟩
     · have hM := R.p.loMass D r hg.1; rw [show (fun i:ℕ=> R.p.mass (P.support i) (if i=0 then r else 0))=Pi.single 0 (R.p.mass D r) by funext i; by_cases h:i=0; subst i; simp [P,kickoff]; simp only [if_neg h,Pi.single_eq_of_ne h]; simp [BudgetPoint.mass]]; exact ⟨fun i=>by by_cases h:i=0; subst i; simpa using hg.1.trans hM; rw [Pi.single_eq_of_ne h], (hasSum_pi_single _ _).summable,by simp; rfl⟩
     · intro i; by_cases h:i=0; simpa [P,kickoff,h] using hg; simpa [P,kickoff,h] using bound_smul 0 hg
     obtain ⟨b,hb,ht⟩:=hs; exact ⟨b,⟨hb.1,hb.2.1,hb.2.2.trans hz⟩,ht⟩
   · have ht (i):0 ≤ (Pi.single D h : Support n→ℝ) i:= by by_cases hx:i=D; subst i; simpa; rw [Pi.single_eq_of_ne hx]
     refine ⟨fun i=>?_,fun i hp=>?_,Pi.single D h,⟨fun i=>mul_nonneg (Real.exp_pos _).le (ht i),Summable.of_finite,?_⟩, fun i=>⟨ht i,fun U=>?_⟩⟩
     · by_cases hx:i=D;subst i; rwa [Pi.single_eq_same]; rw [Pi.single_eq_of_ne hx]; exact Attaches.zero ..
     · by_cases h:i=D; exact h.symm ▸ hc; exact (hp (Pi.single_eq_of_ne h _)).elim
     · rw [tsum_fintype,sum_eq_single D,Pi.single_eq_same]; intro b _ hb; rw [Pi.single_eq_of_ne hb,reservedMass,mul_zero]; simp
     by_cases hx:i=D; subst i; rw [Pi.single_eq_same,Pi.single_eq_same]; exact ha U
     simp [Pi.single_eq_of_ne hx]
   change profile R.activities K=_; rw [hf,show clipSum X (fun x=>p) = Pi.single D p from ?_]
   funext i U; unfold clipSum; rw [expand_eq,tsum_fintype,Fintype.sum_unique];by_cases h:D=i; subst i; simp [X]; rw [if_neg (fun he=>h he),Pi.single_eq_of_ne (Ne.symm h)]; rfl
end YM.MergeProof
