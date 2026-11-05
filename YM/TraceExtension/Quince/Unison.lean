import YM.TraceExtension.Quince.Latch
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Wilson Finset Source Extra.Histories Labels
open Push Local Next.Foundations Cub
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Site n}{H:Hol G}{d:ℕ}{F: Frame G d}
variable (S : SectionData F)
def wipe (S:SectionData F)(P:Coefficient F n)(R:Rep G n)(U:Config G n):ℂ:= Local.presented S (0:Site n) R.p.threshold P.x U+∑' i,P.regular i U
variable {S}{w t r u :ℝ}
lemma wiping (hS:S.Sound H)(P:Coefficient F n)(hP:P.Format 0 H R)(U:Config G n)(hU:U∈ dent R.p): P.density 0 S R U= Real.exp (R.exponent U)*wipe S P R U:=by
   have hx:= dent_clear hU; have hg(i:ℕ):P.forced i U=0:=by
       by_contra h; have hp:= hP.forcing i U h; unfold ForcedAddress.eligible at hp; rw[hx, Finset.inter_empty] at hp; exact ((R.activities.forced i).inventory_ne.ne_empty hp.1.symm)
   have hm(i):P.marked R i U=0:=by
       unfold Coefficient.marked; split; · apply Finset.sum_eq_zero; intro j hj; simp [hg]
       rfl
   have hh: P.exponentialEntry 0 S R U=wipe S P R U:=by
       change Local.primary S 0 R.p.threshold P.x U + ∑' i,P.maskedTerm R i U = _; unfold wipe; rw[presented_primary _ hS _ _ (dent_fine hU _)]; exact congr_arg₂ (·+·) rfl (tsum_congr fun i=>masked_eq _ _ _ _ (dent_fine hU _))
   unfold Coefficient.density; rw [Rep.eval,hh,Activities.gas_one R.activities R.p hx, mul_one, show (fun i=>P.marked R i U)=fun _=>0 from funext hm]; simp
section deGen
-- standardized wrap weights
variable {b k :ℕ}{I:Type}{Y:I→Support n}{p:BudgetPoint}{f:I → Config G n→ℂ}{u:I→ℝ}
lemma wound (X:Support n)(hx:o∈X)(h:10*(b*(4*p.B+2)+2*p.B) < n.val)(hi:¬Nonwrapping X o): b ≤ coverNumber p.B X:=by
   contrapose! hi; intro i hh; apply lt_of_le_of_lt _ h; apply Nat.mul_le_mul_left; apply (Corona.extent X p.B hh hx).trans; gcongr
lemma prime_fuel (h:10*(b*(4*p.B+2)+2*p.B) < n.val) {X:Support n}(hx:o∈X)(hi:¬Nonwrapping X o) (hw:0≤w): w ≤ Real.exp (-p.supportExponent*b)*p.mass X w:=by
   unfold BudgetPoint.mass; rw[← mul_assoc,← Real.exp_add]; have hv:=p.exponent_pos; apply le_mul_of_one_le_left hw; exact Real.one_le_exp (by rw [neg_mul]; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr (wound X hx h hi)) hv.le])
end deGen
end YM.PhysicalNext.Repeat.Quince
