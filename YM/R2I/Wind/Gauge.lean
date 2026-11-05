import YM.R2I.Wind.Penny
/-!
# Correcting projection disparity with an actual wound-family patch (flag sensitive).

Send K correction **as soft stake**, preserving all eligibility rules and letting it connect to the actual compulsory shelves later. Wind-powered suppression still needed to *buy*. Correction after Hess redistribution and from the Treasury cut; can't pass through as a priceable (+3) roster (don't consume this estimate with tune_pilot).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Wind
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
open PhysicalNext.Repeat Collection Anchor Next.Foundations
open Next.Scheduling Quotes RG.Supply Push.AbsoluteSums Footprint
open Progress.DirectedRecipe Payments Ovens Extra.Iteration
variable {G:Gauge}{n:Side}{P:BudgetPoint}{X:Support n}{a b:ℝ}
structure Lease (P:BudgetPoint) (n:Side) where
    garden: Support n
    yard: halo 2 ({0}:Support n) ⊆ garden
    pier: ¬ Nonwrapping garden 0
    size: coverNumber P.B garden ≤ brake P.B n+81
lemma hires (hn:20<n.val)(h:2≤P.B): Nonempty (Lease P n):= by obtain ⟨X,h,hp,hg⟩:=cope hn h; exact ⟨⟨X,h,hp,hg⟩⟩
namespace Lease
variable (u:Lease P n)
local notation "B" => u.garden
lemma center : (0:Site n) ∈ u.garden:= u.yard (halo_subset _ _ (mem_singleton_self _))
def place (s:Seat n):= s.spread u.garden
def placement (s:Seat n):=s.reg u.garden u.center
-- strip exactly balancing heads coefficient. Always distribute Seats for isotropy only.
abbrev just (i j:PlaqAxes): ℝ:=if i=j then 1 else 0
def heart (o:Site n)(V:Config G n):= (∑ a,‖petals V o a‖^2)/2
lemma heart_eq (o: Site n): heart (G:=G) o=counter just o:= by
   ext1 U; simp [heart,counter,quad,just,ite_mul]
@[simp] lemma heart_at_one (o:Site n): heart (G:=G) o 1=0:= by rw [heart_eq]; simp [counter,quad]
lemma heads_shape (s:Seat n)(V:Config G n): heads P 0 (s.view V)=heads P s.2 V:= by
  have h' : s.spread {0} = {s.2} := by unfold Seat.spread; simp [affine]
  have ht:= s.healthy P.threshold {0} V; rw [h'] at ht
  by_cases hv : Healthy P.threshold {s.2} V
  · rw [heads,masked_eq _ _ _ _ (ht.mp hv), heads, masked_eq _ _ _ _ hv]
    rw [Seat.view,petals_moves]; simp only [affine,Signed.act_zero,zero_add,reframe_norm]; rw [Equiv.sum_comp _ (fun i => ‖petals V s.2 i‖^2)]
  simp [heads, masked_ne _ _ _ _ (mt ht.mpr hv), masked_ne _ _ _ _ hv]
-- sign: want +a *∑ heads, β loaded with ∆ discrep `a`. Add negative E carry. ℒ=(masked X heart diff) run.
variable (G) in
def tollG (P:BudgetPoint) := (2:ℝ)⁻¹*((Fintype.card PlaqAxes):ℝ)* pairBill G P
lemma tollG_nonneg : 0≤ tollG G P:= by unfold tollG; have h:=pair_nonneg G P; positivity
lemma quoteH (o:Site n): Bill P o (Healthy P.threshold {o}) (tollG G P * P.threshold^2) (Lease.heart (G:=G) o):= by
   rw [heart_eq]; convert (counter_bill o Lease.just P) using 1; unfold just tollG; simp_rw [apply_ite (fun x:ℝ=>|x|)] -- check
   simp_rw [abs_one,abs_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq]; simp; ring
variable (a)
def rayH (a:ℝ)(V:Config G n):= -(factor * a)* heart 0 V
def stem (s:Seat n): Pot G n:= rayH a ∘ s.view
def patchK (V:Config G n):ℝ:= if Healthy P.threshold B V then 0 else factor*a*heads P 0 V
def twig (s:Seat n): Pot G n:= (u.patchK a) ∘ s.view
set_option quotPrecheck false
local notation "t" => P.threshold
lemma bud_balances (s:Seat n) (V:Config G n): -masked t (u.place s) (stem a s) V + u.twig a s V=factor*a*heads P s.2 V:= by
   unfold twig stem place; rw [s.distribute, ← heads_shape s]
   simp only [comp_apply,patchK]; split <;> rename_i he
   · rw [masked_eq _ _ _ _ he]; change -( - (_*_) * _)+0 = _*_*masked t {0} (heart 0) _; rw [masked_eq _ _ _ _ (healthy_mono (singleton_subset_iff.mpr u.center) he)]; ring
   rw [masked_ne _ _ _ _ he]; ring
lemma stems_reg (s:Seat n): P.Regular (u.place s) (stem a s (G:=G)):= by unfold stem rayH; apply Seat.regular; refine CouplingShape.reg_scale _ ?_; rw [heart_eq]; exact reg_larger (counter_regular _ _ P) u.yard
lemma stems_norm (s:Seat n): P.supBounds s.2 (u.place s) (stem a s (G:=G)) (turnFee P * (|a| *(tollG G P*t^2))) := by
   refine sup_le (Seat.sup s (CouplingShape.reg_scale (-(factor*a)) (reg_larger (show P.Regular (halo 2 ({0}:Support n)) (heart (G:=G) 0) by rw [heart_eq]; exact counter_regular ..) u.yard)) (Bill.sup (Bill.mul_left _ (quoteH _)) (fun U h=> healthy_mono (singleton_subset_iff.mpr u.center) h))) (?_)
   rw [abs_neg,abs_mul,abs_of_pos factor_pos]; apply mul_le_mul_of_nonneg_left _ (turnFee_pos P).le; exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) factor_le) (mul_nonneg tollG_nonneg (sq_nonneg t)))
lemma stems_one (s:Seat n) : stem (G:=G) a s 1=0:= by unfold stem Seat.view; rw [comp_apply,pull_one_field,rayH,heart_at_one,mul_zero]
lemma stems_wound (s:Seat n) : Wound (u.placement s):= fun h=> u.pier (Seat.unwrapped s h)
lemma twigs_zero (s:Seat n)(V:Config G n) (hV:Healthy t (u.place s) V): u.twig a s V=0:= by unfold twig patchK; apply if_pos ((s.healthy ..).1 hV)
lemma twigs_tidy (s:Seat n): Trio.Tidy P (u.place s) (u.twig a s (G:=G)):= by
   have hp : P.Regular u.garden (heart (G:=G) 0) := heart_eq (G:=G) (0:Site n) ▸ reg_larger (counter_regular _ _ P) u.yard
   have hT : Measurable (heart (G:=G) (0:Site n)):= hp.borel
   let f := Lease.heart (0:Site n) (G:=G)
   let g := heads (G:=G) (n:=n) P 0
   have he : Trio.Tidy P u.garden (u.patchK (G:=G) a):= by
     refine ⟨fun U V hh hv=>?_, Measurable.ite (healthy_closed ..).measurableSet measurable_const ((masked_measurable _ {0} _ hT).const_mul _),?_⟩
     · have hx:= healthy_reads t _ _ (singleton_subset_iff.mpr u.center) U V hh hv; have h := hp.sites _ _ hh
       have hf:g U=g V:=by
         unfold g heads; by_cases hs : Healthy t {0} V
         · rw [masked_eq _ _ _ _ (hx.symm ▸ hs),masked_eq _ _ _ _ hs]; exact h
         rw [masked_ne _ _ _ _ (hx.symm ▸ hs),masked_ne _ _ _ _ hs]
       unfold patchK; rw [healthy_reads t _ _ (Finset.Subset.refl _) U V hh hv]; simp_rw [show heads P 0 U=heads P 0 V from hf]
     intro l U; let V:= Lattice.gauge l U; have hv: flags t V=flags t U:= gauge_flags ..; have hh:= hp.symmetry l U
     have hx:g V=g U := by
        change masked _ _ f _=masked _ _ f _; by_cases he:Disjoint ({0}:Support n) (flags t U)
        · rw [masked_eq t {0} f V (by unfold Healthy; rw [hv]; exact he),masked_eq _ _ _ _ he]; exact hh
        rw [masked_ne t {0} f V (by unfold Healthy; rw [hv]; exact he),masked_ne _ _ _ _ he]
     unfold patchK; rw [show heads P 0 (Lattice.gauge l U)=_ from hx]; simp only [Healthy,gauge_flags]; congr
   exact ⟨Push.Local.uses_pull (he.uses) _ _, he.borel.comp (continuous_pull ..).measurable, Push.Local.invariant_pull he.invariant _ _⟩
lemma twigs_norm (s:Seat n)(V:Config G n): ‖u.twig a s V‖ ≤ |a| *(tollG G P*t^2):= by
   unfold twig patchK; dsimp only [Function.comp_apply]; have ht:= tollG_nonneg (G:=G) (P:=P); split <;> rename_i he
   · rw [norm_zero]; positivity
   rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos factor_pos]; apply mul_le_mul (mul_le_of_le_one_left (norm_nonneg a) factor_le) _ (norm_nonneg _) (abs_nonneg _)
   by_cases h:Healthy t {0} (s.view V); · rw [heads,masked_eq _ _ _ _ h]; exact Bill.norm (quoteH _) (l:=[]) (by simp) (by simp) h
   rw [heads,masked_ne _ _ _ _ h,norm_zero]; positivity
end Lease
end YM.AnalyticBridge.VerifiedReset.Averaging.Wind
#print axioms YM.AnalyticBridge.VerifiedReset.Averaging.Wind.Lease.stems_norm
