import YM.RG08.Scale.Path
/-!
# Tangent branch: use g, normalization g_k. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Conductor
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Push.AbsoluteSums UVExtension.Free PowerSeries Stationary
open scoped BigOperators Topology Real Classical
variable {I : Type} {y δ : I→ℝ} {r s : ℕ}
-- solve M.M unit. all coefficients ordinary
private def walls (f : Cues) (n:ℕ) := ∑ j∈wheel (n+1), if j.1=0 ∨ j.2=0 then 0 else f j.1*f j.2
private lemma walls_local {f g:Cues}(h:∀ i≤r, f i=g i): walls f r=walls g r:= by apply sum_congr rfl; intro i hi; have he:=mem_antidiagonal.mp hi; split; rfl; next hp=> rw [h,h] <;> omega
private lemma wall_coeff (f:Cues)(hp:f 0=1)(n:ℕ) : coeff (n+1) (PowerSeries.mk f ^ 2) = 2*f (n+1)+ walls f n:= by
  rw [sq,coeff_mul]; unfold walls
  let k:= n+1
  let t:=wheel k
  have hb i (h:i∈t) : f i.1*f i.2= ((if i=(k,0) then f k else 0)+(if i=(0,k) then f k else 0))+(if i.1=0 ∨ i.2=0 then 0 else f i.1*f i.2) := by
    by_cases he:i=(k,0); · rw [he]; simp [k,hp]
    by_cases hy:i=(0,k); · rw [hy]; simp [k,hp]
    simp only [he,hy, ↓reduceIte]; have hh:= mem_antidiagonal.mp h
    rcases i with ⟨x,v⟩; simp only [Prod.mk.injEq] at he hy hh ⊢; rw [if_neg (by omega)]; ring
  simp only [coeff_mk]
  calc
    _ = ∑ i∈ t, (((if i=(k,0) then f k else 0)+(if i=(0,k) then f k else 0)) +(if i.1=0 ∨ i.2=0 then 0 else f i.1*f i.2)) := sum_congr rfl hb
    _ = _ := by rw [sum_add_distrib,sum_add_distrib]; simp [t,k,two_mul,wheel] -- simplifier works?

def matinee (f:Cues) (n:ℕ) : ℝ:= match n with
 | 0=>1
 | n+1=> (f (n+1)-walls (fun j=> if j<n+1 then matinee f j else 0) n)/2
termination_by n
decreasing_by all_goals omega
lemma mat_zero (f:Cues): matinee f 0=1:= by rw [matinee]
lemma mat_step (f:Cues) (n):matinee f (n+1)=(f (n+1)-walls (matinee f) n)/2:= by rw [matinee,walls_local (f:=fun j=> if j<n+1 then matinee f j else 0) (g:=matinee f) (by intro i hi; rw [if_pos]; omega)]
lemma dawn (f:Cues)(h:f 0=1): PowerSeries.mk (matinee f)^2=PowerSeries.mk f:= by
   ext i; cases i with
   | zero=> simp [mat_zero,h,pow_succ]
   | succ n=> rw [wall_coeff _ (mat_zero _) n,coeff_mk, mat_step]; ring
lemma mat_unique {g f:Cues}(h:g 0=1)(hg:PowerSeries.mk g ^ 2=PowerSeries.mk f) : matinee f=g := by
   ext i; induction i using Nat.caseStrongRecOn with
   | zero=> rw [mat_zero,h]
   | ind n ih=> rw [mat_step,walls_local ih,← show coeff (n+1) (PowerSeries.mk f)=f (n+1) from coeff_mk .., ← hg,wall_coeff _ h]; ring
lemma Lease.mat {A B:I→Cues}(h : ∀ i≤r, Lease y δ (fun j=> A j i) (fun j=> B j i)) (he : Audience y) : Lease y δ (fun i=> matinee (A i) r) (fun i=>matinee (B i) r) := by
   induction r using Nat.caseStrongRecOn with
   | zero=> simp_rw [mat_zero]; exact Lease.const ..
   | ind n ih=>
     let F (V : I→ Cues)(p:ℕ×ℕ)(i:I):= if p.1=0 ∨ p.2=0 then 0 else matinee (V i) p.1 * matinee (V i) p.2
     have hp : Lease y δ (fun i=> walls (matinee (A i)) n) (fun i=> walls (matinee (B i)) n) := by
       refine Lease.lists (F A) (F B) he (fun i hi=> ?_); unfold F
       split; exact Lease.const ..; next hh=>
         have hx:= mem_antidiagonal.mp hi
         exact (ih _ (by omega) (fun i hi=>h _ (by omega))).times (ih _ (by omega) (fun i hi=>h _ (by omega))) he
     have ht := Lease.times hp (Lease.const _ _ (-1)) he
     have hP := ((h _ le_rfl).plus ht he).times (Lease.const _ _ (2:ℝ)⁻¹) he
     simp_rw [mat_step,div_eq_mul_inv,sub_eq_add_neg]; convert hP using 1 <;> ext i <;> simp
abbrev afternoons (V : Cues) := PowerSeries.expand 2 (by decide) (PowerSeries.mk (matinee V))
-- receipt for measuring formal g_i at g_k
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g : KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}{u:I→Windows}

def ladder (X : Chain)(ν:G.ColorIndex)(D:ChartRatio G)(N i k) := PowerSeries.X * afternoons (rootsRatio X ν D N i k)
lemma fuel (N i k:ℕ): ladder X ν D N i k ^ 2 = PowerSeries.expand 2 (by decide) (Span (rootsRatio X ν D N i k)):= by simp only [ladder,Span,map_mul,expand_X,afternoons,← dawn (rootsRatio X ν D N i k) (rooted_unit ..),map_pow,mul_pow]
lemma prices_come (h:Circuit S ν D u)(hp:X.Wake G)(he:LocalRatio D)(hα:G.Simple)(hr:r≤ E): Lease (fun i:Roam u=>i.measure X) (fun i=> i.cost X) (fun i=> coeff r (afternoons (rootsRatio X ν D i.N i.i i.main))) (fun i=> coeff r (afternoons (rootsRatio X ν D i.M i.i i.main))) := by
   simp only [afternoons,coeff_expand,coeff_mk]
   by_cases hh : 2 ∣ r
   · simp only [hh,↓reduceIte]; exact Lease.mat (fun i hi=> tolls_paid h hp he hα (hr:=by omega)) (fun i=> Wings.sh X _)
   simp only [hh,↓reduceIte]; exact Lease.const ..
-- standard sign of inverse-square. a=t² f
lemma reporting_ratio (N i k) : let S:= ladder X ν D N (i+1) k; let U := ladder X ν D N i k
    S ^ 2= U ^ 2 * PowerSeries.subst (S^2) (PowerSeries.mk (slag X ν D N i)):= by
  intro S U; unfold S U
  apply Eq.trans (fuel ..) _
  conv_lhs=> rw [show Span (rootsRatio X ν D N (i+1) k)= _ from across_all N i k,map_mul]
  rw [fuel,fuel]
  apply congr_arg _ (PowerSeries.expand_subst (S:=ℝ) (f:=Span (rootsRatio X ν D N (i+1) k)) 2 (by decide) spanning _) -- parameter type
end YM.RG08.Conductor
