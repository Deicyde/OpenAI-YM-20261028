import YM.RG08.Pill.Listen
/-!
# Reverse and common coefficients tariffs and weighted errors.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
variable {I:Type}{u:I→Windows}
section
-- B forced inverse subst. Vu powers charging.
private lemma inquest {A B:PowerSeries ℝ} (h : PowerSeries.subst (⨯*A) (⨯*B)=⨯)(hp : constantCoeff A=1)(he:n>0): coeff n B= - ∑ i∈range n, coeff i B * coeff (n-i) (A^(i+1)) := by
    have ha := congr_arg (coeff (n+1)) h
    rw [stencilSub,Finset.sum_range_succ'] at ha; simp only [coeff_succ_X_mul,pow_zero,coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul,add_zero,Nat.add_sub_add_right,coeff_X,if_neg (by omega:n+1≠1)] at ha
    rw [Finset.sum_range_succ,tsub_self] at ha; simp only [coeff_zero_eq_constantCoeff_apply,map_pow,hp,one_pow,mul_one] at ha; linarith
variable {y δ:I→ℝ}{F G A B:I→PowerSeries ℝ}
lemma power_paid (hk : ∀ i≤E, Lease y δ (fun x=> coeff i (A x)) (fun x=> coeff i (B x))) (hx:k≤E) (he : Audience y) (r) : Lease y δ (fun i=>coeff k ((A i)^r)) (fun i=> coeff k ((B i)^r)) := by
    have hh:= Lease.powerT (f:=fun i j=> coeff j (A i)) (g:=fun i j=> coeff j (B i)) he hk r _ hx
    have hX (X:PowerSeries ℝ) : PowerSeries.mk (fun j=> coeff j X)=X:=by ext k; rw [coeff_mk]
    simp_rw [powT,hX] at hh; exact hh
lemma reversePaid (hf : ∀ i,constantCoeff (F i)=1)(hg:∀ i,constantCoeff (G i)=1)(hA:∀ i,constantCoeff (A i)=1)(hB:∀ i,constantCoeff (B i)=1) (he:∀ i, PowerSeries.subst (⨯*A i) (⨯*F i)=⨯)(hp:∀ i, PowerSeries.subst (⨯*B i) (⨯*G i)=⨯) (hk : ∀ i≤E, Lease y δ (fun x=>coeff i (A x)) (fun x=>coeff i (B x))) (hh:k≤ E)(hz:Audience y): Lease y δ (fun i=> coeff k (F i)) (fun i=> coeff k (G i)) := by
    induction k using Nat.caseStrongRecOn with
    | zero=> simp only [coeff_zero_eq_constantCoeff_apply,hf,hg]; exact Lease.const ..
    | ind k ih=>
        simp_rw [fun i=> inquest (he i) (hA _) (show k+1>0 from Nat.succ_pos _),fun i=>inquest (hp i) (hB _) (show k+1>0 from Nat.succ_pos _)]
        have hv j (hj:j≤k): Lease y δ (fun i=> coeff j (F i)*coeff (k+1-j) (A i^(j+1))) (fun i=> coeff j (G i)*coeff (k+1-j) (B i^(j+1))) := (ih _ hj (by omega)).times (power_paid hk (by omega) hz (j+1)) hz
        refine cast ?_ (Lease.times (Lease.const y δ (-1)) (Lease.lists (s:=range (k+1)) (fun j i=> coeff j (F i)*coeff (k+1-j) (A i^(j+1))) _ hz (fun j hj=> hv _ (mem_range_succ_iff.mp hj))) hz)
        congr 1 <;> funext i <;> simp -- η
lemma rounds (h: ∀ i≤k,Lease y δ (fun j=> coeff i (F j)) (fun j=> coeff i (G j))) (he : ∀ i≤k,Lease y δ (fun j=> coeff i (A j)) (fun j=> coeff i (B j))) (hp:Audience y) : Lease y δ (fun i=> coeff k (PowerSeries.subst (⨯*A i) (F i))) (fun i=> coeff k (PowerSeries.subst (⨯*B i) (G i))) := by
  simp_rw [stencilSub]; apply Lease.lists; exact hp
  intro i hi; exact (h i (mem_range_succ_iff.mp hi)).times (power_paid he (Nat.sub_le ..) hp i) hp
end
local notation "●" => (fun i:Roam u=>i.measure X)
local notation "⧫" => (fun i:Roam u=> i.cost X)
variable (ht:Tights T S ν D' u)
include ht
lemma carriers (hk:k≤E) : Lease ● ⧫ (fun i=> coeff k (afternoons (rootsRatio X ν D' i.N i.main i.i))) (fun i=> coeff k (afternoons (rootsRatio X ν D' i.M i.main i.i))) := by
    have hp N i k : constantCoeff (afternoons (rootsRatio X ν D' N i k))=1:= by unfold afternoons; simp [mat_zero]
    have he N i k: PowerSeries.subst (ladder X ν D' N k i) (ladder X ν D' N i k)=⨯:= (global ..).trans notary
    exact reversePaid (fun _=> hp ..) (fun _=> hp ..) (fun _=> hp ..) (fun _=> hp ..) (fun i=> he ..) (fun i=> he ..) (fun i hi=> prices_come ht.hc ht.hv ht.hz ht.hs hi) hk (fun _=> sh X _)
-- Evaluate common v of either type, ratio as needed
lemma classPaid {V W:Roam u→Native (Letter F)} (hv: ∀ i≤E,∀ j,Lease ● ⧫ (fun x=> coeff i (V x j)) (fun x=> coeff i (W x j))) (hk:k ≤ E) b: Lease ● ⧫ (fun i=> coeff k (forward X ν D' i.N i.i i.main (V i) b)) (fun i=> coeff k (forward X ν D' i.M i.i i.main (W i) b)) := rounds (fun j hj=> hv j (hj.trans hk) b) (fun j hj=> carriers ht (hj.trans hk)) fun i=>sh X _
end YM.RG08.Pill
