import YM.RG08.Pill.Reams
/-!
# Moment-only market and diagonal gain. Includes softened η for unslotted continuation.
Root-length budget on true supports.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ} {R σ θ η w A B C:ℝ} {v:ℝ}{L: Side}
variable {I J Y α β γ:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
def tailP (k:ℕ)(v:ℝ)(i:Beads α r):= (1+v*girth i)^k -- addresses stay same fixed section ball
abbrev cis (k:ℕ)(v:ℝ)(U:Quire.Rooted Y α r)(C:ℝ):= Quire.Ink (tailP k v) U C
lemma tailp (h:0≤v): 1≤ tailP k (r:=r) (α:=α) v := fun i=> one_le_pow₀ (le_add_of_nonneg_right (by positivity))
lemma root_size (x:Beads α r)(i): size (x i).1 ≤ girth x:= single_le_sum (fun i _=>Nat.zero_le (size (x i).1)) (mem_univ i)
private lemma heap_size (x:Beads α r)(z:Site L): (girth (carpet z x):ℝ) ≤ 4*(r:ℝ) + (L.val:ℝ)⁻¹ * girth x := by -- missing binder L
   unfold girth; rw [Nat.cast_sum,Nat.cast_sum]
   have ht: 4*(r:ℝ)=∑ _i:Fin r,(4:ℝ):= by simp; ring
   rw [ht,mul_sum,← sum_add_distrib]; exact sum_le_sum fun i _=> centerd z _
lemma heel (x:Beads α r)(z:Site L)(hp:0≤η)(hw:η≤1)(he:η/L.val≤σ): tailP k η (carpet z x) ≤ (1+4*(r:ℝ))^k * tailP k σ x := by
   have hs:0≤σ:=(div_nonneg hp (by positivity)).trans he
   unfold tailP; rw [←mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _
   let b := 4*(r:ℝ); let c:=((L.val:ℝ)⁻¹)
   have hZ : b≥0:= by unfold b; positivity
   have hz := (mul_le_mul_of_nonneg_right hw hZ); have ht : η*c≤σ:= by simpa only [c,div_eq_mul_inv] using he
   nlinarith only [hz,mul_le_mul_of_nonneg_left (heap_size x z) hp, mul_le_mul_of_nonneg_right ht (show 0≤ (girth x:ℝ) by positivity), show 0≤ b*(σ*girth x) by positivity]
lemma shift_priceM (x:Beads α r) (v: Beads β r)(z:Beads γ r)(h:∀ i,(x i).1=(v i).1+(z i).1) (hp:0 ≤ η)(he:η ≤ 1): tailP k η x ≤ tailP k η v * mint k z:= by
   have hx : (girth x:ℝ)≤ girth v+(girth z:ℝ):= by
      exact_mod_cast (show girth x ≤ girth v+girth z from by unfold girth; rw [← sum_add_distrib]; apply sum_le_sum; intro i _; rw [h]; exact size_add ..)
   have hb : η* (girth z:ℝ) ≤ girth z:= mul_le_of_le_one_left (by positivity) he
   unfold tailP
   apply le_trans _ (mul_le_mul_of_nonneg_left (lower_bill z k) (by positivity))
   rw [← mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _; nlinarith only [mul_le_mul_of_nonneg_left hx hp,hb,show 0≤(η*girth v)*girth z by positivity]
lemma rideP {f:α→ℝ}(g:α→ℝ)(hu:Charge g f A)(hp : Y): Quire.Ink g (fun i=> (f i) • hp) (A*‖hp‖):= by
   rw [mul_comm]; unfold Quire.Ink; apply cast _ (budget_scale (norm_nonneg hp) hu); congr 1; funext i; rw [norm_smul]; ring
-- total row tasks pay curvature shifts by polynomial offers
lemma bulb_charge (P:Fin r→Paper α β)(v:Fin r→Cover×β→ℝ)(x: Beads α r)(C:Fin r→ℝ)(h:∀ i,Charge (v i) (P i (x i)) (C i)): Charge (fun y:Beads β r=>∏ i,v i (y i)) (fun i=> bulb P (x,i)) (∏ i,C i) := by
  unfold bulb Charge; simp_rw [norm_prod,←prod_mul_distrib]; exact budget_fin_prod _ h

variable [Fintype β]
lemma waysP {P:Cross L α β}(hv : P.strip θ A)(hp:0<θ)(v:Beads α r)(p:Site L)(hw: 0≤η)(hη:η ≤ 1)(hk:η/L.val ≤ σ) :
    Charge (tailP k η) (fun i=>bulb (fun _=>node p P) (v,i)) ((1+4*(r:ℝ))^k * tailP k σ v * ((θ⁻¹^k*(k.factorial:ℝ)*Real.exp θ)*(Fintype.card β*A))^r) := by
  let Q j (y:Cover×β):= dime k (y.1-carry p (v j).1)
  let C:= (θ⁻¹^k*(k.factorial:ℝ)*Real.exp θ); let B:= (Fintype.card β:ℝ)*A
  have hc:0≤C:= by unfold C; positivity
  have ht(j:Fin r): Charge (Q j) (node p P (v j)) (C*B) := by
    apply budget_mono (budget_scale hc (node0 hv p (v j))) (fun i=> mul_nonneg (Carrier.liftCost_pos ..) (norm_nonneg _)); intro i
    let y:=i.1-carry p (v j).1; have hx:dime k y≤ C*Real.exp (θ*size y) := by
      apply le_trans (polynomial_price hp (show 0≤ 1+(size y:ℝ) by positivity) k); unfold C; rw [mul_add,mul_one,Real.exp_add]; linarith
    apply (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq; ring
  let W := (1+4*(r:ℝ))^k * tailP k σ v; have hs : 0≤σ:=(div_nonneg hw (by positivity)).trans hk
  have hW:0≤ W:= by unfold W tailP; positivity
  have he':= budget_scale hW (bulb_charge _ Q v (fun _=> C*B) ht); rw [prod_const,card_univ,Fintype.card_fin] at he'
  refine budget_mono he' (fun i=>mul_nonneg (show 0≤tailP k η i from zero_le_one.trans (tailp hw i)) (norm_nonneg _)) fun i=> ?_
  let F (j:Fin r): Cover×β:= ((i j).1-carry p (v j).1,(i j).2)
  have hz : tailP k η i ≤ W*mint k F := (shift_priceM i (carpet p v) F (fun j=> by unfold carpet F; dsimp only; abel) hw hη).trans (mul_le_mul_of_nonneg_right (heel v p hw hη hk) (mint_pos _ _ _ _))
  apply (mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans_eq; unfold mint F Q; ring
end YM.RG08.Run
