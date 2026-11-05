import YM.RG08.Calendar.Base
/-!
 # log schedule → kyage
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Admission
open Set Function Filter Lattice Wilson Exterior Precision Laurent Next.Free RG RG.Supply Bloch Wings
open scoped BigOperators Topology Real Classical
variable {I H:Type} {G:Gauge}

lemma LambdaX_at {x:ℝ}(h:1<x): 2≤ LambdaX x:= le_add_of_nonneg_right (Real.log_pos h).le
lemma betaFraction (a:Levels G)(u v:ℕ) : a.clock.hatBeta u-a.clock.hatBeta v=G.slopeConstant*(a.S.scale u-a.S.scale v):=by unfold Calendar.hatBeta Levels.S; ring
private lemma subt (x y:ℝ) (hy:1≤ y)(hx:0<x): Real.log x-Real.log y ≤ max 0 (x-y):= by
   by_cases h:x≤y
   · exact (sub_nonpos.mpr (Real.log_le_log hx h)).trans (le_max_left ..)
   have H:0<y:=zero_lt_one.trans_le hy
   rw [max_eq_right (sub_nonneg.mpr (by linarith))]
   calc
     _ = Real.log (x/y) := (Real.log_div hx.ne' H.ne').symm
     _ ≤ x/y-1:= Real.log_le_sub_one_of_pos (by positivity)
     _ = (x-y)/y := by field_simp
     _ ≤ x-y := div_le_self (by linarith) hy
lemma z_at (a:Levels G)(i:ℕ): 1≤ z a i:= le_add_of_nonneg_right (Real.log_nonneg (by linarith [LambdaX_at (a.fits.delayed i)]: 1 ≤ LambdaX _))
lemma z_older (p:G.Simple)(a:Levels G)(m n:ℕ): z a m ≤ z a n + G.slopeConstant*|a.S.scale m-a.S.scale n| := by
   let Z := G.slopeConstant; have ht : 0≤Z:= (Gauge.slopeConstant_pos p).le
   let x:=LambdaX (a.clock.hatBeta m); let y:=LambdaX (a.clock.hatBeta n);
   have hx : 2 ≤ x:= LambdaX_at (a.fits.delayed m); have hy:2 ≤ y:= LambdaX_at (a.fits.delayed n)
   let D := |a.S.scale m-a.S.scale n|; have hd:0≤D:=abs_nonneg _
   have h:x-y≤ Z*D:= by
      simp only [x,y,LambdaX,add_sub_add_left_eq_sub]; apply (subt _ _ (a.fits.delayed _).le (zero_lt_one.trans (a.fits.delayed _))).trans
      apply max_le (mul_nonneg ht hd); rw [betaFraction]; exact mul_le_mul_of_nonneg_left (le_abs_self _) ht
   have hh:Real.log x-Real.log y ≤ Z*D:= (subt x y (by linarith) (by positivity)).trans (max_le (mul_nonneg ht hd) h)
   change 1+Real.log x≤ 1+Real.log y+Z*D; linarith
-- can pay with Lambda instead; z smaller for local mixed estimates
lemma z_small (a:Levels G)(i:ℕ): z a i ≤ LambdaX (a.clock.hatBeta i):= by
   let x:=LambdaX (a.clock.hatBeta i); change 1+Real.log x ≤ x
   have h:2≤x:= LambdaX_at (a.fits.delayed i)
   linarith [Real.log_le_sub_one_of_pos (by linarith:0<x)]
variable {w:I→Windows}{a:Levels G}
local notation "X"=> Chain.actual a

def NearZ (a:Levels G)(w:I→Windows):Prop:=∀ b, z a (w b).k ≤ (w b).Z
-- for auxiliary constant windows use abstract budget definition directly instead
lemma payable (p:G.Simple)(hV:NearZ a w): Weighed (Launch.farY X) (fun i:Launch w=> z a i.i):=by
   have hh:= Gauge.slopeConstant_pos p
   refine ⟨1+G.slopeConstant,1,by positivity,fun i=>⟨zero_le_one.trans (z_at ..),?_⟩⟩
   have hp:= (hV i.b); refine (z_older p a i.i (w i.b).k).trans ?_
   rw [pow_one]; unfold Launch.farY; let u:= |a.S.scale i.i-a.S.scale (w i.b).k|; let y:=(w i.b).Z
   have he:0≤y:= (w i.b).pos; have hz:0≤u:= abs_nonneg _; have hv:z a (w i.b).k≤y:=hp
   change _ +G.slopeConstant*u ≤ (1+G.slopeConstant)*(2+y+u); nlinarith
lemma Affords.cash_w (p:G.Simple)(hV:NearZ a w){N:Need}(hx:∀ k, Affords N a (w k).start) {f:Launch w→ℝ} (hB:∀ i,0≤ f i)(hQ:∀ i, f i ≤ N.cost _ _ ((Chain.actual a).step i.i (.top _)) (a.clock.params i.i)): Weighed (Launch.farY X) f:= (payable p hV).mono hB (fun i=> (hQ i).trans ((hx i.b).hi _ i.geC))

lemma eventual_requests {R:Type} [Encodable R] (a:Levels G) (w:R→Need)(h:∀ x n, Encodable.encode x ≤ a.clock.J n → Affords (w x) a n)(f:R→ℕ)(r:R): ∀ᶠ i in atTop,f r ≤ a.clock.J i∧ Affords (w r) a i := ((a.fits.deep.eventually (eventually_ge_atTop _)).and (a.fits.deep.eventually (eventually_ge_atTop _))).mono fun i hp=> ⟨hp.1,h _ i hp.2⟩
end YM.RG08.Admission
