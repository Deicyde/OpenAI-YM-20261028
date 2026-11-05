import YM.TraceExtension.Fen.Wails
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine AnalyticNext.QuarticMatch.Estimate
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}(R:Rep G n){I:Type}(b:I→Barley) {k:ℕ}{σ A D C:ℝ}
lemma pumpkin (σ:ℝ) (hs:0≤σ)(p: I→Prop)[DecidablePred p]{q:ℝ}{f:ℕ→ℝ}(hf:∀ i,0 ≤ f i)(Q:ℕ)(Z:ℝ)(hZ:1≤ Z)(H:∀ i,f i≤ Z*(1+i)^Q)(e:Lines G n 1)
 (hp:SumBudget (fun i:I=>if p i then Pointed R b σ i*(1+rowL R b i)^(Q+4) else 0) q):
    SumBudget (fun i:Seat n×I=> if p i.2 then upLand R b e i*f (mote R (b i.2)) else 0) (bankCost R.p.B*(Z*q)):=by
   let F(i:I):=if p i then rowAm R b i*f (rowL R b i) else 0
   have ht(i:I):0 ≤ F i:=by unfold F; split; exact mul_nonneg (ports_n R _) (hf _); rfl
   have he: ∀ i:Seat n×I,(if p i.2 then upLand R b e i*f (mote R (b i.2)) else 0)=if e.1∈ metal R b i then F i.2 else 0 :=by
      intro i; unfold upLand F; split_ifs <;> simp_all[rowL, rowAm,Tar]
   simp_rw [he]
   refine centCost R b e.1 F ht (Cost.mono (Cost.scale hp Z (by positivity)) (fun i=>mul_nonneg (ht i) (by positivity)) fun i=>?_)
   by_cases h:p i
   · simp only [h,if_true,F]; unfold Pointed; let D:ℝ:= rowL R b i
     refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show rowAm R b i ≤ rowAm R b i*Real.exp (σ*D) from le_mul_of_one_le_right (ports_n R _) (Real.one_le_exp (by positivity))) (by positivity)) (by positivity)); rw[pow_add]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (H _) (ports_n R (b i))) (show 0 ≤ (1+D)^4 by positivity)).trans_eq; unfold D rowAm; ring
   simp [h,F]
lemma waves {G:Gauge}: ∀ k:ℕ, ∃ f:ℕ→ℝ, MarksP f ∧∀ (I:Type)(b:I→Barley)(n:Side)(R:Rep G n), 2 ≤ R.p.B → ∀ (i:Seat n×I)(e:Lines G n 1),Allows k (outD (seatP R b i) e ∘ input G n) 0 (upLand R b e i*f (mote R (b i.2))):=by
    intro k; obtain ⟨B,hB,H⟩:=armsP (k+1) G 0 le_rfl; obtain ⟨f,hf,h⟩:=peach G B k hB
    exact ⟨f,hf,fun I b n R hB i e=> h _ I b R hB (input G n) 0 (H n 0 (by simp)) i e⟩
variable (L:Finset I) {q A:ℝ}
def piste:= ∑ j:Seat n,∑ i∈L,seatP R b (j,i)
abbrev spikes(r:ℕ):=L.filter fun j=> rowL R b j ≤ r
def ski (L:Finset I)(r:ℕ):= piste R b (spikes R b L r)
private lemma exact_v (p:Seat n×I)(Z:Config G n): ContDiffAt ℝ ω (fun y=>seatP R b p (input G n y * Z)) 0:=lick R b p _ _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park Z _))
lemma slopeD(V:Config G n): DifferentiableAt ℝ (fun y=>piste R b L (input G n y*V)) 0:=by
    simp only[piste,Finset.sum_apply]; exact ((ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun k h=> exact_v R b (i,k) V))):ContDiffAt ℝ ω _ _).differentiableAt (by simp)
lemma overlook (e:Lines G n 1): outD (piste R b L) e=∑ p∈(univ (α:=Seat n) ×ˢ L),outD (seatP R b p) e:=by
    ext1 U; unfold outD piste; simp only [Finset.sum_apply]; rw[fderiv_fun_sum (x:= (0:Link G n)) (𝕜:=ℝ)]; simp only [_root_.sum_apply]; rw[sum_product]; apply Finset.sum_congr rfl fun s _=>?_; rw[fderiv_fun_sum]; simp only [_root_.sum_apply]; intro i _; exact (exact_v R b (s,i) U).differentiableAt (by simp)
    intro i _; exact (ContDiffAt.sum (n:=ω) (fun k _=> exact_v R b (i,k) U)).differentiableAt (by simp)
end YM.Trace.Fen
