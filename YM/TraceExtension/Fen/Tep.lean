import YM.TraceExtension.Fen.Measures
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {d k:ℕ}{σ A C q:ℝ}(R:Rep G n) (h:R.path.Bounds R.clip σ A C){I:Type}(b:I→Barley)
lemma clips_out (w:I→ℝ)(hw:∀ i,0 ≤ w i)(h:Summable w)(hv:0< q): ∀ᶠ L:Finset I in atTop, SumBudget (fun i=> if i∈L then 0 else w i) q:=by
    classical
    let D:=∑' i,w i
    filter_upwards [h.hasSum.eventually (Metric.ball_mem_nhds D hv)] with L hx
    let g(i):=if i∈L then 0 else w i; have hp': Summable g:=by
        refine Summable.of_nonneg_of_le (f:=w) (fun i=>?_) (fun i=>?_) h <;> unfold g <;> split <;> first| rfl| exact hw _
    refine ⟨fun i=> by change 0 ≤ if _ then _ else w i; split <;> first| exact hw _|exact le_rfl,hp',?_⟩
    have hp:D-(∑' i,g i)=∑ i∈L,w i:=by rw[show D= _ from rfl,← h.tsum_sub hp', tsum_eq_sum (s:=L)]; refine Finset.sum_congr rfl  (fun i hi=> by rw [show g i=0 from if_pos hi]; exact sub_zero _); intro i hi; rw [show g i=w i from if_neg hi]; exact sub_self _
    have hu := abs_le.mp (show |(∑ i∈ L,w i)-D| ≤ q from le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq] using hx)); change ∑' i,g i≤q; linarith only [hu.1,hp]
def rowAm (p:I):= port R (b p)
def rowL(p:I):= mote R (b p)
abbrev Pointed (q:ℝ) := fun p:I=> rowAm R b p*Real.exp (q*rowL R b p)
lemma purpose (A:ℝ)(he:SumBudget (Pointed R b σ) A)(hs:0<σ)(q:ℝ)(hq:0<q)(hq':q≤σ):∀ i:ℕ, SumBudget (fun k=> Pointed R b (σ-q) k*(1+rowL R b k)^i) (momentPrice i q*A):=by
   intro i; apply Cost.mono (Cost.scale he (momentPrice i q) (momentPrice_pos _ hq).le) (fun i=> ?_) (fun p=>?_)
   · exact mul_nonneg (mul_nonneg (ports_n R (b i)) (Real.exp_pos _).le) (by positivity)
   let Z:= rowAm R b p; let T:ℝ:= rowL R b p; have hz:0 ≤ Z:=ports_n R (b p)
   apply (mul_le_mul_of_nonneg_left (spendMoment i hq (show 0 ≤ T by positivity)) (show 0 ≤ Z*Real.exp ((σ-q)*T) by positivity)).trans_eq
   change Z*Real.exp _ * _ = momentPrice _ _ *(Z*Real.exp (σ*T)); rw [show σ*T=(σ-q)*T+q*T from by ring,Real.exp_add];ring
lemma coatout (p r:ℕ)(A q:ℝ)(hs:0<σ)(hp:SumBudget (Pointed R b σ) A)(he:0<q): ∀ᶠ L:Finset I in atTop, let c i:= i∈L ∧ rowL R b i≤r; SumBudget (fun i=> if c i then 0 else Pointed R b (σ/4) i*(1+rowL R b i)^p) (q+Real.exp (-(σ/4)*r)*(momentPrice p (σ/2)*A)):=by
    let V(i:I):=Pointed R b (σ/4) i*(1+rowL R b i)^p
    let W(i:I):=Pointed R b (σ/2) i*(1+rowL R b i)^p
    have ht:= purpose R b A hp hs (σ/2) (half_pos hs) (by linarith) p; rw [show σ-σ/2= σ/2 by ring] at ht
    have hv : SumBudget V (momentPrice p (σ/2)*A):=by
       apply Cost.mono (g:=W) ht (fun i=>mul_nonneg (mul_nonneg (ports_n R _) (Real.exp_pos _).le) (by positivity)) (fun i=>?_)
       change V i≤W i; unfold V W Pointed; gcongr; apply ports_n; linarith
    filter_upwards [clips_out V hv.1 hv.2.1 he] with L HL
    intro c; let Q:=Real.exp (-(σ/4)*r); have hh:= Extra.Multi.Budget.plus HL (Cost.scale ht Q (Real.exp_pos _).le)
    apply Cost.mono hh (fun i=>by change 0 ≤ if c i then _ else V i; split <;> first|exact hv.1 i|rfl) (fun i=> ?_); split <;> rename_i hc
    · exact hh.1 i
    by_cases hL:i∈ L
    · change V i≤ (if i∈L then 0 else V i)+Q*W i; rw [if_pos hL,zero_add]
      have hx : (r:ℝ)≤ rowL R b i:=Nat.cast_le.mpr (le_of_lt (lt_of_not_ge fun z=>hc ⟨hL,z⟩))
      unfold V W Pointed Q; rw [← mul_assoc (Real.exp _),mul_left_comm (Real.exp _) (rowAm R b i),← Real.exp_add]
      gcongr; apply ports_n; nlinarith only [hs,hx]
    change V i≤ (if i∈L then 0 else V i)+Q*W i; rw [if_neg hL]; exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (ht.1 _))
-- elevate payments based geometric
abbrev metal (p: Seat n × I):= officeC R p.1 (b p.2)
lemma centCost (x:Site n)(f:I→ℝ)(h:∀ i,0 ≤ f i)(hv:SumBudget (fun i=> f i*(1+rowL R b i)^4) A):
  SumBudget (fun i:Seat n×I=> if x∈ metal R b i then f i.2 else 0) (bankCost R.p.B*A):=by
    let g(i:I×Seat n):= if x∈officeC R i.2 (b i.1) then f i.1 else 0; have ht(i):0 ≤ g i:=by unfold g; split <;> first| exact h _|rfl
    refine Cost.equiv (f:=g) (Equiv.prodComm ..) (Cost.product (Cost.scale hv _ ?_) (fun i=> ?_)); rotate_left
    · refine ⟨fun j=> ht (i,j),Summable.of_finite,?_⟩; rw [tsum_fintype]; unfold g; rw [←sum_filter]; dsimp only; rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (swag R x (b i)) (h i)).trans_eq; unfold rowL; ring
    unfold bankCost; positivity
end YM.Trace.Fen
