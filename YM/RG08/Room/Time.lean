import YM.RG08.Room.Kettle

/-!
# Nonlinear volume comparison via velocity path, arbitrary finite diagram regulator
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I : Type}[Fintype I]
namespace Haze
 set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000
variable (H:Haze I)

private lemma wtime (i:I)(p:Inn I): wick H.price (pderiv i p)=pderiv i (wick H.price p):=by
 have hs(i j:I)(p:Inn I):pderiv i (pderiv j p)=pderiv j (pderiv i p):=by
   induction p using MvPolynomial.induction_on with
   | C=>simp
   | add _ _ hi hj=>simp only [map_add,hi,hj]
   | mul_X p k h=>simp only [pderiv_mul,map_add,pderiv_X,Pi.single_apply,apply_ite,pderiv_one,map_zero,h];split_ifs <;> simp only [mul_one,mul_zero,add_zero] <;> try abel
 have he(p:Inn I):radiator H.price (pderiv i p)=pderiv i (radiator H.price p):=by
   simp only [radiator,slab_do,axes,map_sum,Derivation.map_smul]
   apply Finset.sum_congr rfl;intro j _; apply Finset.sum_congr rfl;intro k _;rw [hs k i,hs j i]
 have hg(k:ℕ):gust H.price k (pderiv i p)=pderiv i (gust H.price k p):=by
   unfold gust;rw [Derivation.map_smul];congr 1
   induction k with
   | zero=>rfl
   | succ k hh=>rw [iterate_succ_apply',hh,he,iterate_succ_apply']
 obtain ⟨n,hn⟩:=halts H.price H.flipped p
 rw [wick_budget hn,wick_budget (Γ:=H.price) (p:=pderiv _ _) (n:=n) (fun k hk=>by rw [hg,hn k hk,map_zero]),map_sum];simp_rw [hg]

lemma brew_pin {s:I}(hs:s∉H.foam)(p:Port I): pin s (H.brew p)=H.brew (pin s p):=by
 ext e :1;change tap _ _=tap _ _; rw [brew_view]; unfold tap; rw [flight_apply,flight_apply]
 simp_rw [← show tap e (H.brew p)=PowerSeries.coeff e (H.brew p) from rfl,brew_view]
 let b:=tap e p
 have ht(q:Inn I):pderiv s (aeval H.stop q)=aeval H.stop (pderiv s q):=by induction q using MvPolynomial.induction_on with
 | C=>simp
 | add _ _ hi hj=>simp only [map_add,hi,hj]
 | mul_X p k h=>
   have hx:pderiv s (aeval H.stop (X (R:=ℝ) k))=aeval H.stop (pderiv s (X (R:=ℝ) k)):=by
      rcases eq_or_ne s k with hz|hz
      · subst k; simp [stop,hs]
      rw [pderiv_X_of_ne (by exact Ne.symm hz),map_zero,aeval_X]; unfold stop;split_ifs
      · simp
      exact pderiv_X_of_ne (by exact Ne.symm hz)
   simp only [map_mul,pderiv_mul,h,hx,map_add]
 change pderiv s (aeval H.stop (wick _ b))=aeval H.stop (wick _ (pderiv s _)); rw [ht,H.wtime]

/-- Compare a moving positive-order formal density with its Jacobian; *before* taking log or
Markov denominator. Neglected heat exponent Q centered or shifted (use Boil here centered).
-/
theorem bottle {s:I}{P:I→I→ℝ}{Q:Inn I}{x:I→Port I}
    (hs:s∉H.foam)(hz:Near x)(ho:anchored H.foam x)(hb:H.Boil P Q)
    (F:Port I)(hf:pin s F=0)(hq:pin s (liftInn Q)=0) (hu:tiny F):
    pin s (H.brew (rise (belt x F+belt x (liftInn Q)-liftInn Q)*(gate x).det))=0:=by
 obtain ⟨v,hv,hV⟩:=velvet _ hz ho s
 let K:=(liftInn Q : Port I)
 let A:=belt x F+belt x K-K
 let E:=rise A
 let L:=(gate x).det
 let M:=E*L
 have hA:tiny A:=by
    unfold A tiny at *; rw [map_sub,map_add]; change tap 0 (belt x F)+tap 0 (belt x K)-_=0
    simp_rw [rim,show (fun i=>tap 0 (x i))=(fun i=>MvPolynomial.X (R:=ℝ) i) from funext hz];simp [tap,hu,K,liftInn]
 have hr(g:Derivation ℝ (Inn I) (Inn I)) : flight g E=E*flight g A:=lift_rise g hA
 have hX:gustaway s v E=E*gustaway s v A:=by
   simp only [away,pin,hr,mul_sub,Finset.mul_sum];apply congrArg₂ (·-·) rfl;apply Finset.sum_congr rfl;intro i _;ac_rfl
 have hd:gustaway s v A=drag v K:=by
   unfold A;rw [map_sub,map_add,changed hv,changed hv,hf,show pin s K=0 from hq,map_zero,zero_add,away,show pin s K=0 from hq,←drag_do];abel
 have hm: gustaway s v M= M*drag v K+M*flux v:=by
    unfold M;rw [Derivation.leibniz,hX,hd,show gustaway s v L=L*flux v from moving hv]; simp [smul_eq_mul,mul_assoc,add_comm,mul_comm,mul_left_comm]
 change pin s (H.brew M)=_;rw [H.brew_pin hs]
 rw [away,drag_do,flux, Finset.mul_sum,Finset.mul_sum] at hm
 have he:=eq_add_of_sub_eq hm
 rw [he,map_add,map_add,map_sum,map_sum,map_sum]
 rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib];apply Finset.sum_eq_zero;intro i _
 by_cases hi:i∈H.foam
 · rw [show M*(v i*pin i K)=pin i K * (M*v i) from by ac_rfl,H.mint hb hi (M*v i), Derivation.leibniz,map_add];simp only [smul_eq_mul];abel
 rw [hV i hi,map_zero];simp

end Haze
end YM.RG08.Room
