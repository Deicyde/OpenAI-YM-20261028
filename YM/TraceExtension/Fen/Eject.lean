import YM.TraceExtension.Fen.Wood
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine AnalyticNext.QuarticMatch.Estimate
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} (R:Rep G n){I:Type}(b:I→Barley) {k P:ℕ}{σ A B C:ℝ}
lemma chapelMain (h:R.path.Bounds R.clip σ A C)(e:Lines G n 1) : ContDiffAt ℝ ω (outD (Main R) e ∘ input G n) 0:=by
    let V(p:Link G n×Link G n):=input _ _ p.2 * input _ _ p.1
    have hp: ContDiffAt ℝ ω (Main R ∘ V) (0,0):= Work.F02.mainTerm_contDiffAt (A:=V) h ((Army.powL contDiffAt_snd).mul (Army.powL contDiffAt_fst))
    obtain ⟨C,hC,h⟩:=exists_allows (s:={(0,(0:Link G n))}) (f:=Main R ∘ V) isCompact_singleton (fun x hx=>hx.symm ▸ hp) 1
    exact (priced_partial (x:= (0:Link G n)) (a:=bolt e) (n:=0) (h _ (Set.mem_singleton _)) (norm_bolt e).le).analytic
private lemma wholesale {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X](u:Finset I)(f:I→X→ℝ)(h:∀ i∈u,ContDiffAt ℝ ω (f i) 0): ContDiffAt ℝ ω (fun x=>∑ i∈u,f i x) 0:=ContDiffAt.sum h
private lemma atpole (e:Lines G n 1)(hB:2 ≤ R.p.B)(L:Finset I): ContDiffAt ℝ ω (outD (piste R b L) e ∘ input G n) 0:=by
    obtain ⟨f,hf,H⟩:=waves (G:=G) 0
    rw [overlook]; unfold Function.comp; simp only[Finset.sum_apply]; exact wholesale _ _ (fun i _=> (H _ b _ R hB i e).analytic)
private lemma ateak (e:Lines G n 1)(hB:2 ≤ R.p.B)(L:Finset I) (k:ℕ): iteratedFDeriv ℝ k (outD (piste R b L) e ∘ input G n) 0=∑ p∈univ ×ˢ L,iteratedFDeriv ℝ k (outD (seatP R b p) e ∘ input G n) 0:=by
    obtain ⟨f,hf,H⟩:=waves (G:=G) k
    rw [overlook]; unfold Function.comp; simp only[Finset.sum_apply]; exact iteratedFDeriv_fun_sum_apply (f:=fun i x=> outD (seatP R b i) e (input G n x)) (fun i _=> ((H _ b _ R hB i e).analytic).of_le le_top)
private lemma abends {X:Type}[NormedAddCommGroup X](f:I→X)(u:Finset I) (y:X)(h:HasSum f y): HasSum (fun i=> if i∈ u then 0 else f i) (y-∑ i∈u,f i):=by
    let s (i):=if i∈u then f i else 0; have hs:HasSum s (∑ i∈u,f i):=by
        rw [show (∑ i∈u,f i)=∑ i∈u,s i from Finset.sum_congr rfl (fun i hi=> by simp [s,hi])]; exact hasSum_sum_of_ne_finset_zero (fun i hi=> if_neg hi)
    refine (h.sub hs).congr_fun fun i=>?_; by_cases ht:i∈u <;> simp[s,ht]
lemma east (G:Gauge)(k:ℕ): ∃ K:ℝ, ∃ P:ℕ, 0 ≤ K∧∀ (n:Side)(R:Rep G n)(σ A C:ℝ), R.path.Bounds R.clip σ A C →2≤ R.p.B →
    let B:=Geo.lowerSize R.clip A+(A+A); let Z:= bankCost R.p.B*K*(momentPrice P (σ/2)*B)
    (∀ e:Lines G n 1, Allows k (outD (Main R) e ∘ input G n) 0 Z) ∧ ∀ r:ℕ,∀ q:ℝ, 0<q →∀ᶠ L:Finset GreenA in atTop,∀ e:Lines G n 1,
        Allows k ((outD (Main R - ski R legF L r) e) ∘ input G n) 0 (bankCost R.p.B*K*q +Real.exp (-(σ/4)*r)*Z):=by
    obtain ⟨f,⟨hf,K,P,hK,hf'⟩,H⟩:= waves (G:=G) k
    refine ⟨K,P+4,by positivity,fun n R σ A C hp hr=>?_⟩
    intro B Z; let z:= k; let X:=Pointed R legF (σ/2); have hs:= hp.width; let P':=P+4
    let F(e:Lines G n 1)(i:Seat n×GreenA):= outD (seatP R legF i) e ∘ input G n
    have ht(e:Lines G n 1)(i): Allows k (F e i) 0 (upLand R legF e i*f (mote R (legF i.2))):= H GreenA legF n R hr i e
    constructor
    · intro e
      have he:= purpose R legF B (off_budget R hp) hs (σ/2) (half_pos hs) (by linarith only[hs]) P'; rw[show σ-σ/2=σ/2 by ring] at he
      let g i:=upLand R legF e i*f (mote R (legF i.2))
      have hu:SumBudget g Z:=by
          have hh:= pumpkin R legF (σ/2) (half_pos hs).le (fun _=>True) hf P K hK hf' e (by simp only[if_true]; exact he)
          simpa only[Z, if_true,P',mul_assoc] using! hh
      refine ⟨chapelMain R hp e,fun j hj=>?_⟩
      have hw:= earnW R e hp j
      have hz: ∀ i, ‖iteratedFDeriv ℝ j (F e i) 0‖ ≤ g i:=fun i=> (ht e i).norm_le _ hj
      rw [← hw.tsum_eq]; exact (norm_tsum_le_tsum_norm hw.summable.norm).trans ((Summable.tsum_le_tsum hz hw.summable.norm hu.2.1).trans hu.2.2)
    intro r q hq
    filter_upwards [coatout R legF P' r B q hs (off_budget R hp) hq] with L HL e
    let t:= ski R legF L r; let u:= spikes R legF L r; let U:= outD (Main R) e ∘ input G n; let V:=outD t e ∘ input G n; let E:Finset (Seat n × GreenA):= univ ×ˢ u
    have hz(i:GreenA): i∈u↔ i∈L ∧ rowL R legF i ≤r:= mem_filter
    have hv: ∀ i:Seat n × GreenA, i∈E↔ i.2∈u:=by simp[E]
    let c:=momentPrice P' (σ/2)*B; let S:=Real.exp (-(σ/4)*r)
    let p(i:GreenA):Prop:=i∉ u; let f'(i):=if i∈E then 0 else upLand R legF e i*f (mote R (legF i.2))
    have hU: SumBudget f' (bankCost R.p.B*(K*(q+S*c))):=by
       apply Cost.mono (pumpkin R legF (σ/4) (by positivity) p hf P K hK hf' (e:=e) (q:=q+S*c) ?_) (fun i=> by unfold f'; split; exact le_rfl; exact (ht e i).nonneg) (fun i=> by unfold f'; by_cases x:i.2∈u <;> simp [hv i,p,x])
       convert! HL using 1; funext i; by_cases hx:i∈L ∧ rowL R legF i≤r <;> simp only[p,hz]; all_goals simp[hx,P']
    have ha:ContDiffAt ℝ ω V 0:= atpole R legF e hr u
    have hV : outD (Main R-t) e ∘ input G n=U - V:=by
       funext i; unfold U V outD
       let Y:= input G n i
       simp only[Function.comp_apply,Pi.sub_apply]; rw [fderiv_fun_sub (lightsA R (input G n i) hp|>.differentiableAt (by simp)) (show DifferentiableAt ℝ (fun y=> t (input G n y * input G n i)) 0 from slopeD R legF u Y)]; rfl
    rw[hV]; refine ⟨(chapelMain R hp e).sub ha,fun j hj=>?_⟩
    let w(i):=iteratedFDeriv ℝ j (F e i) 0
    rw[iteratedFDeriv_sub_apply ((chapelMain R hp e).of_le le_top) (ha.of_le le_top), show iteratedFDeriv ℝ j V 0=∑ i∈E,w i from ateak R legF e hr u j]; have hw:= abends w E _ (earnW R e hp j)
    let F' i:= if i∈E then 0 else w i
    have ht'(i): ‖F' i‖≤f' i:=by unfold F' f'; split <;> first|exact (ht e i).norm_le _ hj|simp
    -- ht sub sum
    rw [show iteratedFDeriv ℝ j U 0 -∑ i∈E,w i=(∑' i,F' i) from hw.tsum_eq.symm]
    exact (norm_tsum_le_tsum_norm hw.summable.norm).trans ((Summable.tsum_le_tsum ht' hw.summable.norm hU.2.1).trans (hU.2.2.trans_eq (by unfold Z c; unfold S; ring)))
end YM.Trace.Fen
