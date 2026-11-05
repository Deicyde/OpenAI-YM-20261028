import YM.TraceExtension.Quince.Creed
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pieces
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rays
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push.Local (Probe)
open Push Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free Laurent Cub Finset
open MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n c f:Side}
variable {k p d r j u:ℕ}{B:BudgetPoint}{S:StepData c f}{T:Tube G S}
-- exact access all columns letter
section Letter
variable (H:Hol G)(Q: Probe G d)(s t:ℝ)
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
lemma panel_fade (k:ℕ): let A y:=Ramble.panel Q y s; throughSlot (iteratedDeriv k A 0) k:=by
   intro A j he; let P:=Mom.deck (G:=G) (d:=d) j
   have hv := DFunLike.congr_fun (P.iteratedFDeriv_comp_left (x:=0) (Ramble.panel_paid Q s).contDiffAt (show (k:WithTop ℕ∞)≤ ω from le_top)) (fun _=> (1:ℝ))
   let v:=P (A 1)
   have ht(z:ℝ): P (A z)= z^(j.val+2) • v:= by
       unfold v P; simp only[Mom.deck_at]; ext1 i; by_cases hi:i=j
       · subst i; simp[A,Ramble.panel,WardBin.engineered_at]; exact smul_comm ..
       simp only [Pi.single_eq_of_ne hi,Pi.smul_apply,smul_zero]
   have hw: P (iteratedDeriv k A 0)=0:=by rw [show P (iteratedDeriv k A 0)=iteratedDeriv k (fun t=> P (A t)) 0 from hv.symm]; simp_rw [ht]; rw [iteratedDeriv_smul_const (contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero]; simp [he.ne]
   simpa [P,Mom.deck_at] using congr_fun hw j
lemma gaze (k:ℕ) : ∃ g: E4→ Axis→G.Color, g ∈ Place.rangeLt (Axis→G.Color) k ∧ Ramble.lamina Q k t s=verdict g:=by
   let A y:=Ramble.panel Q y s; let P(i:Axis)(z:E4):Snap G d→G.Color:=Film.lane z i; let f (p:OrderedFinpartition k) (x:E4) (i:Axis):= t⁻¹ • Cases.caseRead p (P i x) A 0 (fun _=>1)
   have he (p:OrderedFinpartition k) : f p ∈Place.rangeLt _ k:=by
       have hx:= Film.lane_polynomial p.partSize (fun i=>iteratedDeriv (p.partSize i) A 0) (fun i=> panel_fade Q s (p.partSize i)) p.partSize_pos
       have hq:∑ i,p.partSize i=k := by simpa using p.sum_sigma_eq_sum (fun _ => (1:ℕ))
       rw [hq] at hx; unfold f Cases.caseRead; rw [show A 0=0 from Ramble.paid_origin Q s]; exact (Place.rangeLt _ _).smul_mem t⁻¹ hx
   refine ⟨∑ p: OrderedFinpartition k,f p,(Place.rangeLt _ _).sum_mem (fun i _=> he i),?_⟩
   funext x i; unfold verdict; rw[Finset.sum_apply,Finset.sum_apply]; have hg : ContDiff ℝ ω A:=Ramble.panel_paid ..; have hh : ContDiffAt ℝ ω (P i (seat x)) (A 0):=by rw[show A 0=0 from Ramble.paid_origin Q s]; exact Film.lane_smooth ..
   change iteratedFDeriv ℝ k (t⁻¹ • (P i (seat x) ∘ A)) 0 (fun _=>1) = _; rw[iteratedFDeriv_const_smul_apply ((hh.comp _ hg.contDiffAt).of_le le_top),smul_apply,Cases.compReads hh hg.contDiffAt le_top,Finset.smul_sum]
lemma politics (e:Axis) {q:E4→ Axis → G.Color}(hq:q∈Place.rangeLt _ k): (fun v=>q v e)∈ Powers.space E4 G.Color (k-1):=by
   let Z:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis=> G.Color) e
   obtain ⟨a,ha,rfl⟩:= Place.range_decompose hq
   have h(i:Fin k) : (fun v=> a i v e)∈ Powers.space E4 G.Color (k-1):=by
      have he:= Place.linear_pure Z (ha i)
      exact Powers.residence ⟨Place.exact_smooth he ω,fun t v=> Place.exact_scale he v t⟩ (by omega)
   simp_rw [Finset.sum_apply]; exact Powers.sums _ _ (fun j _=> h j)
lemma map_city {X:Support f}(Y: Directions G f){A:E4→Axis→G.Color}(hp:A∈Place.rangeLt _ k)(he:∀ i : Bond f,Mom.needed X i → Y i=A (Place.seat (lift i.1)) i.2) : Mom.screen X Y ∈ Mom.Maps 0 X k:=by
    refine ⟨fun i v=> A v i,fun i=>politics (G:=G) i hp,fun i=>?_⟩
    rw[Mom.screen_at]; split
    next ht=> rw [he i ht]; simp only[Mom.stamp,sub_zero];rfl
    rfl
lemma city_p (k':ℕ)(a:Flight j u){r1:ℝ}(ht:0<r1)(hu:4≤ u)(h:k'≤j): ∃ z:E4→Axis→G.Color,z∈Place.rangeLt _ k' ∧ applyLine (linesOf a r1) (Ramble.lamina Q k' t s)=verdict z:=by
    obtain ⟨p,hx,hp⟩:=gaze Q s t k'; rw [hp]; obtain ⟨q,hQ,-,hy⟩:= accepts_V _ ht a hu h _ hx; exact ⟨_,hQ,hy⟩
end Letter
end YM.PhysicalNext.Repeat.Quince
