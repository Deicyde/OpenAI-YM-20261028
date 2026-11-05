import YM.RG12.Spins.Valley
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 2048
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice Wilson RG Source Source.Drops Labels Next.Foundations Planned.AtomRegular Foliage WardBin.Lies
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{n:Side}
lemma arc_still (H:Hol G)(d:ℕ)(o:Site n)(J:Jet G): fderiv ℝ (testLog H d o J) 0=0 :=by
   have hl : HasDerivAt (fun s:ℝ=> trunk d (scaleJet J s)) 0 0:=(hasDerivAt_pi).mpr fun k=>by
        change HasDerivAt (fun s:ℝ=>s^(k.val+2) • _) (0:Labels.Taylor G k.val) _
        have he {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (c : F): HasDerivAt (fun s:ℝ=> s^(j+2) • c) 0 0:=by
           have hi:=(((hasDerivAt_id' (0:ℝ)).pow (j+2)).smul_const c); convert hi using 1 <;> first| rfl| simp
        exact he k.val (J k.val)
   let F (X:Snap G d): Directions G n:=fun e=> G.plog (G.mat (H.testLinks d o (Source.Drops.expand d X) 1 e))
   have hF : DifferentiableAt ℝ F 0:= differentiableAt_pi.mpr (fun e=>by
        let q:Edge Cover:=(Lattice.lift (e.1-o),e.2)
        obtain ⟨hk,ht,_⟩:= Work.G02.linkGerm H d q
        have hi: ContDiffAt ℝ ω (fun X:Snap G d=>G.plog (G.mat (H.testLinks d o (Source.Drops.expand d X) 1 e))) 0:=
          (show ContDiffAt ℝ ω G.plog (G.mat (H.testLinks d o (Source.Drops.expand d (0:Snap G d)) 1 e)) from (by change ContDiffAt ℝ ω G.plog (G.mat (H.links d _ 1 q)); rw [ht,G.mat_one]; exact G.plog_diff)).comp (f:=fun X:Snap G d=> G.mat (H.links d (Source.Drops.expand d X) 1 q)) 0 hk.contDiffAt
        exact hi.differentiableAt (by simp)) -- not Applic?
   rw [show testLog H d o J= F ∘ (fun y=> trunk d (scaleJet J y)) from (by funext y; unfold testLog; rw [test_scaled]; rfl)]
   have hv: trunk d (scaleJet J (0:ℝ))=0:=by ext1 i; simp [trunk,scaleJet]
   rw [fderiv_comp 0 (hv.symm ▸ hF) hl.differentiableAt, hl.hasFDerivAt.fderiv]; apply ContinuousLinearMap.ext; intro x
   simp -- function 1-dimensional smul?
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
private lemma blister (p:OrderedFinpartition 4)(h:2≤ p.length)(he:∀ i,(2:ℕ) ≤ p.partSize i): p.length=2 ∧ ∀ i,p.partSize i=2:=by
   have ht:= (p.sum_sigma_eq_sum (fun (_:Fin 4)=>(1:ℕ)))
   simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at ht
   have hx:= Finset.sum_le_sum (s:=Finset.univ) (f:=fun i:Fin p.length=>2) (fun i _=> he i)
   simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hx
   have hz:p.length=2:=by omega
   refine ⟨hz,fun i=>le_antisymm ?_ (he i)⟩
   have hy:= Finset.sum_erase_add _ p.partSize (Finset.mem_univ i)
   have hk:= Finset.sum_le_sum (s:=Finset.univ.erase i) (f:=fun i:Fin p.length=>2) (fun j _=> he j)
   simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,Fintype.card_fin, hz, smul_eq_mul] at hk; omega
lemma formed (H:ℝ→E)(F:E→F)(hh:ContDiffAt ℝ 4 H 0)(ht:ContDiffAt ℝ 4 F 0)(hH : H 0=0)(hd:fderiv ℝ H 0=0)(hz:fderiv ℝ F 0=0):
    let V:=iteratedDeriv 2 H 0
    ‖iteratedDeriv 4 (F ∘ H) 0‖ ≤ (Fintype.card (OrderedFinpartition 4):ℝ) * ‖iteratedFDeriv ℝ 2 F 0 (fun _=>V)‖:=by
   intro V
   let v:Fin 4→ℝ:= fun _=>1
   unfold iteratedDeriv; rw [iteratedFDeriv_comp (g:=F) (f:=H) (hH.symm ▸ ht) hh (n:=(4:ℕ∞ω)) (by norm_num),FormalMultilinearSeries.taylorComp,_root_.sum_apply];
   apply (norm_sum_le ..).trans
   calc
    (∑ i: OrderedFinpartition 4,_) ≤ ∑ i:OrderedFinpartition 4,‖iteratedFDeriv ℝ 2 F 0 (fun _=>V)‖:=Finset.sum_le_sum fun p _=>?_
    _=_:=by simp
   change ‖iteratedFDeriv ℝ p.length F (H 0) (fun i=> iteratedFDeriv ℝ (p.partSize i) H 0 (v ∘ p.emb i))‖ ≤ _
   rw [hH]; by_cases hp:2 ≤p.length
   swap
   · rcases show p.length=0 ∨ p.length=1 by omega with ha|ha
     · exact (p.length_pos (by decide :0<4) |>.ne' ha).elim
     have hj(n:ℕ)(h:n=1)(g:Fin n→E): iteratedFDeriv ℝ n F 0 g=0:=by
         subst n; have he: iteratedFDeriv ℝ 1 F 0=0:=by rw [←norm_eq_zero,norm_iteratedFDeriv_one,hz,norm_zero]
         rw [he]; rfl
     rw [hj _ ha, norm_zero]; exact norm_nonneg _
   by_cases he:∀ j:Fin p.length,2 ≤ p.partSize j
   · obtain ⟨hk,hA⟩:=blister p hp he
     have hh(n:ℕ)(h:n=2)(u:Fin n→ℝ)(hu:∀ i,u i=1):iteratedFDeriv ℝ n H 0 u=V:=by subst n; rw [funext hu]; rfl
     rw [show (fun i=> iteratedFDeriv ℝ (p.partSize i) H 0 (v ∘ p.emb i))=(fun (_:Fin p.length)=>V) from funext (fun i=> hh _ (hA i) _ fun _=>rfl)]
     rw [hk]
   push Not at he
   obtain ⟨i,hi⟩:=he
   have hh(n:ℕ)(h:n=1)(u:Fin n→ℝ):iteratedFDeriv ℝ n H 0 u=0:=by
       subst n; have he: iteratedFDeriv ℝ 1 H 0=0:=by rw [←norm_eq_zero,norm_iteratedFDeriv_one,hd,norm_zero]
       rw [he]; rfl
   rw [(iteratedFDeriv ℝ p.length F 0).map_coord_zero i (hh _ (le_antisymm (by omega) (p.partSize_pos i)) _),norm_zero]; exact norm_nonneg _
end YM.RG12.Spins
