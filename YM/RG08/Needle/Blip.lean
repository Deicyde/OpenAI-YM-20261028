import YM.RG08.Needle.Pale
/-!
# Tree and horizontal mean passages on a TRUE ROOT
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c f L:Side}{v w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}{T:SectionData F}
variable {X:Cross L (Loc G 1) (Loc G 1)} {V: EnvelopeU D R G r}{p':Site m}{S:Screed ℝ (Loc G 1)}
set_option maxHeartbeats 400000 in
lemma lights (h:∀ i j,Tidy (S i j))(hp:Shore p' τ S) (x:PAC (Candles G) m) (n r:ℕ) :
    let U:= Loom.strand τ n S
    rootSong (U r) m p' (fderiv ℝ (dragged G m) 0 x)=rootSong (U r) m p' (bundleLink x)-∑ j∈range r,rootSong (crock (U j) r) m p' x := by
  intro U
  obtain ⟨W,hW⟩:= shelved (p:=n) (n:=r+τ) hp (by omega) h
  let F:= W∘input G m; let H:= large p' r U; let Z:= dragged G m; let g:= bundleLink (G:=G) (m:=m); let K:= input G m
  have hg : ContDiffAt ℝ ω Z 0:= dragged_analytic.contDiffAt; have hz : Z 0=0:= dragged_zero
  have ht : ∀ i,Tidy (U i):= fun i=> strand_tid h
  have he : F ∘ Z=ᶠ[𝓝 0] F∘g := by
    have hp : Tendsto K (𝓝 0) (𝓝 1):= by simpa [K] using input_cont.tendsto (0:Link G m)
    let G':=bundleSites (G:=G) (m:=m)
    have hX: Tendsto G' (𝓝 0) (𝓝 0) := by simpa only [map_zero] using G'.continuous.tendsto 0
    exact hW.coast (K ∘ g) (K ∘ Z) _ _ (hp.comp (by simpa only [map_zero] using g.continuous.tendsto 0)) (hp.comp (hz ▸ hg.continuousAt.tendsto)) (hX.eventually moveField_germ)
  let p (i:ℕ):= rootSong (U i) m p' ∘ Z
  have heq (i): ContDiffAt ℝ ω (p i) 0 := (Tensor.diag_smooth ..).contDiffAt.comp _ hg
  have hH i (hp:i≤r) : Tensor.coeff F i 0= Tensor.coeff H i 0:= (hW.scores_at i (by omega)).trans (Loom.large_jet _ _ ht hp).symm
  have hx : Tensor.coeff (F∘Z) r 0 = Tensor.coeff (H∘Z) r 0 := by
    unfold Tensor.coeff; congr 1; ext1 v
    rw [Cases.compReads (hg:= (show ContDiffAt ℝ ω F (Z 0) from hz.symm ▸ hW.hol)) hg le_top,Cases.compReads (large_smooth ..).contDiffAt hg le_top]
    apply sum_congr rfl; intro i _; unfold Cases.caseRead; rw [hz]; apply DFunLike.congr_fun; apply smul_right_injective _ (show ((i.length.factorial:ℝ)⁻¹)≠0 by positivity); exact hH _ i.length_le
  let u:=fun _:Fin r=>x
  have hh' : H ∘ Z=∑ i∈range (r+1),p i := funext fun x=> by simp only [H,p,large,Function.comp_apply,Finset.sum_apply]
  have hE : rootSong (U r) m p' (g x)=∑ i∈range (r+1), Tensor.coeff (p i) r 0 u := by
    rw [← _root_.sum_apply, ← Tensor.coeff_sum _ _ _ _ (fun i _=>(heq i).of_le le_top),←hh',←hx]
    unfold rootSong Tensor.diagonal -- order
    rw [← hW.scores_at r (by omega),Tensor.GermCoeff r he]
    unfold Tensor.coeff; rw [Next.Foundations.jets_linear g (show ContDiffAt ℝ r F 0 from hW.hol.of_le le_top)]; rfl
  have hI (i:ℕ): Tensor.coeff (p i) r 0 u=rootSong (crock (U i) r) m p' x := by
    rw [crock_hike (ht i).pens]; change Tensor.diagonal (Tensor.coeff (p i) r 0) x=ink (fun z:ℝ=>p i (z•x)) r; rw [pulse_ray (p i) r ((heq i).of_le le_top),jet_coefficient]
  have hK: Tensor.coeff (p r) r 0 u= stitch (U r) m p' (fun i=> fderiv ℝ Z 0 x) := by
    unfold Tensor.coeff
    let f:= rootSong (U r) m p'; have hh: ContDiffAt ℝ ω f (Z 0):= (Tensor.diag_smooth ..).contDiffAt
    rw [_root_.smul_apply, Cases.compReads hh hg le_top, sum_eq_single (.atomic r)]; swap
    · intro i _ he; unfold Cases.caseRead; rw [hz]; let j:=i.length
      have hx : Tensor.coeff f j 0=0:= coeff_diagonal_else _ ((ht r).sym p') (show j≠ r from fun h=> he (Cases.finest i h)); simp only [Tensor.coeff,smul_eq_zero,inv_eq_zero,Nat.cast_eq_zero,Nat.factorial_ne_zero,false_or] at hx
      rw [show iteratedFDeriv ℝ i.length f 0=0 from hx]; rfl
    swap; · simp
    rw [Cases.one,hz]; exact DFunLike.congr_fun (coeff_at_diagonal _ ((ht r).sym p')) _
  rw [Finset.sum_range_succ,hK] at hE; rw [show rootSong (U r) m p' (bundleLink x)=_ from hE]; simp_rw [hI]; rw [add_sub_cancel_left]; rfl
end YM.RG08.Needle
