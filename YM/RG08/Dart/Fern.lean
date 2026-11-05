import YM.RG08.Dart.Fay
/-! # Pack reproduction at leading order, potentials fully promoted. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter Work.F02
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295 Work.F03 Shade
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {r k i:ℕ}{G:Gauge}{m:Side}{R σ C:ℝ} {V : Rooted ℝ (Loc G 2) r}
-- leading curvature via true torus. Includes even zero.
lemma ring_height (p:Site m)(j:Beads (Loc G 2) r)(x:Link G m): (actionP j|>.poly fun i=> faceCurl (slotFace ((actionP j).leg i) p) (arm G m 1 x))= ∏ i, raze x (p+wrap m ((j i).1),(j i).2):=by
    let L(i:Fin r):= (j i).2.2
    unfold Atom.poly; rw [sum_eq_single_of_mem L (mem_univ _),show (actionP j).coeff L=1 from Pi.single_eq_same ..,one_mul]; swap; · intro i _ hi; rw [show (actionP j).coeff i=0 from Pi.single_eq_of_ne hi _,zero_mul]
    refine prod_congr rfl fun i _=>?_; unfold faceCurl raze; unfold actionP slotFace; dsimp only; rw [walkSlot_end,show plaquette (walkSlot (plaqEquiv.symm (j i).2.1) (j i).1).plaq=(j i).2.1 from plaqEquiv.apply_symm_apply _,add_comm p]
lemma ring_ray (h: Quire.Lit V σ C)(hp:0<σ)(p:Site m)(x:Link G m) : Tendsto (fun t:ℝ=> t⁻¹^r * rise_a p V (t • x)) (𝓝[≠]0) (𝓝 (rootSong V m p (raze x))):= by
    unfold rootSong Tensor.diagonal; have hv:= Ink.pens h (ling_one hp.le); rw [stitch_apply hv.of_norm]
    have hT i : Tendsto (fun t: ℝ=> t⁻¹^r * (V i*(actionP i|>.unmasked (input G m (t•x)) p))) (𝓝[≠]0) (𝓝 (V i*rosary (fun _=>raze x) p i)):= by
       convert (atom_limit (actionP i) p (arm G m 1 x)).const_mul (V i) using 1
       · ext t; unfold input; rw [map_smul,div_eq_mul_inv,inv_pow]; ring
       rw [ring_height p i x]; rfl
    obtain ⟨B,hB,H⟩:= slots_bound (arm G m 1 x)
    unfold rise_a shore_at; dsimp only [Function.comp_apply]; simp_rw [← tsum_mul_left]; refine tendsto_tsum_of_dominated_convergence (hv.mul_right (B^r)) hT ?_
    filter_upwards [H] with t ht i
    rw [show t⁻¹ ^r * _ = V i*((actionP i).unmasked (Precision.represent (t•arm G m 1 x)) p / t^r) from (by unfold input; rw [map_smul,inv_pow, div_eq_mul_inv]; ring),norm_mul, atom_scale]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (poly_bound (actionP i) _ B (fun i=>ht p _)).trans_eq (by rw [mag_atom,one_mul])
lemma altitude (h:Quire.Lit V σ C)(hp:0<σ)(p : Site m): Rays r (rise_a p V) := ray_origin (fun x=>⟨_,by simpa only [inv_pow,smul_eq_mul] using ring_ray h hp p x⟩)
lemma heights_d (h:Quire.Lit V σ C)(hp:0<σ)(p:Site m): Tensor.diagonal (Tensor.coeff (rise_a p V) r 0) = fun x=> rootSong V m p (raze x) := by funext x; exact tendsto_nhds_unique (ray_limit (rise_t h hp p|>.1) (altitude h hp p) x) (by simpa only [inv_pow, smul_eq_mul] using ring_ray h hp p x)
lemma born_r (h:Quire.Lit V σ C)(hp:0<σ)(p : Site m)(he:i < r): Tensor.coeff (rise_a p V) i 0=0:= by rw [Tensor.coeff,(rays_jet (rise_t h hp p|>.1) r).1 (altitude h hp p) i he,smul_zero]
lemma gem_f (h:Quire.Lit V σ C)(hp:0<σ)(p:Site m)(he:Dapple V): force (rise_a p V) ∧ Stained G (rise_a p V):= by
   refine ⟨?_,fun s=> Eventually.of_forall fun x=> ?_⟩
   · unfold force; filter_upwards [moveField_germ (G:=G) (m:=m)] with z hz
     change shore_at p V (input G m (moveField z))= _; rw [hz]; exact shore_g h hp he _ _ _
   change shore_at p V (input G m (stain s x))=_; rw [← stain_cons]; exact shore_g h hp he _ _ _
lemma token_preserves {U: Rooted ℝ (Loc G 1) r}(hv:0<σ)(hp:Tidy U)(hh: Quire.Lit U (2*σ) C)(h:Toll U) : butter (dart U) r=U:=by
   apply Tidy.uniquely (butter_h (thorn hh hv) hv _) hp; intro m
   unfold rootSong; rw [(rise_t (thorn hh hv) hv _).2]
   rw [heights_d (thorn hh hv) hv]; funext x; exact Eq.symm (toll_eye (U:=U) (fun _=>x) hh hv h)
-- including unqualified lower zeros from height. use exact reproduction.
lemma pearls_z {W:Rooted ℝ (Loc G 2) r}(h:Quire.Lit W σ C)(hv:0<σ)(hp:i < r): butter W i=0:=by
    refine Tidy.uniquely (butter_h h hv i) (Tidy.zero ..) (fun m=>?_); unfold rootSong; rw [(rise_t h hv _).2, born_r h hv _ hp]; rw [st_zero]
end YM.RG08.Dart
