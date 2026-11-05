import YM.MergeProof.South.Sand

/-!
 # Uniform coarse cone, sup. labels may be budgeted later at EACH k, no N.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {G:Gauge}(C:Family G)(N k m p d:ℕ) (L:C.label d)(H:C.Makes)
local notation "o!"=> (0:Site (C.side k p))
local notation "R"=> C.path.rep N p
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
private lemma into {n:Side}(m:ℕ)(i:Site n)(h:separation i 0 ≤ m): i∈GridApprox.window 0 m:=by
    have hk : lift i∈box m:=by unfold separation at h; rw [sub_zero] at h; rw [box_test]; constructor <;> intro j <;> have := (component_le i j).trans h <;> omega
    exact ⟨_,hk,(add_zero _).trans (wrap_lift _)⟩
def lensScope (d:ℕ) := stencilRadius C d + 4
set_option quotPrecheck false
include H
lemma scopes (hN : k≤N) : lens C N k p d L= fun U=> alto C.path k d* L 0 + masked (C.path.levels.clock.threshold k) ((Y!).footprint o!) (candidate C k p d ((F).core L)) U:=by
   let Z:= Extra.Histories.primary o! L; let B:=R k; let u:=B.p.threshold; let S:= Y!; let a:=alto C.path k d
   have hB:u=C.path.levels.clock.threshold k:= congr_arg BudgetPoint.threshold ((H.wilson.represents N p k hN).vac)
   funext U; change a*Z.exponentialEntry 0 S B U= _; unfold Coefficient.exponentialEntry; have hx(i):Z.maskedTerm B i U=0:=by unfold Coefficient.maskedTerm;by_cases H:Healthy B.p.threshold (Z.support i) U;rw [masked_eq _ _ _ _ H];rfl;exact masked_ne _ _ _ _ H -- separate
   simp_rw [hx,tsum_zero,add_zero]
   change a*(L 0+masked u (S.footprint o!) _ _)=a*L 0+masked _ _ _ U; rw [← hB,mul_add]; congr 1
   by_cases he : Healthy u (S.footprint o!) U
   · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ he,show B.p.threshold= _ from hB]; rfl
   rw [masked_ne _ _ _ _ he, masked_ne _ _ _ _ he,mul_zero]
lemma visible (hN:k≤N) : Interior (GridApprox.window o! (lensScope C d)) (lens C N k p d L):=by
   rw [scopes C N k p d L H hN]; let V:=Y!; let a:=V.footprint o!; let t:= C.path.levels.clock.threshold k; let g:=candidate C k p d ((F).core L); have hk:=candidate_fits C H k p d ((F).core L); apply (Interior.constant _ _).plus; apply Interior.enlarges (K:=inspected a) -- arg
   · have hp: LocalOn (inspected a) (masked t a g):=by
       refine UsesFinal.allReads _ _ _ (uses_mask _ ?_); intro U W h; exact congr_arg (alto C.path k d * ·) ((C.localSection d).placed_local 0 _ _ _ h) -- polyp eval
     have hT := hk.borel
     obtain ⟨M,hM⟩:= (cylinder_env hk).cost
     refine ⟨invariant_mask hk.gauge _ _,masked_measurable _ _ _ hT,hp,M,fun U=>?_⟩
     by_cases H: Healthy t a U
     · rw [masked_eq t a g U H]; exact hM U
     rw [masked_ne t a g U H,norm_zero]; exact (norm_nonneg (g U)).trans (hM U)
   intro x hx; obtain ⟨i,hi,H'⟩:= halo_spec.mp (Extra.Multi.System.within a hx)
   obtain ⟨y,hy,he⟩:= stencil_fits C d (0:Site (C.side k p)) hi
   apply into; rw [separation_comm]; apply (separation_triangle _ i _).trans (Nat.add_le_add ?_ H'); rw [← he]; exact Work.E08.separation_box_add _ hy -- order?
lemma cameras : ∃ A:ℝ,0≤A∧∀ N p,k≤N→∀ U, ‖lens C N k p d L U‖ ≤ A:=by
   let g:= (F).core L; obtain ⟨A,hA,h⟩:=candidate_bounded C d k ‖g‖ (norm_nonneg g)
   refine ⟨‖(alto C.path k d)*L 0‖+A,add_nonneg (norm_nonneg _) hA.le,fun N p hk U=> ?_⟩
   rw [scopes C N k p d L H hk]; apply (norm_add_le ..).trans (add_le_add_right ?_ _); let t:=C.path.levels.clock.threshold k; let a:=(C.localSection d).footprint (0:Site (C.side k p)); let F₀:= candidate C k p d g
   change ‖masked t a F₀ U‖ ≤ A; by_cases he: Healthy t a U
   · rw [masked_eq _ _ _ _ he]; exact h p g le_rfl U
   rw [masked_ne _ _ _ _ he,norm_zero]; exact hA.le
end YM.MergeProof.Accent
