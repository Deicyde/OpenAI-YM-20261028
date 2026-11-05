import YM.TraceExtension.Perfect.Trove
import YM.Analysis.Exchange
import YM.TraceExtension.Lamp.Keg
set_option autoImplicit false
/-! # polynomial from freely gauged stem -/
noncomputable section
namespace YM.Tensor
open Set Function ContinuousMultilinearMap Analysis
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j k : ℕ}
theorem bore_diag (A : T E F j) (ha : Sym A) : coeff (diagonal A) j 0 = A := by
  apply ContinuousMultilinearMap.ext; intro u
  induction j with
  | zero => rw [coeff_apply_zero]; exact congr_arg A (Subsingleton.elim ..)
  | succ j ih =>
    rw [← Fin.cons_self_tail u]
    let v := u 0
    let s := Fin.tail u
    let B := A.curryLeft v
    let t : ℝ := (↑(j+1 : ℕ) : ℝ)
    have he : D v (diagonal A) = t • diagonal B := funext fun x => by
      rw [D,differential_diagonal A ha]
      change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
      rw [Nat.cast_smul_eq_nsmul]; rfl
    have hs := ih B (freeze_sym A ha v) s
    have ht : t ≠ 0 := by dsimp [t]; positivity
    change coeff (diagonal A) (j+1) 0 (Fin.cons v s) = _
    rw [coeff_apply_cons (diag_smooth A _ |>.contDiffAt),he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply,hs]
    change t⁻¹ • t • B s = _
    rw [inv_smul_smul₀ ht]
    rfl

theorem bore_diag_ne (A : T E F j) (ha : Sym A) (hh : k ≠ j) :
    coeff (diagonal A) k 0 = 0 := by
  apply ContinuousMultilinearMap.ext; intro u
  induction k generalizing j with
  | zero =>
    rw [coeff_apply_zero]
    cases j with
    | zero => exact (hh rfl).elim
    | succ j =>
      change A _ = (0:F)
      exact A.map_coord_zero (0 : Fin (j+1)) rfl
  | succ k ih =>
    rw [← Fin.cons_self_tail u, coeff_apply_cons (diag_smooth A _ |>.contDiffAt)]
    cases j with
    | zero =>
      rw [show diagonal A = fun _ => diagonal A 0 from
        funext fun _ => congr_arg A (Subsingleton.elim ..)]
      have hz : D (u 0) (fun _ => diagonal A 0) = fun _ => (0:F) := by simp [D, funext_iff]
      rw [hz, coeff_zero]; simp
    | succ j =>
      let v := u 0
      let B := A.curryLeft v
      have he : D (u 0) (diagonal A) = (↑(j+1 : ℕ) : ℝ) • diagonal B := funext fun x => by
        rw [D,differential_diagonal A ha];
        change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
        rw [Nat.cast_smul_eq_nsmul]; rfl
      rw [he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply, ih B (freeze_sym A ha v) (by omega)]
      simp

end YM.Tensor
namespace YM.Trace.Filch
open Function Filter Set Lattice Precision Finset Planned.PrimaryIntegral295.Cases Lamp
open scoped Topology ContDiff Classical
variable {X Y V : Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup V][NormedSpace ℝ V]{n d:ℕ}{F H:X→ Y}{x:X}
open Tensor Perfect

def choral(n:ℕ)(F:X→ Y) : X→Y:= ∑ i∈range (n+1), diagonal (coeff F i 0)
lemma rhythm (F:X→Y)(n:ℕ): ContDiff ℝ ω (choral n F):=by
    rw [show choral n F=(fun x=>∑ i∈range (n+1), diagonal (coeff F i 0) x) from funext fun x=>Finset.sum_apply ..]; exact ContDiff.sum (fun i _=> diag_smooth (coeff F _ _) _)
lemma reverberate (F:X→ Y)(x:X)(n:ℕ): choral n F x=∑ i∈range (n+1), neap i F 0 x := Finset.sum_apply ..
lemma repitch (h:ContDiffAt ℝ ω F 0)(n:ℕ): braid F (choral n F) 0 n:=by
    intro i hi
    have hx: coeff (choral n F) i 0=coeff F i 0:=by
       rw[choral,coeff_sum i _ _ _ (fun i _=> (diag_smooth (coeff F _ _) _).contDiffAt),sum_eq_single i,bore_diag _ (coeff_symm (h.of_le le_top))]; intro j _ H; exact bore_diag_ne _ (coeff_symm (h.of_le le_top)) (Ne.symm H)
       simp[show i<n+1 by omega]
    exact (smul_right_injective (ContinuousMultilinearMap ℝ (fun _:Fin i=> X) Y) (inv_ne_zero (show (i.factorial:ℝ) ≠0 by positivity))) hx.symm
lemma intoned (L:X→L[ℝ]Y)(H:X→V)(F:Y→ V)(h:H=ᶠ[𝓝 0] F ∘ L)(n:ℕ)(hf:ContDiffAt ℝ ω F 0) (x:X): choral n H x=choral n F (L x):=by
   rw [reverberate,reverberate]; refine sum_congr rfl (fun i _=> ?_); unfold neap; rw [(braided (n:=i) h) i le_rfl, Push.Uniform.iter_lin_at (show ContDiffAt ℝ i F (L 0) from (map_zero L).symm ▸ hf.of_le le_top),map_zero]; rfl
lemma slice_tone(L:Y→L[ℝ] V)(F:X→ Y)(n:ℕ)(hf:ContDiffAt ℝ ω F 0)(x:X) : choral n (L ∘ F) x=L (choral n F x):=by
   rw [reverberate,reverberate,map_sum]; refine sum_congr rfl (fun i _ => ?_); unfold neap; rw [L.iteratedFDeriv_comp_left hf le_top,map_smul]; rfl
end YM.Trace.Filch
