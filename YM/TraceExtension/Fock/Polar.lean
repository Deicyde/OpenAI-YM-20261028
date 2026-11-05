import YM.TraceExtension.Fock.Form

/-! Polarization tools. `diagonal` uses affine arguments only; no ambient
norm or continuity on a local vector space needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

lemma powers_unique (f : ℕ → ℂ) (h : ∀ (t : ℝ), 0<t → HasSum (fun n : ℕ => (t:ℂ)^n * f n) 0)
    (n : ℕ) : f n=0 := by
    induction n using Nat.strong_induction_on with
    | h k ih =>
      have ht (t : ℝ) (ht : 0<t) : HasSum (fun i : ℕ => (t:ℂ)^i * f (i+k)) 0 := by
          have hp := (hasSum_nat_add_iff' k).mpr (h t ht)
          simp only [pow_add] at hp
          rw [Finset.sum_eq_zero (fun i hi => (by rw [ih i (Finset.mem_range.mp hi),mul_zero])),sub_zero] at hp
          have he := hp.mul_left ((t:ℂ)^k)⁻¹
          rw [mul_zero] at he
          convert! he using 1; funext i; field_simp [(Complex.ofReal_ne_zero.mpr ht.ne')]
      have hf : Summable (fun n => ‖f (n+k)‖) :=
          (show HasSum (fun i => f (i+k)) 0 by simpa using ht 1 one_pos).summable.norm
      have hu : Tendsto (fun t:ℝ => ∑' i : ℕ,(t:ℂ)^i * f (i+k)) (𝓝[>] 0)
          (𝓝 (∑' i : ℕ,(↑(0:ℝ):ℂ)^i * f (i+k))) := by
        apply tendsto_tsum_of_dominated_convergence hf (fun i => ((show Continuous (fun t:ℝ => (t:ℂ)^i*f (i+k)) from by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
        filter_upwards [(gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with i hi hp j
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (le_of_lt (show 0 < i from hp))]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (le_of_lt (show 0 < i from hp)) hi.le)
      rw [tsum_eq_single 0 (fun i hi => by simp [hi]), pow_zero,one_mul,Nat.zero_add] at hu
      exact tendsto_nhds_unique_of_eventuallyEq hu tendsto_const_nhds (Eventually.mono self_mem_nhdsWithin (fun i hi => (ht i hi).tsum_eq))

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ}
abbrev MLinear (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℝ V] := MultilinearMap ℝ (fun _ : Fin n => V) ℂ

private lemma mult_sym {f : MLinear n V} (hr : ∀ (v : Fin n → V) (u : Equiv.Perm (Fin n)), f (v ∘ u)=f v)
    (i j : Fin n) (x y : V) : f (update (fun _ => x) i y) = f (update (fun _ => x) j y) := by
    rw [← hr (update (fun _ => x) j y) (Equiv.swap i j)]
    congr 1; ext k
    by_cases ht : k=i
    · simp [ht]
    have hv : (Equiv.swap i j) k ≠ j := by simpa only [Equiv.swap_apply_left] using (Equiv.swap i j).injective.ne ht
    simp [hv,ht]

lemma diag_tail (f : MLinear (n+1) V) (hr : ∀ v (u : Equiv.Perm (Fin (n+1))), f (v ∘ u)=f v)
    (x : V) (v : Fin n → V) (u : Equiv.Perm (Fin n)) :
    f.curryLeft x (v ∘ u) = f.curryLeft x v := by
    change f (Fin.cons _ _) = f (Fin.cons _ _)
    let a := (Equiv.optionCongr u)
    let s := finSuccEquiv n
    let b : Equiv.Perm (Fin (n+1)) := s.trans (a.trans s.symm)
    rw [← hr (Fin.cons (α:=fun _ : Fin (n+1) => V) x v) b]; congr 1; ext i
    refine Fin.cases ?_ (fun j=> ?_) i <;> simp [b,s,a]

lemma diag_deriv (f : MLinear n V) (hr : ∀ v (u : Equiv.Perm (Fin n)), f (v ∘ u)=f v) (x y : V) :
    HasDerivAt (fun t : ℝ => f fun _ => x+t • y) (∑ i : Fin n, f (update (fun _ => x) i y)) 0 := by
    induction n with
    | zero =>
      rw [Finset.sum_of_isEmpty]
      convert! hasDerivAt_const (𝕜:=ℝ) 0 (f fun _ => x) using 1; ext1; congr!
    | succ n ih =>
      let F (u:V) := fun t : ℝ => f.curryLeft u (fun _ => x+t • y)
      have he : (fun t : ℝ => f fun _ => x+t • y) = fun t => F x t + t • F y t := by
          ext t; dsimp only [F]; rw [← _root_.smul_apply, ← map_smul, ← _root_.add_apply, ← map_add]; change f _=f _
          congr 1; ext1 i; refine Fin.cases ?_ (fun j=> ?_) i <;> simp
      rw [he]
      convert! (ih (f.curryLeft x) (diag_tail f hr x)).add ((hasDerivAt_id' (0:ℝ)).smul (ih (f.curryLeft y) (diag_tail f hr y))) using 1
      simp only [zero_smul,add_zero,one_smul]; rw [Fin.sum_univ_succ]; dsimp [F]
      have hp : (fun i => f (update (fun _ => x) i.succ y)) = fun i => f.curryLeft x (update (fun _ => x) i y) := by
         ext i; change f _=f _; congr 1; ext1 j; refine Fin.cases ?_ (fun j=> ?_) j
         · simp [update_of_ne (Ne.symm i.succ_ne_zero)]
         by_cases h:j=i <;> simp [h]
      simp_rw [congr_fun hp]
      rw [add_comm]; congr 1; rw [zero_add]; change f _=f _; congr 1; ext i; refine Fin.cases ?_ (fun j=> ?_) i <;> simp

lemma polar_identity (f : MLinear n V) (hr : ∀ v (u : Equiv.Perm (Fin n)), f (v ∘ u)=f v)
    (h : ∀ z : V, f (fun _ => z)=0) (v : Fin n→V) : f v=0 := by
    induction n with
    | zero => convert h 0 using 2
    | succ n ih =>
        rw [← Fin.cons_self_tail v]; let y:= v 0
        refine ih (f.curryLeft y) (diag_tail f hr _) ?_ (Fin.tail v)
        intro x
        have hv := diag_deriv f hr x y
        simp_rw [h] at hv
        have hb := hv.unique (hasDerivAt_const ..)
        simp_rw [show ∀ i, f (update (fun _ => x) i y) = f.curryLeft y (fun _=>x) from fun i => by
            rw [mult_sym hr i 0]; change f _=f _; congr 1; ext j; refine Fin.cases ?_ (fun k=> ?_) j <;> simp] at hb
        simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_eq_zero] at hb; exact hb.resolve_left (Nat.cast_ne_zero.mpr n.succ_ne_zero)
end
end YM.TraceExtension.Photons
