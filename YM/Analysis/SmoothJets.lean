import YM.Analysis.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Ordinary mixed tensors, slot convention

Over the reals. These are **local** assertions at a point,
so they can be used directly on separated configuration spaces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Set Filter ContinuousMultilinearMap Equiv
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j : ℕ} {f g : E → F} {x : E}

/-- Directional derivative. Totalized as with mathlib `fderiv`. -/
def D (u : E) (f : E → F) (x : E) : F := fderiv ℝ f x u

theorem dSmooth {m n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x) (u : E) (h : m+1 ≤ n) :
    ContDiffAt ℝ m (D u f) x := (hf.fderiv_right h).clm_apply contDiffAt_const

theorem iterD (h : ContDiffAt ℝ j f x) (u : Fin j → E) :
    ContinuousAt (fun y ↦ iteratedFDeriv ℝ j f y u) x :=
  (ContinuousMultilinearMap.apply ℝ (fun _ => E) F u).continuous.continuousAt.comp (h.continuousAt_iteratedFDeriv le_rfl)

theorem cons_jet (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (u : E) (v : Fin j → E) :
    iteratedFDeriv ℝ (j+1) f x (Fin.cons u v) =
      D u (fun z ↦ iteratedFDeriv ℝ j f z v) x := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    h.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr j.lt_succ_self)
  rw [hd.iteratedFDeriv_succ_apply_left']
  simp [D]

theorem snoc_jet (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (u : E) (v : Fin j → E) :
    iteratedFDeriv ℝ (j+1) f x (Fin.snoc v u) =
      iteratedFDeriv ℝ j (D u f) x v := by
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  let E1 := ContinuousLinearMap.apply ℝ F u
  change _ = iteratedFDeriv ℝ j (E1 ∘ fderiv ℝ f) x v
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left]
  · rfl
  · exact h.fderiv_right (by push_cast; rfl)
  rfl

theorem GermD (u : E) (he : f =ᶠ[𝓝 x] g) : D u f x = D u g x := by
  rw [D,D, he.fderiv_eq]

theorem commuteD (h : ContDiffAt ℝ 2 f x) (u v : E) : D u (D v f) x = D v (D u f) x := by
  have hu := (h.isSymmSndFDerivAt (by simp))
  have hd (a b : E) : D a (D b f) x = (fderiv ℝ (fderiv ℝ f) x a) b := by
    unfold D
    rw [fderiv_clm_apply (hc := (h.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) (hu := differentiableAt_const _)]
    simp
  rw [hd, hd, hu u v]

theorem double_cons (h : ContDiffAt ℝ (↑(j+2 : ℕ)) f x) (u w : E) (v : Fin j → E) :
    iteratedFDeriv ℝ (j+2) f x (Fin.cons u (Fin.cons w v)) =
    D u (D w fun z : E ↦ iteratedFDeriv ℝ j f z v) x := by
  rw [cons_jet h]
  refine GermD u ?_
  have he (i : ℕ) : (i : WithTop ℕ∞) ≠ ∞ := by simp
  filter_upwards [h.eventually (he _)] with y hy
  exact cons_jet (hy.of_le (Nat.cast_le.mpr (j+1).le_succ)) w v

theorem sym_Jet (h : ContDiffAt ℝ j f x) : Tensor.Sym (iteratedFDeriv ℝ j f x) := by
  induction j generalizing x with
  | zero => intro v s; congr! 1
  | succ j ih =>
    cases j with
    | zero =>
      intro v s
      rw [show v ∘ s = v from funext fun a ↦ congr_arg v (@Subsingleton.elim (Fin 1) _ _ _)]
    | succ k =>
      -- Tail permutations, from lower-order symmetry locally.
      let B (s : Perm (Fin (k+1))) := Perm.decomposeFin.symm (0,s)
      let P (s : Perm (Fin (k+2))) := ∀ v : Fin (k+2) → E, iteratedFDeriv ℝ (k+2) f x (v ∘ s) = iteratedFDeriv ℝ (k+2) f x v
      have T (s : Perm (Fin (k+1))) : P (B s) := by
        intro v
        let w := Fin.tail v
        conv_lhs => rw [show v ∘ B s = Fin.cons (v 0) (w ∘ s) by
          ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [B, w, Fin.tail]]
        conv_rhs => rw [← Fin.cons_self_tail v]
        rw [cons_jet h, cons_jet h]
        refine GermD (v 0) ?_
        filter_upwards [h.eventually (by simp)] with y hy
        exact ih (hy.of_le (Nat.cast_le.mpr (k+1).le_succ)) w s
      -- And exchange the first two positions, by the real C² theorem.
      let oneI := (0 : Fin (k+1)).succ
      have U : P (swap 0 oneI) := by
        intro v
        let w := Fin.tail (Fin.tail v)
        conv_rhs => rw [show v = Fin.cons (v 0) (Fin.cons (v oneI) w) by
          change v = Fin.cons (v 0) (Fin.cons (Fin.tail v 0) (Fin.tail (Fin.tail v)))
          rw [Fin.cons_self_tail, Fin.cons_self_tail]]
        conv_lhs => rw [show v ∘ swap 0 oneI = Fin.cons (v oneI) (Fin.cons (v 0) w) by
          ext i; refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · refine Fin.cases ?_ (fun n ↦ ?_) j
            · dsimp only [oneI]; simp
            simp only [w, Function.comp, swap_apply_def, oneI]
            simp only [Fin.succ_ne_zero, Fin.succ_inj, ↓reduceIte, Fin.cons_succ]
            rfl]
        rw [double_cons h, double_cons h]
        refine commuteD ((ContinuousMultilinearMap.apply ℝ _ F w).contDiff.contDiffAt.comp x
          (h.iteratedFDeriv_right ?_)) _ _
        push_cast; rw [add_comm, add_assoc]; rfl
      have M (s t : Perm (Fin (k+2))) (hs : P s) (ht : P t) : P (s*t) := fun v =>
        (ht (v ∘ s)).trans (hs v)
      have IH0 (s : Perm (Fin (k+2))) (hs : P s) : P s⁻¹ := by
        intro v
        rw [← hs]
        rw [show (v ∘ ⇑s⁻¹) ∘ ⇑s = v by ext; simp]
      have V (i : Fin (k+2)) : P (swap 0 i) := by
        refine Fin.cases (by intro v; simp) ?_ i
        intro j
        let t := swap 0 j
        have he := swap_apply_apply (B t) 0 oneI
        have ht0 : (B t) 0 = 0 := by simp [B]
        have ht1 : (B t) oneI = j.succ := by simp [B, oneI, t]
        rw [ht0, ht1] at he
        rw [he]
        exact M _ _ (M _ _ (T _) U) (IH0 _ (T _))
      intro v s
      obtain ⟨⟨i,q⟩,rfl⟩ := Perm.decomposeFin.symm.surjective s
      have he : Perm.decomposeFin.symm (i,q) = swap 0 i * B q := by
        ext a
        refine Fin.cases ?_ (fun j ↦ ?_) a <;> simp [B]
      rw [he]; exact M _ _ (V _) (T _) _

theorem cons_inner (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (u : E) (v : Fin j → E) :
    iteratedFDeriv ℝ (j+1) f x (Fin.cons u v) =
      iteratedFDeriv ℝ j (D u f) x v := by
  rw [← snoc_jet h, Fin.snoc_eq_cons_rotate]
  exact (sym_Jet h _ (finRotate _)).symm

end YM.Analysis
