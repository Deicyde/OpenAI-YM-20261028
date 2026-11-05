import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest

set_option warningAsError false

/-! Removal in finite coordinate supports, exact polynomial derivatives and
cost accounting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {n j : ℕ}

def ether (P : Sol G.Color j) (i : Slot G) (z : E4) : ℂ := (legKernel (G:=G) (dualSol _ _ P) (coordinateLeg i) z:ℂ)

theorem coordStep (P : Sol G.Color j) {x y : E4} (hx : x≠y) (w : WickPol G) {J : Finset (Slot G)}
    (hv : w.vars ⊆ J) : descend P x y w = ∑ i∈J, ether P i (x-y) • MvPolynomial.pderiv i w := by
  classical
  let D : Derivation ℂ (WickPol G) (WickPol G) := ∑ i∈J, ether P i (x-y) • MvPolynomial.pderiv i
  have he : (descend P x y-D) w = 0 := by
    apply MvPolynomial.derivation_eq_zero_of_forall_mem_vars
    intro i hi
    change descend P _ _ (X i) - D (X i) = _
    rw [descend_X P i hx]; unfold D; rw [deriv_apply_sum,Finset.sum_eq_single_of_mem i (hv hi)]
    · change C (ether P i (x-y)) - (ether P i (x-y) • pderiv i (X i : WickPol G)) = _; simp [← C_mul']
    intro b _ hb
    change ether P b (x-y) • pderiv b (X i : WickPol G) = _; simp [pderiv_X_of_ne hb.symm]
  rw [show descend P x y w=D w from sub_eq_zero.mp he]; unfold D; rw [deriv_apply_sum]; rfl







/-- Ordinary linear response with the first input selected; use even if
there are no exterior entries. -/
def encounter (x : Points (n+1)) (v : Fin n → WickPol G) : WickPol G →ₗ[ℂ] ℂ := Pair.replace x (Fin.cons 0 v) 0

theorem before_all (x : Points (n+1)) (p : WickPol G) (v : Fin n → WickPol G) (g : WickPol G) : Pair.replace x (Fin.cons p v) 0 g =
    moment G x (Fin.cons g v) := by
  rw [replace_at,show update (Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) p v) 0 g = Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) g v by funext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp]

lemma encounter_vals (x : Points (n+1)) (v : Fin n→ WickPol G) (p) : encounter x v p = moment G x (Fin.cons p v) := before_all ..


lemma update_tail {ι : Type*} (p : ι) (f : Fin n → ι) (i : Fin n) (x : ι) :
    Function.update (Fin.cons (α:= fun _ : Fin (n+1) => ι) p f) i.succ x = Fin.cons (α:= fun _ : Fin (n+1) => ι) p (Function.update f i x) := by
  funext j; refine Fin.cases ?_ (fun k => ?_) j
  · rw [update_of_ne (Ne.symm (Fin.succ_ne_zero i))]; rfl
  by_cases he : k=i <;> simp [he]

def endOne (n : ℕ) : Fin n≃Pair.Others (0:Fin (n+1)) where
  toFun i := ⟨i.succ,Fin.succ_ne_zero _⟩
  invFun x := x.val.pred x.property
  left_inv _ := Fin.pred_succ ..
  right_inv x := Subtype.ext (Fin.succ_pred x.val x.property)

theorem open_front (x : Points (n+1)) (hx : x∈conf _) (p : WickPol G) (v : Fin n→WickPol G) (P : Sol G.Color j) :
    encounter x v (p*digit P) = ∑ i : Fin n, encounter x (update v i (descend P (x 0) (x i.succ) (v i))) p := by
  let V : Fin (n+1) → WickPol G := Fin.cons p v
  rw [encounter_vals,← before_all _ p]
  have he := descend_relation P x 0 hx V; change Pair.replace x (Fin.cons p v) 0 (p*digit P)=_ at he
  rw [he]; refine (Fintype.sum_equiv (endOne n) _ _ fun i => ?_).symm
  rw [encounter_vals]
  change _ = Pair.replace x (Fin.cons p v) i.succ (descend P (x 0) (x i.succ) (v i)); rw [replace_at,update_tail]

lemma encounter_update (x : Points (n+1)) (p : WickPol G) (v : Fin n→WickPol G) (i : Fin n) (w : WickPol G) :
    encounter x (update v i w) p = Pair.replace x (Fin.cons p v) i.succ w := by rw [replace_at,update_tail,encounter_vals]

/-- Open one source into the explicit finite number of coordinate legs. -/
theorem slip (P : Sol G.Color j) (x : Points (n+1)) (hx : x∈conf _) (p : WickPol G) (v : Fin n → WickPol G)
    (I : Fin n → Finset (Slot G)) (hi : ∀ i, (v i).vars ⊆ I i) : encounter x v (p*digit P)=
    ∑ i : Fin n, ∑ k ∈ I i, ether P k (x 0-x i.succ) * encounter x (update v i (pderiv k (v i))) p := by
  rw [open_front _ hx]
  apply Finset.sum_congr rfl; intro i _
  have he : x 0 ≠ x i.succ := (show Injective x.ofLp from hx).ne (Ne.symm (Fin.succ_ne_zero i))
  simp_rw [coordStep P he (v i) (hi i),encounter_update,map_sum,map_smul,smul_eq_mul]
end YM.Extra.FD
