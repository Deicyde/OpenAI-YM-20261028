import YM.Extra.FREE_DETECTOR_ALGEBRA.Solutions
import YM.Next.FOUNDATIONS.LinkBounds


set_option warningAsError false

/-!
# Translating finite tensor towers

Ordinary Taylor coefficients, use the accepted foundations calculation to
compute diagonals on lines. Uses no field extension property beyond the actual
polynomial free jet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j k : ℕ}

lemma along {f : E4 → F} {x : E4} (hf : ContDiffAt ℝ k f x) (y : E4) :
    diagonal (coeff f k x) y = (↑(Nat.factorial k) : ℝ)⁻¹ • iteratedDeriv k (fun t : ℝ => f (x+t • y)) 0 := by
  let g : E4 → F := fun z => f (x+z)
  have he : ContDiffAt ℝ k g 0 := (show ContDiffAt ℝ k f (x+0) by simpa using hf).comp _ (contDiffAt_const.add contDiffAt_id)
  have ht : iteratedFDeriv ℝ k g 0 = iteratedFDeriv ℝ k f x := by
    unfold g; rw [iteratedFDeriv_comp_add_left,add_zero]
  rw [show (fun t : ℝ => f (x+t • y)) = fun t : ℝ => g (t • y) from rfl, Next.Foundations.iteratedDeriv_on_line he,ht]
  rfl

lemma deriv_power {f : ℝ → F} (hf : ContDiffAt ℝ k f 0) (hk : k ≤ j) :
    iteratedDeriv k (fun t : ℝ => t^j • f t) 0 = if k=j then (↑(Nat.factorial k):ℝ) • f 0 else 0 := by
  let g (t : ℝ) := t^j
  have hp : ContDiffAt ℝ k g 0 := contDiffAt_id.pow _
  have he := iteratedDerivWithin_smul (mem_univ (0:ℝ)) (uniqueDiffOn_univ (𝕜 := ℝ)) hp.contDiffWithinAt hf.contDiffWithinAt
  simp_rw [iteratedDerivWithin_univ, g, iteratedDeriv_fun_pow_zero] at he
  rw [show iteratedDeriv k (fun t : ℝ => t^j • f t) 0 = _ from he]
  split_ifs with h
  · subst k
    rw [Finset.sum_eq_single_of_mem j (by simp)]
    · simp
    · intro b _ hb; simp [hb]
  rw [Finset.sum_eq_zero]
  intro b hb; have ht := Finset.mem_range.mp hb
  simp [show ¬ b=j by omega]

def splitTensor (P : T E4 F j) (x y : E4) (s : Finset (Fin j)) := P (s.piecewise (fun _ => y) fun _ => x)

theorem line_expands (P : T E4 F j) (x y : E4) (t : ℝ) :
    diagonal P (x+t • y) = ∑ s : Finset (Fin j), t^s.card • splitTensor P x y s := by
  classical
  rw [add_comm]
  have he := P.map_add_univ (fun _ => t • y) (fun _ => x)
  rw [show diagonal P (t • y + x) = _ from he]
  refine Finset.sum_congr rfl fun s _ => ?_
  let u := s.piecewise (fun _ : Fin j => y) (fun _ => x)
  have ht := P.toMultilinearMap.map_piecewise_smul (fun _ => t) u s
  rw [Finset.prod_const] at ht
  change _ = _ • P u
  rw [show t^s.card • P u = _ from ht.symm]
  apply congr_arg P; funext i; by_cases h : i∈s <;> simp [Finset.piecewise, u,h]

theorem line_binom (P : T E4 F j) (k : ℕ) (x y : E4) :
    diagonal (coeff (diagonal P) k x) y =
      ∑ s : Finset (Fin j), if k=s.card then splitTensor P x y s else 0 := by
  rw [along (diag_smooth P k).contDiffAt y]
  have h (s : Finset (Fin j)) : ContDiffAt ℝ k (fun t : ℝ => t^s.card • splitTensor P x y s) 0 :=
    (contDiffAt_id.pow _).smul contDiffAt_const
  rw [show (fun t : ℝ => diagonal P (x+t • y)) = (fun t => ∑ s : Finset (Fin j), t^s.card • splitTensor P x y s) from funext (line_expands P x y),
    iteratedDeriv_fun_sum (fun i _ => h i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [iteratedDeriv_smul_const (show ContDiffAt ℝ k (fun t : ℝ => t^s.card) 0 from contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero]
  split_ifs with he
  · subst k; rw [smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
  simp

theorem coeff_full (P : T E4 F j) (hp : Sym P) (x : E4) : coeff (diagonal P) j x = P := by
  refine ext_diag _ _ (coeff_symm (diag_smooth P j).contDiffAt) hp ?_
  funext y
  rw [line_binom, Finset.sum_eq_single_of_mem Finset.univ (Finset.mem_univ _)]
  · simp only [Finset.card_univ,Fintype.card_fin,↓reduceIte]
    exact congr_arg P (by ext i; simp [Finset.piecewise])
  intro s _ hs
  have he : s.card < (Finset.univ : Finset (Fin j)).card := Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ _) hs)
  simp only [Finset.card_univ,Fintype.card_fin] at he
  rw [if_neg he.ne']

theorem taylor_full (P : T E4 F j) (x y : E4) :
    ∑ k : Fin (j+1), diagonal (coeff (diagonal P) (k:ℕ) x) y = diagonal P (x+y) := by
  simp_rw [line_binom]
  rw [show diagonal P (x+y) = ∑ s : Finset (Fin j), splitTensor P x y s from by simpa using line_expands P x y 1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hc : s.card < j+1 := by
    have h := Finset.card_le_card (Finset.subset_univ s)
    simpa only [Finset.card_univ,Fintype.card_fin, Nat.lt_succ_iff] using h
  let u : Fin (j+1) := ⟨s.card,hc⟩
  rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
  · rw [if_pos (show u.val = s.card from rfl)]
  intro i _ hi
  rw [if_neg (fun h => hi (Fin.ext h))]

/-- Components of the jet translated by `x`; uses the full homogeneous
solution and takes ordinary Taylor components (may also ask k>j). -/
def towards (j k : ℕ) (x : E4) : Sol F j →ₗ[ℝ] Sol F k where
  toFun S := ⟨WaveOn.nth S.field k x,S.wave.jets isOpen_univ (mem_univ _)⟩
  map_add' P Q := by
    apply Subtype.ext; funext a b
    change coeff (P.field a b + Q.field a b) k x = _
    exact coeff_add ((P.smooth a b x).of_le (WithTop.coe_le_coe.mpr le_top)) ((Q.smooth a b x).of_le (WithTop.coe_le_coe.mpr le_top))
  map_smul' c P := by
    apply Subtype.ext; funext a b
    change coeff (c • P.field a b) k x = _
    exact coeff_smul c ((P.smooth a b x).of_le (WithTop.coe_le_coe.mpr le_top))

@[simp] theorem towards_self (P : Sol F j) (x : E4) : towards _ j x P = P :=
  Subtype.ext (funext fun i => funext fun m => coeff_full (P.val i m) (P.closed.coeffSym i m) x)

theorem field_expands (P : Sol F j) (i m : Axis) (x y : E4) :
    ∑ k : Fin (j+1), Sol.field (towards _ k.val x P) i m y = P.field i m (x+y) := taylor_full (P.val i m) x y
end YM.Extra.FD
