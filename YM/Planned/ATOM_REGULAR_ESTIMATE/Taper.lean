import YM.Next.EXTRACTION.Relay
import YM.Next.FOUNDATIONS.SU2
import YM.Planned.ATOM_REGULAR_ESTIMATE.LogChart
import YM.Planned.ATOM_REGULAR_ESTIMATE.Moments


/-!
Arterial estimates for the short principal kernel. `taper_bound` uses
budgeted log coordinates and grade localization of the actual sampled
variations (at fixed coarse field/sample, *prior to testing with f*).
Mean-value proof of Taylor cancellation requiring through order `d+1` on
fine input, and if the coarse test order is higher, only through *that*
order. In particular do not buy one derivative in each step or assume
analyticity of the field. No dependence on count of input sites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Short
open Function Tensor Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n L : Side} {B : BudgetPoint} {o : Site n} {X : Support n} {J : Finset (Link n)}
  {k d m : ℕ} {w c : ℝ}

/-- `w` prices all velocities *at this sample*. `i=d` is the unrestricted
remainder of cost order `L^-(d+1)`. -/
def Taper (B : BudgetPoint) (o : Site n) (X : Support n) (J : Finset (Link n)) (d : ℕ)
    (L : Side) (w : ℝ) (u : Directions G n) :=
  ∃ v : Fin (d+1) → Directions G n, (∑ i,v i)=u ∧
    (∀ i, i.val < d → Flat.FitsGrade o X i.val (limitAmp B o J (v i))) ∧
    ∀ i, ‖v i‖ ≤ w * ((L.val : ℝ)⁻¹)^(i.val+1)

lemma unit_inv (L : Side) : (L.val : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
  (by exact_mod_cast (show 1 ≤ L.val from L.property))
lemma Taper.norm {u : Directions G n} (h : Taper B o X J d L w u) (hw : 0 ≤ w) :
    ‖u‖ ≤ ((d+1:ℕ):ℝ)*w*((L.val:ℝ)⁻¹) := by
  obtain ⟨v,rfl,-,hv⟩ := h
  apply (norm_sum_le ..).trans
  have he i : ‖v i‖ ≤ w*(L.val:ℝ)⁻¹ :=
    (hv i).trans (mul_le_mul_of_nonneg_left (pow_le_of_le_one (by positivity) (unit_inv L) (Nat.succ_ne_zero _)) hw)
  exact (Finset.sum_le_sum (fun i _ => he i)).trans_eq (by rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_assoc])

/-- The polar of the actual `L_X`-argument field in the limited chart.
Estimated at any point of the indicated segment; the RHS deliberately pays
the same polynomial in `w` at every order for integration. -/
theorem taper_bound {f : Config G n → ℂ} {A : Hol G} {v : Directions G n}
    (ha : A.PiVanish d o f) (hy : B.Regular X f) (hc : B.supBounds o X f c)
    (hp : Nonwrapping X o) (hn : 2 ≤ n.val) (hd : d+1 ≤ k) (hk : k ≤ B.order)
    (hg : ∀ s ∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (bone B o J (s • v)))
    (hh : ∀ i∈J, ‖limitAmp B o J v i‖ ≤ 1) (hj : ∀ i∈J, weight B o i ≤ 1)
    (hw : 1 ≤ w) (hv : Taper B o X J d L w v) :
    ∀ i ≤ k, ∀ u : Fin i → Directions G n, (∀ l, Taper B o X J d L w (u l)) →
    ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ i (f ∘ bone B o J) (s • v) u‖ ≤
        ((k:ℝ)+1) * ((baseCost G k * c) * ((((d+1:ℕ):ℝ)*w)^k * ((L.val:ℝ)⁻¹)^(d+1))) := by
  let F := f ∘ bone B o J
  let I := Set.Icc (0:ℝ) 1
  let C := baseCost G k * c
  let r := (L.val:ℝ)⁻¹; let z := (d+1:ℕ); let W := (z:ℝ)*w
  have hr : 0 ≤ r := by unfold r; positivity
  have hr' : r ≤ 1 := unit_inv _
  have hz : 1 ≤ (z:ℝ) := by unfold z; push_cast; simp
  have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le hz hw
  have hW' := zero_le_one.trans hw
  have hC : 0 ≤ C := mul_nonneg (baseCost_nonneg ..) hc.1
  let D := C*(W^k*r^(d+1))
  have hD : 0 ≤ D := mul_nonneg hC (mul_nonneg (pow_nonneg (zero_le_one.trans hW) _) (pow_nonneg hr _))
  have H s (h : s∈I) : ContDiffAt ℝ k F (s • v) ∧ ∀ i ≤ k, ‖iteratedFDeriv ℝ i F (s • v)‖ ≤ C := by
    apply base_bound hy hc hk (hg s h) _ hj; intro i hi
    rw [map_smul,Pi.smul_apply,norm_smul_of_nonneg h.1]
    exact mul_le_one₀ h.2 (norm_nonneg _) (hh i hi)
  have h₀ : (0:ℝ) ∈ I := ⟨le_rfl,zero_le_one⟩
  have hcore := H 0 h₀; rw [zero_smul] at hcore
  have he (i) (hi : i ≤ k) (hi' : d < i) (u : Fin i → Directions G n) (hu : ∀ j,Taper B o X J d L w (u j)) s (hs : s∈I) :
      ‖iteratedFDeriv ℝ i F (s • v) u‖ ≤ D := by
    have ht := ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ((H s hs).2 i hi)
      (show ∀ j, ‖u j‖ ≤ W*r from fun j => (hu j).norm (zero_le_one.trans hw))
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hW hi) (pow_le_pow_of_le_one hr hr' hi') (pow_nonneg hr _) (pow_nonneg (by linarith) _)) hC)
  have hm {i : ℕ} (hi : i ≤ k) (u : Fin i → Directions G n) (hu : ∀ j,Taper B o X J d L w (u j)) :
      ‖iteratedFDeriv ℝ i F 0 u‖ ≤ D := by
    by_cases ht : d < i
    · simpa only [zero_smul] using he i hi ht u hu 0 h₀
    choose p ha' hp' hbill using hu
    rw [← funext ha', (iteratedFDeriv ℝ i F 0).map_sum (α:=fun _ => Fin (d+1))]
    let T := iteratedFDeriv ℝ i F 0
    have H' : ContDiffAt ℝ d (f ∘ increment 1) 0 :=
      (hy.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr ((d.le_succ.trans hd).trans hk))
    have Hb : ∀ j : Fin i → Fin (d+1), ‖T (fun l => p l (j l))‖ ≤ C*(w^i*r^(d+1)) := by
      intro j
      let a (l : Fin i) := (j l).val+1
      let A' := ∑ l,a l
      by_cases hu' : A' ≤ d
      · let M := limitAmp (G:=G) B o J
        have h p' : T p' = iteratedFDeriv ℝ i (f ∘ increment 1) 0 (fun l => M (p' l)) := by
          change iteratedFDeriv ℝ i ((f ∘ increment 1) ∘ M) 0 p' = _
          rw [jets_linear M (H'.of_le (Nat.cast_le.mpr (le_of_not_gt ht)))]; rfl
        rw [h, Flat.moments o X hp hn H' ha hy.symmetry hy.sites _ a (fun l => Nat.succ_pos _) hu', norm_zero]
        · positivity
        intro l
        have ht : (j l).val+1 ≤ d := (Finset.single_le_sum (f:=a) (fun s _ => Nat.zero_le _) (Finset.mem_univ l)).trans hu'
        exact hp' l _ (by omega)
      apply le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hcore.2 i hi) (fun l => hbill l (j l)))
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr' (show d+1 ≤ A' by omega)) (pow_nonneg hW' _)) hC
    refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun j _ => Hb j)).trans ?_)
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    calc
      _ = C*(W^i*r^(d+1)) := by unfold W z; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hW hi) (pow_nonneg hr _)) hC
  intro i hi u hu s hs
  have step (j : ℕ) (hj : j ≤ k) : ∀ u : Fin j → Directions G n, (∀ l,Taper B o X J d L w (u l)) →
      ∀ t ∈ I, ‖iteratedFDeriv ℝ j F (t • v) u‖ ≤ (((k+1-j:ℕ):ℝ))*D := by
    induction hj using Nat.decreasingInduction with
    | self =>
      intro u hu t ht; simpa only [show k+1-k=1 by omega,Nat.cast_one,one_mul] using he k le_rfl hd u hu t ht
    | of_succ j hlt ih =>
      intro u hu t ht
      let g (s:ℝ) := iteratedFDeriv ℝ j F (s • v) u
      let Q (s:ℝ) := iteratedFDeriv ℝ (j+1) F (s • v) (Fin.cons v u)
      have hx s (hs : s∈I) : HasDerivAt g (Q s) s := by
        have hx := (H s hs).1.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hlt)
        let L' := ContinuousMultilinearMap.apply ℝ _ ℂ u
        have hu := (L'.hasFDerivAt.comp (s • v) hx.hasFDerivAt).comp_hasDerivAt s
          (f:=fun z : ℝ => z • v) (f':=v) (by simpa using! (hasDerivAt_id' s).smul_const v)
        unfold Q; rw [iteratedFDeriv_succ_apply_left,Fin.cons_zero,Fin.tail_cons]; exact hu
      have hsucc : ∀ l : Fin (j+1), Taper (G:=G) B o X J d L w ((Fin.cons (α:=fun _ => Directions G n) v u) l) := by
        intro l; refine Fin.cases ?_ (fun a => ?_) l
        · simpa using hv
        simpa using hu a
      have ht' : 0 ≤ (((k+1-(j+1):ℕ):ℝ))*D := mul_nonneg (Nat.cast_nonneg _) hD
      have hdiff : ‖g t - g 0‖ ≤ (((k+1-(j+1):ℕ):ℝ))*D := (Convex.norm_image_sub_le_of_norm_deriv_le
        (fun i hi => (hx i hi).differentiableAt) (fun i hi => (congr_arg (‖·‖) (hx i hi).deriv).trans_le
          (ih _ hsucc _ hi)) (convex_Icc (𝕜:=ℝ) ..) h₀ ht).trans (mul_le_of_le_one_right ht' (by rw [sub_zero,Real.norm_of_nonneg ht.1]; exact ht.2))
      have hcost : ‖g 0‖ ≤ D := by simpa [g] using hm hlt.le u hu
      refine le_trans (show ‖g t‖ ≤ ‖g t-g 0‖+‖g 0‖ from (by simpa using norm_add_le (g t-g 0) (g 0))) ((add_le_add hdiff hcost).trans_eq ?_)
      rw [show k+1-j=k+1-(j+1)+1 by omega,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
  have ht : ((k+1-i:ℕ):ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast (show k+1-i ≤ k+1 from Nat.sub_le ..)
  exact (step i hi u hu s hs).trans (mul_le_mul_of_nonneg_right ht hD)

end YM.Planned.AtomRegular.Short
