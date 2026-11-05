import YM.Spin.Isolates
import YM.Ward.Circles


/-!
# Small representations annihilate on the corrected plane

Lie maps satisfy a finite family of perfect identities. No reducibility assumed of deformed.
The projector inputs P p must be supplied (e.g. polynomial Casimir).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Function Set Filter
open scoped Topology InnerProductSpace BigOperators
variable {R : Type*} [NormedRing R] {I : Type*} [Fintype I] [Nonempty I]

abbrev Relations (D : I → R) (l r : I → I) := ∀ i, D i=D (l i)*D (r i) - D (r i)*D (l i)
omit [Fintype I] [Nonempty I] in
lemma restrict_rel (l r : I → I) (D : I → R) (p : R) (h : p*p=p) (hv : ∀ i, Commute p (D i)) (hp : Relations D l r) :
    Relations (fun i => D i*p) l r := by
  intro i
  dsimp only
  have he a b : D a*p*(D b*p)=D a*D b*p := by rw [mul_assoc,← mul_assoc p (D b),(hv b).eq,mul_assoc (D b),h,mul_assoc]
  rw [he,he,← sub_mul,← hp]

lemma enough (D : I → R) (l r : I → I) (h : Relations D l r) (he : ∀ i, ‖D i‖ < 1/2) : ∀ i, D i=0 := by
  classical
  obtain ⟨y,hy,hp⟩ := Finset.exists_max_image Finset.univ (fun i => ‖D i‖) Finset.univ_nonempty
  have mt i := hp i (Finset.mem_univ i)
  have hn i j : ‖D i*D j‖ ≤ ‖D y‖^2 := (norm_mul_le _ _).trans
    (sq ‖D y‖ ▸ mul_le_mul (mt i) (mt j) (norm_nonneg _) (norm_nonneg _))
  have hx : ‖D y‖ ≤ ‖D y‖^2 + ‖D y‖^2 := calc
                                                ‖D y‖ = _ := congr_arg norm (h y)
                                                _ ≤ _ := (norm_sub_le ..).trans (add_le_add (hn ..) (hn ..))
  intro i; refine norm_eq_zero.mp ?_
  have ht : ‖D y‖=0 := by nlinarith [he y, norm_nonneg (D y)]
  exact le_antisymm ((mt i).trans ht.le) (norm_nonneg _)

/-- Common lift of idempotent inside closed additive-subring constraint
(commuting K; invariant real/H symmetry, etc.). -/
lemma onto [CompleteSpace R] (l r : I → I) (D : I → ℕ → R) (d : I → R) (h : ∀ i, Tendsto (D i) atTop (𝓝 (d i)))
    (he : ∀ᶠ i in atTop, Relations (fun p => D p i) l r) (P : ℕ → R) (p : R) (hx : Tendsto P atTop (𝓝 p))
    (hd : p*p=p) (hp : ∀ i, d i*p=0) (S : Subring R) (hs : IsClosed (S : Set R)) (hS : ∀ᶠ i in atTop, P i∈S)
    (H : ∀ᶠ n in atTop, ∀ i, Commute (P n) (D i n)) : ∃ Q : ℕ → R, Tendsto Q atTop (𝓝 p) ∧
    ∀ᶠ n in atTop, Q n∈S ∧ Q n*Q n=Q n ∧ ∀ i, Commute (Q n) (D i n) ∧ D i n*Q n=0 := by
  obtain ⟨Q,hQ,h'⟩ := stable (show defect p=0 from by simp [defect,pow_two,hd]) P hx
  refine ⟨Q,h',?_⟩
  have hh : ∀ᶠ n in atTop, ∀ i, ‖D i n * Q n‖ < 1/2 := by
    apply eventually_all.mpr; intro i
    have ht := ((h i).mul h').norm; rw [hp,norm_zero] at ht; exact ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hQ,he,hS,H,hh] with n hn hL hy hm ht
  have hm i : Commute (Q n) (D i n) := by
    refine tendsto_nhds_unique (f := fun k => φ^[k] (P n) * D i n) (hn.1.mul_const (D i n))
      ((hn.1.const_mul (D i n)).congr' (Eventually.of_forall fun k => ?_))
    suffices he : Commute (φ^[k] (P n)) (D i n) from he.symm
    induction k with
    | zero => exact hm i
    | succ k hk =>
      rw [iterate_succ_apply',φ]; exact Commute.sub_left
        ((Nat.cast_commute 3 _).mul_left (hk.pow_left _))
        ((Nat.cast_commute 2 _).mul_left (hk.pow_left _))
  have hv : Q n*Q n=Q n := sub_eq_zero.mp (by simpa [defect,pow_two] using hn.2)
  refine ⟨?_,hv,fun i => ⟨hm i,enough _ l r (restrict_rel l r _ _ hv hm hL) ht i⟩⟩
  apply hs.mem_of_tendsto hn.1; apply Eventually.of_forall; intro k
  induction k with
  | zero => exact hy
  | succ k hk =>
    rw [iterate_succ_apply',φ]; exact S.sub_mem (S.mul_mem (by simp) (S.pow_mem hk _))
      (S.mul_mem (by simp) (S.pow_mem hk _))
end YM.Spin
