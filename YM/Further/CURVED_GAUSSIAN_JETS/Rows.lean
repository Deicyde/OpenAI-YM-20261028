import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Progress.STATIONARY_SCENES.Green
import YM.Push.STATIONARY_UNIFORM.Count



/-!
# Kernel accounting for the sector covariance entries

Exponential norm always at a *displayed* distance price. Entry chains
include repeated indices and unmodified orientations. E.g. in paying
`major S ^ k` no absolute values have been moved past a cancellation.
Pairings in vacuum ledger use one real table on the very same chart
coordinates; nothing below gives bounds through a domain switch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open Function Filter Matrix Lattice Progress.StationaryScenes SectorNext.Vacuum Green Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
namespace Rows
variable {n : Side} {I : Type*} [Fintype I]
variable {a : I → Site n} {A B : Table I} {r h s t : ℝ}
abbrev Bill (a : I → Site n) (r : ℝ) (A : Table I) (s : ℝ) := Green.Both a a A r s s

def major (A : Table I) := Matrix.of fun i j => |A i j|

lemma of_rows (he : A.IsHermitian) (hs : Green.Rows a a A r s) : Bill a r A s := by
  have ht : A.transpose=A := he
  exact ⟨hs,ht.symm ▸ hs⟩

lemma tran (hs : Bill a r A s) : Bill a r A.transpose s := ⟨hs.2,hs.1⟩
lemma bigger (hs : Bill a r A s) (h : s≤t) : Bill a r A t := ⟨fun i => (hs.1 i).trans h,fun i => (hs.2 i).trans h⟩
lemma slower (hs : Bill a r A s) (hr : h≤r) : Bill a h A s := by
  have h (M : Table I) (hm : Green.Rows a a M r s) : Green.Rows a a M h s := by
    intro i; refine (Finset.sum_le_sum fun j _=>?_).trans (hm i)
    unfold wt; gcongr
  exact ⟨h _ hs.1,h _ hs.2⟩
lemma unweighted (hs : Bill a r A s) (hr : 0≤r) : Round.rowRate s A := fun i => by
  simpa [wt] using (slower hs hr).1 i
lemma absolute (hs : Bill a r A s) : Bill a r (major A) s := by
  constructor <;> intro i
  · simpa only [major,Matrix.of_apply,abs_abs] using! hs.1 i
  simpa only [Matrix.transpose_apply, major,Matrix.of_apply,abs_abs] using! hs.2 i
lemma pay (hs : Bill a r A s) (v : ℝ) : Bill a r (v • A) (|v| * s) :=
  ⟨Green.Rows.pay hs.1 v, by rw [Matrix.transpose_smul]; exact Green.Rows.pay hs.2 v⟩
lemma neg (hs : Bill a r A s) : Bill a r (-A) s := by simpa only [neg_one_smul,abs_neg, abs_one,one_mul] using pay hs (-1)
lemma plus (hs : Bill a r A s) (ht : Bill a r B t) : Bill a r (A+B) (s+t) := ⟨Green.Rows.plus hs.1 ht.1, Green.Rows.plus hs.2 ht.2⟩

lemma product (hr : 0≤r) (hs : Bill a r A s) (ht : Bill a r B t) (sh : 0≤s) (th : 0≤t) :
    Bill a r (A*B) (s*t) := ⟨Green.Rows.multiply hr hs.1 ht.1 th, by rw [Matrix.transpose_mul, mul_comm]; exact Green.Rows.multiply hr ht.2 hs.2 sh⟩

lemma count_left (hr : 0≤r) (hs : Bill a r A s) : ∀ i, (∑ j, |A i j|) ≤ s := by
  intro i; apply le_trans _ (hs.1 i)
  exact Finset.sum_le_sum fun j _=> le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg hr (Nat.cast_nonneg _)))

lemma entry (hr : 0≤r) (hs : Bill a r A s) (i j : I) : |A i j| ≤ s := by
  exact le_trans (Finset.single_le_sum (f:=fun j=>|A i j|) (fun _ _=>abs_nonneg _) (Finset.mem_univ j)) (count_left hr hs i)


lemma upper (hr : 0≤r) (hs : Bill a r A s) (v : Vec I) : quad A v ≤ s * dotProduct v v :=
    (le_abs_self _).trans (Green.schur A v s (count_left hr hs) (count_left hr (tran hs)))

/-- Uniform family of different column maps (row AND column bill
still necessary). Pointwise exponential from GREEN controls both
via native bounded multiplicity, here unshifted and shifted alike.
No period-size norm is substituted. -/
lemma weighed_budget {K : ℕ} (he : Push.Uniform.Multiplicity a K) {L : ℝ}
    (hs : ∀ i j, wt r (a i) (a j)* |A i j| ≤ L) (hp : 0≤L) (hh : 0 < r) :
    Bill a (r/2) A (L * (K * Push.Uniform.countCost (r/2))) := by
  have hrow (M : Table I) (hm : ∀ i j, wt r (a i) (a j)*|M i j| ≤ L) : Green.Rows a a M (r/2) (L * (K * Push.Uniform.countCost (r/2))) := by
    intro i
    have hi j := mul_le_mul_of_nonneg_left (hm i j) (Push.Uniform.decay_pos (r/2) (a i) (a j)).le
    have heq j : Push.Uniform.Decay (r/2) (a i) (a j) * wt r (a i) (a j) = wt (r/2) (a i) (a j) := by
      unfold Push.Uniform.Decay wt; rw [← Real.exp_add]; congr 1; ring
    simp_rw [←mul_assoc,heq,mul_comm _ L] at hi
    refine (Finset.sum_le_sum (fun j _ => hi j)).trans ?_
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (he.count a (half_pos hh) _) hp
  exact ⟨hrow _ hs,hrow _ (fun i j => by rw [wt_symm]; exact hs j i)⟩

variable [DecidableEq I]
lemma one : Bill a r (1:Table I) 1 := by
  apply of_rows isHermitian_one; intro i; simp [Matrix.one_apply, abs_ite, mul_ite, wt]
lemma power (hr : 0≤r) (hs : Bill a r A s) (hp : 0≤s) (j : ℕ) : Bill a r (A^j) (s^j) := by
  induction j with
  | zero => simp; exact one
  | succ j ih => rw [pow_succ,pow_succ]; exact product hr ih hs (pow_nonneg hp _) hp

/-- Exact convergent ordered chains, physical multiplication. -/
lemma neumann {E : Table I} {q : ℝ} (hE : Bill a r E q) (hr : 0≤r) (hp : 0≤q) (hq : q<1) (i j : I) :
    HasSum (fun k : ℕ => ((-E)^k) i j) (((1+E)⁻¹) i j) := by
  let T : Table I := Matrix.of fun i j => ∑' k : ℕ, ((-E)^k) i j
  have hh i j : HasSum (fun k : ℕ => ((-E)^k) i j) (T i j) := by
    refine (Summable.of_norm_bounded (summable_geometric_of_lt_one hp hq) ?_).hasSum
    intro k; exact entry hr (power hr (neg hE) hp k) i j
  have he : T*(1+E)=1 := by
    rw [Matrix.mul_add,mul_one]; ext i j
    have ht : (T*E) i j = - (∑' k : ℕ, ((-E)^(k+1)) i j) := by
      have hu (l : I) := (hh i l).mul_right ((-E) l j)
      have hx := (hasSum_sum (fun l (_:l∈Finset.univ)=> hu l)).tsum_eq
      simp_rw [pow_succ, Matrix.mul_apply,hx,Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib,neg_neg]
    have hv := (hh i j).summable.sum_add_tsum_nat_add 1
    rw [(hh i j).tsum_eq] at hv
    rw [Matrix.add_apply, ht]; simp only [Finset.sum_range_one, pow_zero] at hv; linarith
  rw [inv_eq_left_inv he]; exact hh i j
lemma precision_series {C E : Table I} (he : 1+E=A*C) (_hc : C.PosDef) {q : ℝ} (hs : Bill a r E q)
    (hr : 0≤r) (hp : 0≤q) (hq : q<1) (i j : I) : HasSum (fun k : ℕ => ((-E)^(k+1) * A) i j) ((C⁻¹-A) i j) := by
  have hi : (1+E)⁻¹*A=C⁻¹ := by
    have hA : (1+E)*(1+E)⁻¹=1 := by
      have hf : Function.Injective (1+E).mulVecLin := by
        apply LinearMap.ker_eq_bot.mp; apply eq_bot_iff.mpr; intro v hv
        have hz : v + E*ᵥv=0 := by simpa [Matrix.add_mulVec] using (LinearMap.mem_ker.mp hv)
        by_contra H; have hv : v≠0 := H
        have hh : E*ᵥv=-v := by rw [← add_right_inj v, hz]; simp
        have hk := Round.rows_norm _ (unweighted hs hr) v; rw [hh,norm_neg] at hk
        exact hq.not_ge (le_of_mul_le_mul_right ((one_mul _).trans_le hk) (norm_pos_iff.mpr hv))
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (by exact Matrix.mulVec_injective_iff_isUnit.mp hf))
    symm; apply inv_eq_left_inv; rw [Matrix.mul_assoc,← he]; exact mul_eq_one_comm.mp hA
  have hw := hasSum_sum (s:=Finset.univ) (fun l _=> (neumann hs hr hp hq i l).mul_right (A l j))
  change HasSum (fun k : ℕ => ((-E)^k * A) i j) (((1+E)⁻¹*A) i j) at hw
  rw [hi] at hw
  simpa only [Matrix.sub_apply, Finset.sum_range_one,pow_zero, Matrix.one_mul] using (hasSum_nat_add_iff' 1).mpr hw
lemma inverse_error {C E : Table I} (he : 1+E=A*C) (hc : C.PosDef) {q : ℝ} (hs : Bill a r E q)
    (ha : Bill a r A s) (sh : 0≤s) (hr : 0≤r) (hp : 0≤q) (hq : q<1) :
    Bill a r (C⁻¹-A) ( (1-q)⁻¹ * q * s) := by
  have aux (M : Table I) (f : ℕ → Table I) (H : ∀ i j,HasSum (fun k => f k i j) (M i j))
      (he : ∀ k,Green.Rows a a (f k) r (q^(k+1)*s)) : Green.Rows a a M r ((1-q)⁻¹*q*s) := by
    intro i
    have hj (j : I) := ((H i j).summable.abs.mul_left (wt r (a i) (a j)))
    calc
      _ ≤ ∑ j, ∑' k : ℕ, wt r (a i) (a j)* |f k i j| := by
        refine Finset.sum_le_sum fun j _=> ?_
        rw [tsum_mul_left,← (H i j).tsum_eq]
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (H i j).summable.norm) (wt_pos ..).le
      _ ≤ _ := by rw [← Summable.tsum_finsetSum (fun j _=>hj j)]; apply ((summable_sum (fun j (_:j∈Finset.univ)=> hj j)).tsum_le_tsum (fun k=> he k i)
            ((((hasSum_geometric_of_lt_one hp hq).mul_right q).mul_right s).summable)).trans_eq
                    ((((hasSum_geometric_of_lt_one hp hq).mul_right q).mul_right s).tsum_eq)
  have hpower k := product hr (power hr (neg hs) hp (k+1)) ha (pow_nonneg hp (k+1)) sh
  have H := precision_series he hc hs hr hp hq
  exact ⟨aux _ _ H fun k => (hpower k).1,aux _ _ (fun i j => H j i) fun k => (hpower k).2⟩
end Rows
end YM.Further.CurvedGaussianJets
