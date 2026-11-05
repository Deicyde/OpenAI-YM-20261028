import YM.Org.Theatre
import YM.Push.STATIONARY_UNIFORM.Calculus

/-!
# Polynomial price for implicit jets

All norms those of actual input/output spaces. No claim on analytic strip; estimates
on real derivatives where the given branch is real analytic. For later locality one
may also re-use the first assertion which peels out the solved-for term, so no
sum over a *spurious* output of the unknown at same order in it. No dividing by
factorials here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric
open scoped Topology ContDiff BigOperators

section Combinatorics

def onePart (n : ℕ) : OrderedFinpartition (n+1) where
  length := 1
  partSize _ := n+1
  partSize_pos _ := Nat.succ_pos n
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint _ _ _ _ hij := False.elim (hij (Subsingleton.elim ..))
  cover i := ⟨0,i,rfl⟩

lemma unique_onePart {n : ℕ} (c : OrderedFinpartition (n+1)) (h : c.length=1) : c=onePart n := by
  have he : ∑ i : Fin c.length, c.partSize i = n+1 := by simpa using c.sum_sigma_eq_sum (fun _ => (1:ℕ))
  cases c with
  | mk l size hp e hm hs hd hc =>
    dsimp at *
    subst l
    have ha : size = fun _ => n+1 := by
      simp at he; simpa only [funext_iff, Fin.forall_fin_one] using he
    subst size
    have ha : e = fun _ => id := funext fun i => le_antisymm (hm i).le_id (hm i).id_le
    subst e; rfl

lemma smaller_parts {n : ℕ} (c : OrderedFinpartition (n+1)) (h : c ≠ onePart n) (i : Fin c.length) : c.partSize i ≤ n := by
  have he := NeZero.of_pos (c.length_pos (Nat.succ_pos _))
  have hl : 1 < c.length := lt_of_le_of_ne (c.length_pos (Nat.succ_pos _)) (fun h' => h (unique_onePart c h'.symm))
  haveI : Nontrivial (Fin c.length) := by
    apply Fintype.one_lt_card_iff_nontrivial.mp; simpa
  obtain ⟨j,hj⟩ := exists_ne i
  have hs := Finset.single_le_sum (fun k _ => Nat.zero_le (c.partSize k))
    (show j∈Finset.univ.erase i from Finset.mem_erase_of_ne_of_mem hj (Finset.mem_univ j))
  have hr := Finset.sum_erase_add _ c.partSize (Finset.mem_univ i)
  have H : ∑ i : Fin c.length, c.partSize i = n+1 := by simpa using c.sum_sigma_eq_sum (fun _ => (1:ℕ))
  have hx := c.partSize_pos j
  omega
end Combinatorics

section Jets
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {x : E} {f : E → F} {g : F → G}

lemma comp_step (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g (f x)) (k : ℕ) :
    iteratedFDeriv ℝ (k+1) (g ∘ f) x =
      (fderiv ℝ g (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ (k+1) f x) +
      ∑ c ∈ Finset.univ.erase (onePart k),
        (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c := by
  rw [iteratedFDeriv_comp hg hf le_top, FormalMultilinearSeries.taylorComp,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (onePart k))]
  congr 1
  ext v
  change iteratedFDeriv ℝ 1 g (f x) _ = _
  rw [iteratedFDeriv_one_apply]; rfl

/-- Besides the equation's own jet budget `M`, the branch's value `R` and
invertibility budget `C`, pay also Id on the horizontal (assumes input norm
at evaluation at most one). Unoptimized bound, polynomial in `R,M,C`.
-/
def implicitCost (R M C : ℝ) : ℕ → ℝ
  | 0 => R
  | n+1 => let I := implicitCost R M C n
           I + C * (M + (Fintype.card (OrderedFinpartition (n+1)):ℝ) * M * (1+I)^(n+1))

lemma implicit_jets {g : E × F → G} {R M C : ℝ}
    (k : ℕ) (hx : ‖x‖ ≤ 1) (hc : ‖f x‖ ≤ R) (h : g ∘ (fun z => (z, f z)) =ᶠ[𝓝 x] 0)
    (hf : ContDiffAt ℝ ω f x) (hg : Allows k g (x, f x) M)
    (hC : 0≤C) (ht : ∀ v : F, ‖v‖ ≤ C * ‖fderiv ℝ g (x, f x) (0,v)‖) :
    Allows k f x (implicitCost R M C k) := by
  induction k with
  | zero => refine ⟨hf, fun i hi => ?_⟩; rw [show i = 0 by omega, norm_iteratedFDeriv_zero]; exact hc
  | succ n ih =>
    let B := implicitCost R M C n
    let N := n+1
    have hp := ih (hg.order (Nat.le_succ _))
    have hh : 0 ≤ B := hp.nonneg
    have hm := hg.nonneg
    have heB : B ≤ implicitCost R M C N := le_add_of_nonneg_right
      (mul_nonneg hC (add_nonneg hm (mul_nonneg (mul_nonneg (by positivity) hm) (pow_nonneg (by linarith) _))))
    refine ⟨hf, fun i hi => ?_⟩
    rcases eq_or_lt_of_le hi with hi|hi
    swap
    · exact (hp.norm_le i (by omega)).trans heB
    subst i
    refine ContinuousMultilinearMap.opNorm_le_bound (hh.trans heB) fun v => ?_
    let I := ContinuousLinearMap.id ℝ E
    let T (z : E) := (z, f z)
    have hi (j : ℕ) : Allows j I x 1 := allows_linear ContinuousLinearMap.norm_id_le hx
    have he : Allows n T x (1+B) :=
      ((hi n).mono (le_add_of_nonneg_right hh)).pair (hp.mono (le_add_of_nonneg_left zero_le_one))
    let m := Fintype.card (OrderedFinpartition N)
    let J (c : OrderedFinpartition N) := (ftaylorSeries ℝ g (T x)).compAlongOrderedFinpartition (ftaylorSeries ℝ T x) c
    let S := Finset.univ.erase (onePart n)
    have HS : ‖∑ c∈S, J c‖ ≤ (m:ℝ) * (M * (1+B)^N) := by
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ _c∈S, M * (1+B)^N := Finset.sum_le_sum fun c hc => by
          have hj := c.norm_compAlongOrderedFinpartition_le (iteratedFDeriv ℝ c.length g (T x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) T x)
          apply hj.trans (mul_le_mul (hg.norm_le _ c.length_le) ?_ (by positivity) hm)
          calc
            _ ≤ ∏ _i : Fin c.length, (1+B) := Finset.prod_le_prod
              (fun _ _ => norm_nonneg _) (fun i _ => he.norm_le _ (smaller_parts c (Finset.ne_of_mem_erase hc) i))
            _ = (1+B)^c.length := by simp
            _ ≤ _ := pow_le_pow_right₀ (by linarith) c.length_le
        _ = (S.card:ℝ)*(M*(1+B)^N) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (by positivity)
    let U := fderiv ℝ g (T x)
    let q := iteratedFDeriv ℝ N I x v
    let y := iteratedFDeriv ℝ N f x v
    have hz : U (q,0) + U (0,y) + (∑ c∈S, J c) v = 0 := by
      have hh : iteratedFDeriv ℝ N (g ∘ T) x=0 := by
        change (iteratedFDeriv ℝ N (g ∘ fun z => (z, f z))) x=0
        rw [(h.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds, iteratedFDeriv_zero]; rfl
      have ha := comp_step he.analytic (show ContDiffAt ℝ ω g (T x) from hg.analytic) n
      have hb : iteratedFDeriv ℝ N T x v=(q,y) := by
        change iteratedFDeriv ℝ N (fun z => (I z,f z)) x v=_
        rw [iteratedFDeriv_prodMk I.contDiff.contDiffAt hf le_top]; rfl
      have hsum := congr_arg (fun H : ContinuousMultilinearMap ℝ (fun _ : Fin N => E) G => H v) (ha.symm.trans hh)
      change U (iteratedFDeriv ℝ N T x v) + (∑ c∈S,J c) v = 0 at hsum
      rw [hb] at hsum
      rw [← map_add]; simpa only [Prod.mk_add_mk,add_zero,zero_add] using hsum
    have hu : ‖U‖ ≤ M := by
      unfold U; rw [← norm_iteratedFDeriv_one g]; exact hg.norm_le 1 (by omega)
    let L := ∏ i, ‖v i‖
    have hx : ‖U (q,0)‖ ≤ M*L := by
      apply (U.le_opNorm _).trans (mul_le_mul hu ?_ (norm_nonneg _) hm)
      have hw : ‖q‖ ≤ 1*L := by
        exact ((iteratedFDeriv ℝ N I x).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((hi N).norm_le _ le_rfl) (by positivity))
      simpa using hw
    have hw : ‖U (0,y)‖ ≤ (M+(m:ℝ)*M*(1+B)^N) * L := calc
      _ = ‖-(U (q,0) + (∑ c∈S,J c) v)‖ := congr_arg norm (by grind)
      _ ≤ ‖U (q,0)‖ + ‖(∑ c∈S,J c) v‖ := by rw [norm_neg]; exact norm_add_le ..
      _ ≤ M*L + ((m:ℝ)*(M*(1+B)^N))*L := add_le_add hx (((∑ c∈S,J c).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right HS (by positivity)))
      _ = _ := by ring
    apply (ht y).trans ((mul_le_mul_of_nonneg_left hw hC).trans ?_)
    change _ ≤ (B+C* _) * L; rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hh) (by unfold L; positivity)
end Jets
end YM.Push.Uniform
