import YM.Push.LOCAL_SPLITTING.Calculus


set_option warningAsError false

/-!
# Domain and primitive atom receipts

A common window on the representatives (in particular sufficient on
hard-flag equality faces!). No radii taken *separately for each atom*
in a countable test, and no changing the branch during differentiation. These data may be requested at a trajectory point, or for a whole fixed
interval of parameters with the SAME choices. The window opens on the physical link fields,
pre-mask. It can depend on the ambient stage/period and the support (to
prove jets at a given stage we just need openness); the *support cost*
is separate and in integration it may well be necessary to prove a
more precise uniform window.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.LogJets
open RG Wilson Lattice Push.Local  Filter Function Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

/-- Window family. Larger-support good sets provide at least the field
neighborhoods needed for the smaller supports. This needn't be how the
representatives themselves are computed (they are globally defined,
Borel, healthy masks unchanged). -/
structure Windows (P : BudgetPoint) (G : Gauge) (n : Side) where
  openAt : Support n → Set (Config G n)
  opens (S) : IsOpen (openAt S)
  fits (S U) : Healthy P.threshold S U → U ∈ openAt S
  less {S T} : S ⊆ T → openAt T ⊆ openAt S

variable {P : BudgetPoint} {G : Gauge} {n : Side} {ι : Type*}
variable (W : Windows P G n)

namespace Windows

/-- Example using any positive margin beyond the actual hard flags. -/
def buffered (ε : ℝ) (he : 0 < ε) : Windows P G n where
  openAt X := {U | ∀ (p : Face (Per n)), ¬ Disjoint X (touched p) → G.chord (faceValue U p) < P.threshold + ε}
  opens X := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite; intro p
    by_cases hh : Disjoint X (touched p)
    · simp [hh]
    simp only [hh, not_false_eq_true,true_imp_iff]
    unfold faceValue
    exact isOpen_lt (by fun_prop) continuous_const
  fits X U h p hp := by
    have hk : G.chord (faceValue U p) ≤ P.threshold := by
      by_contra! hv
      obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp hp
      exact Finset.disjoint_left.mp h hx ((flags_spec ..).mpr ⟨p,hy,hv⟩)
    linarith only [he,hk]
  less h U hu p hp := hu p (fun hd => hp (hd.mono_left h))

/-- A pre-mask coefficient on the true complete support, using the
same C^k extensions at every point of the window. No gauge-coordinate
jet is replaced by an ordinary symmetric iterate. -/
structure Germ (S : Support n) (f : Config G n → ℝ) : Prop where
  probes : LocalOn S f
  borel : Measurable f
  symm : GaugeInvariant f
  smooth (U) : U ∈ W.openAt S → Chart P.order f U

def Cap (o : Site n) (S : Support n) (f : Config G n → ℝ) (v : ℝ) :=
  0 ≤ v ∧ ∀ U ∈ W.openAt S, ∀ l : List (Directions G n), l.length ≤ P.order →
    (∀ a ∈ l, P.dirBound o a) → ‖leftDerivs f l U‖ ≤ v

variable {W} {S : Support n} {o : Site n} {f : Config G n → ℝ} {v : ℝ}



theorem Cap.paid (h : W.Cap o S f v) : P.supBounds o S f v :=
  ⟨h.1, fun U hu => h.2 U (W.fits S U hu)⟩

theorem Germ.scale (h : W.Germ S f) (a : ℝ) : W.Germ S (fun U => a * f U) := by
  exact ⟨fun U V hv => congr_arg (a * ·) (h.probes U V hv), measurable_const.mul h.borel,
    fun t U => congr_arg (a * ·) (h.symm t U),
    fun U hu => contDiffAt_const.mul (h.smooth U hu)⟩

end Windows

/-- Output-independent scalar (including a comparison amplitude). -/
lemma left_constant_mul (f : Config G n → ℝ) (a : ℝ) (l : List (Directions G n)) :
    leftDerivs (fun U => a * f U) l = fun U => a * leftDerivs f l U := by
  induction l with
  | nil => rfl
  | cons b l ih => funext U; simp_rw [leftDerivs, ih]; exact deriv_const_mul_field ..

namespace Windows
variable {W} {S : Support n} {o : Site n} {f : Config G n → ℝ} {a r v : ℝ}


end Windows

/-- Input jets of all counted atoms of the first unforced gas. Requires
control BEFORE flag masking, on true orders through k on the W domain;
none of these predicates require estimates on log coefficients at output.
Alphabet countability will be used separately for Borel results on
regions where the raw representatives needn't be smooth. -/
structure AtomJets (X : ι → Support n) (o : ι → Site n) (E : ι → Config G n → ℝ) (v : ι → ℝ) : Prop where
  anchor (i : ι) : o i ∈ X i
  germ (i) : W.Germ (X i) (E i)
  owns (i) : W.Cap (o i) (X i) (E i) (v i)

namespace AtomJets
variable {W} {X : ι → Support n} {o : ι → Site n} {E : ι → Config G n → ℝ} {v : ι → ℝ}

lemma full (h : AtomJets W X o E v) (i : ι) : (X i).Nonempty := ⟨o i,h.anchor i⟩






end AtomJets

/-! The next two lemmas convert the budget's position-weighted direction
bounds to the pointwise Termwise criterion. No amounts from these
auxiliary scales charged; the true jets are paid at actual dirBound. -/

lemma can_shrink (P : BudgetPoint) (l : List (Directions G n)) :
    ∃ r : ℝ, 0 < r ∧ ∀ o : Site n, ∀ a ∈ l, P.dirBound o (r • a) := by
  classical
  let c := 1 + ∑ a∈l.toFinset, ‖a‖
  have hc : 0 < c := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have h i (hi : i∈l) : ‖i‖ ≤ c :=
    (Finset.single_le_sum (fun j _ => norm_nonneg j) (List.mem_toFinset.mpr hi)).trans
      (le_add_of_nonneg_left zero_le_one)
  let r := P.threshold / c
  have hr : 0 < r := div_pos P.threshold_pos hc
  refine ⟨r,hr,fun o a ha e => ?_⟩
  rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hr.le]
  apply (mul_le_mul_of_nonneg_left ((norm_le_pi_norm a e).trans (h a ha)) hr.le).trans
  unfold r; rw [div_mul_cancel₀ _ hc.ne']
  exact le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp))



end YM.Further.LogJets
