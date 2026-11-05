import Mathlib.Analysis.LocallyConvex.HahnBanach
import YM.Contact.Trial

/-! Simultaneous finite-test order seminorms for normal-coordinate tests, not Borel norms of
kernels. -/

noncomputable section
set_option autoImplicit false
open Function Set Seminorm
open scoped BigOperators BoundedContinuousFunction ContDiff
namespace YM.Contacts
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (E)

def jetMap (j:ℕ) : Trial E →ₗ[ℂ] BoundedContinuousFunction E (E [×j]→L[ℝ] ℂ) where
  toFun φ:= let B:=(Trial.majorant j φ).choose
            BoundedContinuousFunction.ofNormedAddCommGroup _
              ((φ.orders j).continuous_iteratedFDeriv (m:=j) le_rfl) B (fun _=>(Trial.majorant j φ).choose_spec j le_rfl _)
  map_add' φ ψ:=by
    apply BoundedContinuousFunction.ext
    intro x; change (iteratedFDeriv ℝ j _ x)=iteratedFDeriv ℝ j (φ:E→ℂ) x+iteratedFDeriv ℝ j (ψ:E→ℂ) x
    rw [show ⇑(φ+ψ)=(φ:E→ℂ)+ψ from rfl,iteratedFDeriv_add (φ.orders _) (ψ.orders _)]; rfl
  map_smul' c φ:= by
    ext1 x; change iteratedFDeriv ℝ j (c • (φ:E→ℂ)) x = c • iteratedFDeriv ℝ j ⇑φ x; exact iteratedFDeriv_const_smul_apply (φ.orders _|>.contDiffAt)

def seminorm (j:ℕ) : Seminorm ℂ (Trial E):=
    (Finset.range (j+1)).sup (fun i=> (normSeminorm ℂ (E →ᵇ E [×i]→L[ℝ] ℂ)).comp (jetMap E i))
variable (j:ℕ)
lemma sem_nonneg (x) : 0 ≤ seminorm E j x:= apply_nonneg ..

lemma controls_order (φ:Trial E): Major j φ (seminorm E j φ):=by
   let s (i):= (normSeminorm ℂ (E →ᵇ E [×i]→L[ℝ] ℂ)).comp (jetMap E i)
   intro i hi a
   have ht := BoundedContinuousFunction.norm_coe_le_norm (jetMap E i φ) a
   exact ht.trans ((show s i ≤ (Finset.range (j+1)).sup s from Finset.le_sup (Finset.mem_range_succ_iff.mpr hi)) φ)
lemma order_le' {φ:Trial E}{B:ℝ}(h:Major j φ B):seminorm E j φ ≤ B:=by
  unfold seminorm; -- use `Finset.sup_apply` maybe
  suffices he:∀ I:Finset ℕ,I⊆Finset.range (j+1)→
                       (I.sup fun i=> (normSeminorm ℂ (E →ᵇ E [×i]→L[ℝ] ℂ)|>.comp (jetMap E i))) φ≤B from he _ (subset_refl _)
  intro I hI; classical induction I using Finset.induction_on with
  | empty=> exact h.nonneg
  | insert i I ha ih=>
    simp only [Finset.sup_insert,Seminorm.sup_apply, max_le_iff]
    refine ⟨(BoundedContinuousFunction.norm_le h.nonneg).mpr fun x=> h i (Finset.mem_range_succ_iff.mp ((Finset.insert_subset_iff.mp hI).1)) x,ih (Finset.insert_subset_iff.mp hI).2⟩

end YM.Contacts
