import YM.TraceExtension.Fock.Age

/-! Splitting lemma inside the growth-gated module. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {n k : ℕ}

lemma eigen_mono : StrictMono eigenFee := fun _ _ h => by unfold eigenFee; gcongr ; norm_num
lemma signal_add (i : Fin n) (k : ℕ) (q r : Wave n) : signalPoly i (q+r) k=signalPoly i q k+signalPoly i r k := by
    induction k with
    | zero => rfl
    | succ k h=> unfold signalPoly; rw [h,map_add,smul_add]; abel
lemma signal_smul (i : Fin n) (k : ℕ) (c : ℝ) (q : Wave n) : signalPoly i (c • q) k=c • signalPoly i q k := by
    induction k with
    | zero=> rfl
    | succ k h=> unfold signalPoly; rw [h,map_smul,smul_sub,smul_comm _ c]
def operates (i : Fin n) (k : ℕ) : Module.End ℝ (Wave n) :=
    IsLinearMap.mk' (fun q=>signalPoly i q k) ⟨signal_add i k, signal_smul i k⟩
lemma operative (i : Fin n) (k) (p) : operates i k p=signalPoly i p k := rfl
lemma roots_commute (i j : Fin n) (k) : Commute (operates i k) (zoom j) := by
    apply LinearMap.ext; intro x; simp only [Module.End.mul_apply,operative]
    induction k with
    | zero=> rfl
    | succ k h=>
        unfold signalPoly; rw [h,map_sub,map_smul]
        rw [show zoom i (zoom j _)=zoom j (zoom i _) from LinearMap.congr_fun (different i j) _]
lemma under (i : Fin n) (k) {p : Wave n} {S : Submodule ℝ (Wave n)} (h : ∀ x∈ S, zoom i x∈ S) (hp : p∈S) : signalPoly i p k∈S := by
    induction k with
    | zero=> exact hp
    | succ k ih=> exact S.sub_mem (h _ ih) (S.smul_mem _ ih)
lemma calculate (i : Fin n) (k : ℕ) (p : Wave n) (d : ℝ) (hd : zoom i p=d • p) :
    signalPoly i p k = (∏ j∈Finset.range k, (d-eigenFee j)) • p := by
    induction k with
    | zero=> simp [signalPoly]
    | succ k h=> rw [signalPoly,h,map_smul,hd, Finset.prod_range_succ]; module

def mainSet (S : Submodule ℝ (Wave n)) (u : Finset (Fin n)) (k : ℕ) :=
    {p∈ (S : Set (Wave n)) | ∀ j∈u, ∃ d, d < k ∧ zoom j p=eigenFee d • p}

/-- Multi-eigen splitting preserving a restriction only required stable in those slots. -/
lemma splitParts (S : Submodule ℝ (Wave n)) (u : Finset (Fin n)) (k : ℕ)
    (p : Wave n) (hs : p∈S) (hu : ∀ i∈u, ∀ x∈S, zoom i x∈S) (hp : ∀ i∈u, signalPoly i p k=0) :
    p∈ Submodule.span ℝ (mainSet S u k) := by
    induction u using Finset.induction_on generalizing S p with
    | empty => exact Submodule.subset_span (by simp [mainSet,hs])
    | insert i u he ih =>
        let U := insert i u; let B:=mainSet S U k; let A:=Submodule.span ℝ B
        have hx (j hj) := hu j (Finset.mem_insert_of_mem hj)
        have hi := hu i (Finset.mem_insert_self ..)
        have hJ (w : Wave n) (hw:w∈ S) (h : ∀ j∈u, signalPoly j w k=0) (s) (hr:s<k) (hy : zoom i w=eigenFee s • w) : w∈A := by
            let Q := Module.End.eigenspace (zoom i) (eigenFee s); let T := S ⊓ Q
            have hm : w ∈ T := ⟨hw,Module.End.mem_eigenspace_iff.mpr hy⟩
            have hg (j) (hj:j∈u) (x : Wave n) (h:x∈T) : zoom j x∈T :=
                ⟨hx j hj x h.1,Module.End.mem_eigenspace_iff.mpr (by
                 rw [show zoom i (zoom j _)=zoom j (zoom i _) from LinearMap.congr_fun (different i j) x,Module.End.mem_eigenspace_iff.mp h.2,map_smul])⟩
            refine Submodule.span_mono (s:=mainSet T u k) (t:=B) ?_ (ih T w hm hg h)
            rintro v ⟨⟨hv,hQ⟩,hq⟩; refine ⟨hv,fun j hj=>?_⟩
            rcases Finset.mem_insert.mp hj with rfl|h; exact ⟨s,hr, Module.End.mem_eigenspace_iff.mp hQ⟩
            exact hq j h
        let R := S ⊓ ⨅ j:↥(u:Set (Fin n)),LinearMap.ker (operates j k)
        have hw (z) : z∈R ↔ z∈S ∧ ∀ j∈u, signalPoly j z k=0 := by
            simp only [R,Submodule.mem_inf, Submodule.mem_iInf,Subtype.forall]; rfl
        have ha (z) (hz:z∈R) : zoom i z∈R := by
            refine (hw _).2 ⟨hi z hz.1,fun j hj=>?_⟩
            rw [← operative,show operates j k (zoom i z) = zoom i (operates j k z) from LinearMap.congr_fun (roots_commute j i k) z,operative, (hw z|>.1 hz).2 j hj,map_zero]
        have reduce (t : ℕ) (ht : t ≤ k) (z) (hz:z∈ R) (h : signalPoly i z t=0) : z∈A := by
            induction t generalizing z with
            | zero => rw [show z=0 from h]; exact A.zero_mem
            | succ t ih =>
                let v := signalPoly i z t
                have hu : v∈ R := under _ _ ha hz
                have hg : zoom i v=eigenFee t • v := sub_eq_zero.mp h
                have he := hJ v ((hw v).1 hu).1 ((hw v).1 hu).2 _ ht hg
                let b := ∏ j∈Finset.range t,(eigenFee t-eigenFee j)
                have hb : 0<b := Finset.prod_pos fun j hj=> sub_pos.mpr (eigen_mono (Finset.mem_range.mp hj))
                have hd : signalPoly i (z-b⁻¹ • v) t=0 := by
                    rw [← operative,map_sub,map_smul, operative i t z, operative, calculate i t v _ hg];
                    change v-b⁻¹ • b • v=0; rw [smul_smul, inv_mul_cancel₀ hb.ne',one_smul,sub_self]
                have hy := A.add_mem (ih (Nat.le_of_succ_le ht) _ (R.sub_mem hz (R.smul_mem _ hu)) hd) (A.smul_mem b⁻¹ he); rwa [sub_add_cancel] at hy
        exact reduce k le_rfl p ((hw p).2 ⟨hs,fun j hj=> hp j (Finset.mem_insert_of_mem hj)⟩) (hp _ (Finset.mem_insert_self ..))
end YM.TraceExtension.Photons
