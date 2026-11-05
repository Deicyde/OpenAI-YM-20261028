import YM.Fields.Star
import YM.Shift.Cut
import YM.Shift.Ridge


/-!
# Half -> actual absolute cone; testing Lorentz transport

'Half' here dual of ascending time-axis shifts. Encodes all cumulative suffix
in all n relative times; cone derived from JOINT identities without reducing
test arity. Mixed (absolute) common translation-free arguments use partial
closed heights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Filter Set Distribution Probe MeasureTheory Mink Mink.Poincare
open scoped Topology InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}

def half (n : ℕ) := ⋂ (y : sunrise n), {p : Points n|0 ≤ inner ℝ (dawn y.val) p}
lemma submissive (n) : IsClosed (half n) := isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)

def coneM (n : ℕ) := ⋂ K : Lorentz, (togetherL (Lorentz.dual K) n) ⁻¹' half n
lemma closedM (n) : IsClosed (coneM n) := isClosed_iInter fun _ => (submissive _).preimage (togetherL ..).continuous
@[simp] lemma pit (n : ℕ) : (0 : Points n) ∈ coneM n := by simp [coneM,half]
lemma basis_half {p : Points n} (h : p∈half n) (y : Heights n) (hp : y∈sunrise n) :
    0 ≤ ∑ i,y i * YM.time (p i) := by
  have he : 0≤ inner ℝ (dawn y) p := mem_iInter.mp h ⟨_,hp⟩
  rw [PiLp.inner_apply] at he; simpa [dawn,pairing, place, add_comm] using he

lemma present {p : Points n} (h : p∈coneM n) (K : Lorentz) : togetherL (Lorentz.dual K) n p∈half n :=
  mem_iInter.mp h K

/-- all incl total (j=0), including empty j. -/
def suffixP (p : Points n) (j : ℕ) := ∑ k : Fin n, if j ≤ k.val then p k else 0
@[simp] lemma after_n {p : Points n} : suffixP p n=0 := by simp [suffixP,fun i : Fin n => not_le.mpr i.isLt]
lemma selectedP (b : Lorentz) (p : Points n) (j) : suffixP (togetherL b _ p) j=b.act (suffixP p j) := by
  unfold suffixP; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by split <;> simp_all
lemma see_half {p : Points n} (h : p∈half n) (j : ℕ) : 0≤YM.time (suffixP p j) := by
  let v (i : Fin n) := if j ≤ i.val then (1:ℝ) else 0
  have hv : v∈sunrise n := by
    intro i k hik; change v i ≤ v k; simp only [v]; split_ifs with a b b
    · rfl
    · exact False.elim (b <| a.trans hik)
    · norm_num
    rfl
  have he := basis_half h v hv
  change 0≤clockL (suffixP _ _)
  unfold suffixP; rw [map_sum]
  refine he.trans_eq (Finset.sum_congr rfl fun i _ => by unfold v; split_ifs <;> simp)

lemma sees {p : Points n} (h : p∈coneM n) (j) : suffixP p j∈cone := (Lorentz.from_half _).2
  fun K => by rw [← selectedP]; exact see_half (present h K) j
lemma conc_zero {p : Points n} (h : p∈half n) : YM.time (suffixP p 0)=0 := by
  refine le_antisymm ?_ (see_half h 0)
  have he := basis_half h (fun _ => (-1)) (show (fun _ : Fin n => (-1:ℝ))∈sunrise n from monotone_const)
  simp only [neg_mul,one_mul, Finset.sum_neg_distrib,Right.nonneg_neg_iff] at he
  change clockL _≤0; unfold suffixP; simpa [map_sum] using he
lemma low {p : Points n} (h : p∈coneM n) : YM.time (suffixP p 0)=0 := by
  have he : Lorentz.dual 1=1 := Lorentz.ext _ _ fun x => by
    change General.walk Lorentz.reverseL (General.walk Lorentz.reverseL x)=x;simp
  have hv := present h 1; rw [he] at hv
  simpa [selectedP] using conc_zero hv
lemma total {p : Points n} (h : p∈coneM n) : suffixP p 0=0 := by
  apply Mink.ext_by
  · apply norm_eq_zero.mp _ |>.trans (map_zero Mink.restL).symm
    refine le_antisymm ?_ (norm_nonneg _); exact le_trans (sees h 0) (low h).le
  rw [low h,Mink.clock_zero]

def shores (n : ℕ) := ⋂ (i : Fin n) (j : Fin n) (_ : i.val+1=j.val), {y : Points n| y j-y i∈cone}
def fields (n : ℕ) := ⋂ (i : Fin n) (j : Fin n) (_ : i.val+1=j.val), {y : Points n| y j-y i∈inside}
lemma smooth_fields (n) : IsOpen (fields n) := isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => open_inside.preimage (by fun_prop)

lemma etched {y : Heights n} (h : y∈east n) : dawn y∈fields n := by
  simp only [fields,mem_iInter]; intro i j H
  change ‖spatial _‖<YM.time _; rw [sub_eq_add_neg,rest_add,clock_add,rest_neg,clock_neg]; simp only [dawn,place,points,WithLp.ofLp_toLp,spatial_position,
    time_position,Pi.zero_apply, neg_zero,add_zero,norm_zero]; have ht := h (show i<j by omega); linarith

section
variable {G : Gauge} {L : Register G} {S : Table L}

/-- needed in all scopes (bar commutativity later). -/
structure Urs (W : Surface S) (K : Spins S) : Prop where
  translation (n : ℕ) (v : Fin n → S.Union) (x : Joint n) (a : E4) : W.W n v (Joint.gpush n (Poincare.translation a) x)=W.W n v x
  rotation (n : ℕ) (v : Fin n → S.Union) (x : Joint n) (r : Lorentz) : W.W n (fun i => K.rail r (v i)) (along (togetherL r _).symm x) = W.W n v x

lemma parr (r : Lorentz) (p x : Points n) : inner ℝ (togetherL r _ p) (togetherL (Lorentz.dual r) _ x)=inner ℝ p x := by
  simp_rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro i _; exact Lorentz.dual_sent _ _ _
lemma acrossV (r : Lorentz) (n) : MeasurePreserving (togetherL r n) volume volume := by
  have he := together (motion r) n
  rw [show ⇑(togetherL r n)= (motion r).zusammen n from funext fun x => PiLp.ext fun i => by simp [zusammen]]
  exact he

lemma turns (r : Lorentz) (x : Joint n) : hat (along (togetherL (Lorentz.dual r) _).symm x)=
    along (togetherL r _).symm (hat x) := by
  ext1 y
  rw [along_at,hat_eq,hat_eq]
  have hp := acrossV (Lorentz.dual r) n
  let A := togetherL (Lorentz.dual r) n
  rw [← hp.integral_comp (A.toHomeomorph.toMeasurableEquiv.measurableEmbedding)]
  simp_rw [Probe.along_at, ContinuousLinearEquiv.symm_apply_apply]
  congr! 2
  unfold plane; congr! 3;
  rename_i u; rw [← real_inner_comm (togetherL (Lorentz.dual r) n u), ← real_inner_comm u, ← parr r (-(togetherL r n).symm y)]; simp

lemma tents (W : Surface S) (K : Spins S) (h : Urs W K) (hv : ∀ (v : Fin n → S.Union), dsupport (Distn.fourier (W.W n v)) ⊆ half n) (p : Fin n → S.Union) :
    dsupport (Distn.fourier (W.W n p)) ⊆ coneM n := by
  rw [coneM]; apply subset_iInter; intro i
  let A := togetherL (Lorentz.dual i) n
  apply (Distn.due (Distn.fourier (W.W n p)) (A⁻¹' half n) ((submissive n).preimage A.continuous)).2
  intro t ht
  let z := along A.symm t
  let q := fun j => K.rail i (p j)
  have hZ : tsupport z ⊆ (half n)ᶜ := by
    have he : tsupport z ⊆ A.symm ⁻¹' tsupport t := by
      refine closure_minimal ?_ ((isClosed_tsupport t).preimage A.symm.continuous)
      intro x hx; exact subset_tsupport _ hx
    intro x hx hI; apply ht (he hx)
    rw [Set.mem_preimage]; rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hp := (Distn.due (Distn.fourier (W.W n q)) (half n) (submissive n)).mp (hv q) z hZ
  change W.W n _ (hat _)=_; rw [← h.rotation n p _ i, ← turns]; exact hp
end
end YM.Boundary
