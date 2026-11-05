import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Planned.ATOM_REGULAR_ESTIMATE.EdgeTaylor

/-! Pi-varying reads. No formal analyticity of field on Snap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor Lattice Wilson RG Source Labels Source.Drops Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

lemma arity {n : ℕ} (k : Fin n → ℕ) (h : ∀ i, 0 < k i) : n ≤ ∑ i, k i := by
  have hh : (∑ _i : Fin n, (1:ℕ)) ≤ ∑ i, k i := Finset.sum_le_sum (fun i _ => h i)
  simpa using hh

private lemma payments {n m : ℕ} {r : Fin m → Fin n} (w : Fin n → ℕ) (hr : Surjective r)
    (hp : ∀ i, 0 < w i) : (∑ i, w i) = (∑ i, w (r i)) ↔ n=m := by
  constructor
  · intro he
    have hr' := hr
    choose f hf using hr
    have hz : Injective f := fun i j hh => (hf i).symm.trans ((congr_arg r hh).trans (hf j))
    have h1 : n ≤ m := by simpa using Fintype.card_le_of_surjective r hr'
    by_contra hn
    let M := Finset.univ.image f
    have hM : M.card=n := (Finset.card_image_of_injective _ hz).trans ((Finset.card_univ).trans (Fintype.card_fin _))
    have ht : M.card < (Finset.univ:Finset (Fin m)).card := by simp [hM]; omega
    obtain ⟨x,hx,h⟩ := Finset.exists_mem_notMem_of_card_lt_card ht
    have he' : ∑ i∈M, w (r i)=∑ i,w i := by rw [Finset.sum_image (fun i _ j _ e => hz e)]; simp_rw [hf]
    have hc := Finset.sum_lt_sum_of_subset (f:=fun i => w (r i)) (Finset.subset_univ M) hx h (hp _) (fun i _ _ => Nat.zero_le _)
    omega
  rintro rfl
  exact ((Equiv.ofBijective r ⟨Finite.injective_iff_surjective.mpr hr,hr⟩).sum_comp w).symm

/-- Knowing derivatives of curves passing through all *subsets* of slots
(the projection tests have all amplitudes, stronger), one obtains the requested
mixed polar. Allow unequal powers of the slots, compare true derivatives.
-/
theorem polar_snap {m k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℂ} (w : Fin m → ℕ)
    (hp : ∀ i, 0 < w i) (x : Fin m → E) (u : ℝ → Fin m → E) (hu : ∀ t i,u t i = t^(w i) • x i)
    (hF : ContDiffAt ℝ k F 0) (hk : (∑ i,w i)≤k)
    (h : ∀ s : Finset (Fin m), iteratedDeriv (∑ i,w i) (fun t => F (∑ i∈s,u t i)) 0=0) :
    iteratedFDeriv ℝ m F 0 x = 0 := by
  let l := ∑ i,w i
  have hl : m≤k := (arity w hp).trans hk
  let P := Work.G05.blockTaylor k F
  let T i := Tensor.coeff F i 0
  let v (s : Finset (Fin m)) (t : ℝ) := ∑ i∈s,u t i
  have hw (s) : ContDiff ℝ k (v s) := by
    unfold v; simp_rw [hu]; exact ContDiff.sum fun i _ => (contDiff_id.pow (w i)).smul contDiff_const
  have hQ (s) : iteratedDeriv l (P ∘ v s) 0 = 0 := by
    have h₁ : v s 0 = 0 := Finset.sum_eq_zero (fun i _ => by rw [hu]; simp [(hp i).ne'])
    have he : iteratedFDeriv ℝ l (P ∘ v s) 0 = iteratedFDeriv ℝ l (F ∘ v s) 0 := by
      refine Work.G05.jets_comp ((hw s).contDiffAt) ((hw s).contDiffAt) (Work.G05.blockTaylor_contDiff .. |>.contDiffAt)
        (?_) rfl (fun _ _ => rfl) ?_ l hk
      · rwa [h₁]
      rw [h₁]; exact Work.G05.blockTaylor_jets hF
    change iteratedFDeriv ℝ l (P ∘ v s) 0 _ = _
    rw [he]; exact h s
  let f (i : ℕ) (t : ℝ) := ∑ r : Fin i → Fin m with Surjective r, t^(∑ j, w (r j)) • T i (x ∘ r)
  let R (s : Finset (Fin m)) (t : ℝ) := (-1:ℝ)^sᶜ.card • P (v s t)
  have he t : (∑ s, R s t) = ∑ i∈Finset.range (k+1), f i t := by
    unfold R P Work.G05.blockTaylor; simp_rw [Finset.sum_apply, Finset.smul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [show _ = ∑ r : Fin i → Fin m with Surjective r, T i (u t ∘ r) from cross_effect (T i) (u t)]
    unfold f
    simp_rw [Function.comp_def,hu,(T i).map_smul_univ,Finset.prod_pow_eq_pow_sum]
  have hb (i) : iteratedDeriv l (f i) 0 = if i=m then
      (l.factorial : ℝ) • ∑ r : Fin m → Fin m with Surjective r,T m (x ∘ r) else 0 := by
    let W (r : Fin i → Fin m) := ∑ j, w (r j)
    have hd (r : Fin i → Fin m) : ContDiffAt ℝ l (fun t : ℝ => t^(W r) • T i (x ∘ r)) 0 := by fun_prop
    unfold f; rw [iteratedDeriv_fun_sum (fun i _ => hd i)]
    simp_rw [Degree.monojet]
    by_cases hx : i=m
    · subst i
      rw [if_pos rfl,Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => if_pos ?_
      exact (payments w (Finset.mem_filter.mp hj).2 hp).mpr rfl
    rw [if_neg hx]; exact Finset.sum_eq_zero (fun j hj => if_neg (by
      exact mt ((payments w (Finset.mem_filter.mp hj).2 hp).mp) (Ne.symm hx)))
  have hf i : ContDiff ℝ l (f i) := ContDiff.sum (fun j _ => (contDiff_id.pow _).smul contDiff_const)
  have hP s : ContDiffAt ℝ l (P ∘ v s) 0 :=
    ((Work.G05.blockTaylor_contDiff k F _).comp (hw s)).contDiffAt.of_le (Nat.cast_le.mpr hk)
  have hZ : iteratedDeriv l (fun t => ∑ s, R s t) 0 = 0 := by
    rw [iteratedDeriv_fun_sum (f:=R) (fun s _ => (hP s).const_smul _)]
    refine Finset.sum_eq_zero fun s _ => ?_
    change iteratedDeriv l (fun t => (-1:ℝ)^sᶜ.card • (P ∘ v s) t) 0 = 0; rw [iteratedDeriv_fun_const_smul (hP _), hQ,smul_zero]
  rw [funext he, iteratedDeriv_fun_sum (fun i _ => (hf i).contDiffAt)] at hZ
  have hz := coeff_symm (hF.of_le (Nat.cast_le.mpr hl))
  simp_rw [hb, perm_effect (T m) hz] at hZ
  rw [Finset.sum_eq_single m (fun i _ hi => if_neg hi) (fun h => False.elim (h (Finset.mem_range.mpr (by omega)))), if_pos rfl] at hZ
  have he : T m x = 0 := (smul_eq_zero.mp ((smul_eq_zero.mp hZ).resolve_left (by positivity))).resolve_left
    (by exact_mod_cast (perm_cost_pos m).ne')
  unfold T coeff at he; rw [smul_apply] at he; exact (smul_eq_zero.mp he).resolve_left (by positivity)

variable {G : Gauge} {n : Side} {k d : ℕ}

def whorl (v : Snap G d) (t : ℝ) := trunk d (scaleJet (expand d v) t)
@[simp] lemma whorl_at (i : Fin (d-1)) (v : Snap G d) (t : ℝ) : whorl v t i = (t^(i.val+2)) • v i := by
  simp [whorl,trunk,scaleJet,expand,i.isLt]
lemma whorl_single (v : Snap G d) (t : ℝ) (i : Fin (d-1)) :
    whorl (G:=G) (d:=d) (Pi.single i (v i)) t = (t^(i.val+2)) • Pi.single i (v i) := by
  funext j
  by_cases h : j=i
  · rw [h]; rw [whorl_at, Pi.smul_apply]
  simp [h]
lemma whorl_sum (s : Finset (Fin k)) (v : Fin k → Snap G d) (t : ℝ) :
    whorl (G:=G) (d:=d) (∑ i∈s, v i) t = ∑ i∈s,whorl (v i) t := by
  funext i
  simp only [whorl_at, Finset.sum_apply, Finset.smul_sum]

lemma snap_null {F : Snap G d → ℂ} (h : ContDiffAt ℝ d F 0)
    (hk : ∀ v : Snap G d, ∀ k ≤ d, iteratedDeriv k (F ∘ whorl v) 0=0)
    (u : Fin k → Snap G d) (j : Fin k → ℕ) (hJ : ∑ i, j i ≤ d) (he : ∀ i, Lower (j i) (u i)) :
    iteratedFDeriv ℝ k F 0 u = 0 := by
  let V := iteratedFDeriv ℝ k F 0
  let e (i : Fin k) (a : Fin (d-1)) : Snap G d := Pi.single a (u i a)
  have hx (i : Fin k) : u i = ∑ v : Fin (d-1),e i v := by
    funext m; rw [Finset.sum_apply, Finset.sum_eq_single m (fun j _ hj => Pi.single_eq_of_ne hj.symm _) (by simp)]; unfold e; rw [Pi.single_eq_same]
  change V u = _
  rw [funext hx,V.map_sum (α:=fun _ => Fin (d-1))]
  refine Finset.sum_eq_zero (fun r _ => ?_)
  by_cases hm : ∀ i, (r i).val+2 ≤ j i
  · let x i := e i (r i)
    have ht := polar_snap (fun i => (r i).val+2) (fun _ => by omega)
      x (fun t i => whorl (x i) t) (fun t i => whorl_single _ t _) h
      (le_trans (Finset.sum_le_sum fun i _ => hm i) hJ) (fun s => ?_)
    · exact ht
    let a := ∑ i,((r i).val+2)
    rw [show (fun t => F (∑ i∈s, whorl (x i) t)) = F ∘ (whorl (∑ i∈s, x i)) from funext fun t => by rw [comp_apply, whorl_sum]]
    exact hk _ _ ((Finset.sum_le_sum fun i _ => hm i).trans hJ)
  push Not at hm
  obtain ⟨i,hi⟩ := hm
  apply V.map_coord_zero i; dsimp only [e]; rw [he i _ hi, Pi.single_zero]

end YM.Planned.AtomRegular.Flat
