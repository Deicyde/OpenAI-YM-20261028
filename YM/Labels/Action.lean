import YM.Labels.Polynomial

/-! Tensor action and real form on unrenormalized labels. -/

set_option autoImplicit false
noncomputable section
namespace YM.Labels
open Function Set
open scoped BigOperators Topology

variable {G : Gauge}

/-- Linear change of jet variables within each degree. -/
def changed (e : (i : ℕ) → Module.End ℝ (Taylor G i)) : Pol G →ₐ[ℂ] Pol G :=
  MvPolynomial.aeval fun i : Key G => ∑ j,
    MvPolynomial.C (σ := Key G) (coord_lift i (e i.1 ((axes G i.1) j))) *
      MvPolynomial.X ⟨i.1, j⟩
where coord_lift (i : Key G) (x : Taylor G i.1) : ℂ := (((axes G i.1).repr x) i.2 : ℝ)

def changedJet (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (A : Jet G) : Jet G :=
  fun i => e i (A i)

theorem read_changed (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (A : Jet G) :
    (read A).comp (changed e) = read (changedJet e A) := by
  ext i
  simp only [AlgHom.comp_apply, changed, read, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  rcases i with ⟨j,i⟩
  have hx : (axes G j).repr (e j (A j)) i = ∑ l : Fin (dim G j),
      ((axes G j).repr (e j (axes G j l)) i * (axes G j).repr (A j) l) := by
    conv_lhs => rw [← (axes G j).sum_repr (A j)]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _; exact mul_comm _ _
  simp only [changedJet, coord, changed.coord_lift, hx, Complex.ofReal_sum,
    Complex.ofReal_mul]

theorem eval_changed (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (A : Jet G) (p : Pol G) :
    read A (changed e p) = read (changedJet e A) p := DFunLike.congr_fun (read_changed e A) p

theorem pure_moved {M : Type*} [AddCommMonoid M] (d : ℕ → M)
    (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (b : Key G →₀ ℕ) (c : ℂ) :
    let w : Key G → M := fun i => d i.1
    MvPolynomial.IsWeightedHomogeneous w (changed e (MvPolynomial.monomial b c)) (Finsupp.weight w b) := by
  classical
  intro w
  have H (i : Key G) : MvPolynomial.IsWeightedHomogeneous w (changed e (MvPolynomial.X i)) (w i) := by
    rw [changed,MvPolynomial.aeval_X]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j _
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    exact MvPolynomial.isWeightedHomogeneous_X ℂ w ⟨i.1,j⟩
  simp only [MvPolynomial.monomial_eq, map_mul, changed, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [Finsupp.weight_apply]
  unfold Finsupp.prod Finsupp.sum
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  rw [map_prod]
  simp_rw [map_pow]
  exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun i _ ↦ (H i).pow (b i)

theorem moved_limit {d : ℕ} {p : Pol G} (h : p ∈ limited G d)
    (e : (i : ℕ) → Module.End ℝ (Taylor G i)) : changed e p ∈ limited G d := by
  rw [limited, MvPolynomial.restrictSupport_eq_span] at h
  refine Submodule.span_induction (p := fun p _ ↦ changed e p ∈ limited G d) ?_ ?_ ?_ ?_ h
  · rintro f ⟨x,hx,rfl⟩
    rw [limited, MvPolynomial.mem_restrictSupport_iff]
    intro b hb
    have he := pure_moved (fun n => n+2) e x 1 (MvPolynomial.mem_support_iff.mp hb)
    change height b = height x at he
    change height b ≤ d
    rw [he]; exact hx
  · rw [map_zero]; exact (limited G d).zero_mem
  · intro a b _ _ ha hb
    rw [map_add]; exact (limited G d).add_mem ha hb
  intro c a _ ha
  rw [map_smul]; exact (limited G d).smul_mem c ha

/-- Coordinate transforms: simultaneous with `Ortho.move`, hence
acting on labels by composition with the inverse on connections. -/
def rotated (s : Ortho) : Pol G →ₐ[ℂ] Pol G := changed fun _ => Taylor.turn s⁻¹

theorem rotation_law (s t : Ortho) (p : Pol G) : rotated (s*t) p = rotated s (rotated t p) := by
  apply eval_ext
  intro A
  rw [rotated, eval_changed, rotated, eval_changed, rotated, eval_changed]
  apply congr_arg (fun Z => read Z p)
  funext i
  simp only [changedJet, mul_inv_rev, Taylor.turn_mul]

def tensor {d : ℕ} (s : Ortho) : Label G d →ₗ[ℂ] Label G d where
  toFun p := ⟨rotated s p.val, moved_limit p.property.1 _, by
    intro A u
    rw [rotated, eval_changed, eval_changed]
    exact (show changedJet _ (colored u A) = colored u (changedJet (fun i => Taylor.turn (j := i) s⁻¹) A) from
      funext fun i => (Taylor.turn_paint ..).symm) ▸ p.property.2 _ u ⟩
  map_add' p q := Subtype.ext ((rotated s).map_add p.val q.val)
  map_smul' c p := Subtype.ext (map_smul (rotated s) c p.val)

@[simp] theorem tensor_mul {d : ℕ} (s t : Ortho) (v : Label G d) :
    tensor (s*t) v = tensor s (tensor t v) := Subtype.ext (rotation_law s t v.val)

@[simp] theorem tensor_one {d : ℕ} (v : Label G d) : tensor 1 v = v := by
  apply Subtype.ext
  change rotated 1 v.val = _
  apply eval_ext
  intro A
  rw [rotated, eval_changed]
  rw [inv_one, show changedJet (fun _ => Taylor.turn 1) A = A from funext fun i => Taylor.oneTurn _]

/-- Ordinary conjugation, before reflection. -/
def conjPol (p : Pol G) := MvPolynomial.map (starRingEnd _) p

theorem conj_value (p : Pol G) (A : Jet G) : read A (conjPol p) = star (read A p) := by
  unfold conjPol
  induction p using MvPolynomial.induction_on with
  | C a => simp [read]
  | add p q hp hq => simp only [map_add, hp,hq, star_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, hp, map_mul]
    simp [read, coord]

lemma conj_mem {d : ℕ} (v : Label G d) : conjPol v.val ∈ localFields G d := by
  constructor
  · change conjPol _ ∈ limited G d
    apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
    intro b hb
    have h : b ∈ v.val.support := MvPolynomial.support_map_subset (starRingEnd ℂ) v.val hb
    exact ((MvPolynomial.mem_restrictSupport_iff ℂ).mp (show v.val ∈ limited G d from v.property.1)) h
  intro A u; rw [conj_value, conj_value, v.property.2 A u]

def realBar {d : ℕ} : Label G d →ₛₗ[starRingEnd ℂ] Label G d where
  toFun v := ⟨conjPol v.val, conj_mem v⟩
  map_add' p q := Subtype.ext (map_add (MvPolynomial.map (starRingEnd ℂ)) p.val q.val)
  map_smul' c p := by
    apply Subtype.ext
    apply eval_ext
    intro A
    change read A (conjPol (c • p.val)) = read A (star c • conjPol p.val)
    rw [conj_value,map_smul,map_smul, conj_value]
    simp

@[simp] theorem twice {d : ℕ} (v : Label G d) : realBar (realBar v) = v := by
  apply Subtype.ext
  change conjPol (conjPol v.val) = _
  apply eval_ext; intro A; rw [conj_value, conj_value, star_star]

@[simp] theorem real_turn {d : ℕ} (s : Ortho) (v : Label G d) :
    realBar (tensor s v) = tensor s (realBar v) := by
  apply Subtype.ext; apply eval_ext; intro A
  change read A (conjPol (rotated s v.val)) = read A (rotated s (conjPol v.val))
  rw [rotated, conj_value, eval_changed, eval_changed, conj_value]
end YM.Labels
