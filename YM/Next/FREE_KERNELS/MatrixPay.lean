import YM.Next.FREE_KERNELS.Masks

/-!
# Entry costs (fixed matrix types)

Absolute cube bounds. Fiber residue or alias size still varying? Put the
chosen residue or alias into the index over which the bounds are uniform, NOT
into the matrix type here. In particular the `times` product theorem spends
dimension constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {ι κ α β γ : Type*}

lemma staple [Fintype κ] (P : κ → ℝ → ℝ → Prop)
    (h : ∀ i, ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ P i σ C)
    (m : ∀ i σ C η A, P i σ C → η ≤ σ → 0<η → C ≤ A → P i η A) :
    ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ i, P i σ C := by
  classical
  have he (s : Finset κ) : ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ i∈s, P i σ C := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,1,one_pos,one_pos,by simp⟩
    | insert b s _ ih =>
      obtain ⟨σ,C,hσ,hC,hb⟩ := h b
      obtain ⟨η,A,hη,hA,hx⟩ := ih
      have hp := lt_min hσ hη
      refine ⟨min σ η,max C A,hp,lt_max_of_lt_left hC,fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact m _ _ _ _ _ hb (min_le_left ..) hp (le_max_left ..)
      exact m _ _ _ _ _ (hx i hi) (min_le_right ..) hp (le_max_right ..)
  obtain ⟨σ,C,hσ,hC,he⟩ := he Finset.univ
  exact ⟨σ,C,hσ,hC,fun i => he i (Finset.mem_univ _)⟩

/-- Matrix with every displacement still *unscaled* native; entries on
radial-frequency cubes. -/
structure Pay (w : ι → ℝ) (f : ι → Momentum → Matrix α β ℂ) : Prop where
  site i : 0 ≤ w i
  tap a b : Moderate w fun i p => f i p a b

namespace Pay
variable {w u : ι → ℝ} {f g : ι → Momentum → Matrix α β ℂ}
lemma reindex (hf : Pay w f) (π : κ → ι) : Pay (fun i => w (π i)) fun i => f (π i) :=
  ⟨fun i => hf.site (π i), fun a b => (hf.tap a b).index π⟩
lemma raise (h : Pay w f) (he : w ≤ u) : Pay u f :=
  ⟨fun i => (h.site i).trans (he i), fun a b => (h.tap a b).raise_price he⟩
lemma add (h : Pay w f) (h' : Pay w g) : Pay w fun i p => f i p + g i p :=
  ⟨h.site,fun a b => (h.tap a b).add (h'.tap a b)⟩
lemma sub (h : Pay w f) (h' : Pay w g) : Pay w fun i p => f i p - g i p :=
  ⟨h.site,fun a b => (h.tap a b).sub (h'.tap a b)⟩

lemma transpose (h : Pay w f) : Pay w fun i p => (f i p).transpose := ⟨h.site,fun a b => h.tap b a⟩
lemma reverse (h : Pay w f) : Pay w fun i p => f i (-p) := ⟨h.site,fun a b => (h.tap a b).reverse⟩
lemma scale {c : ι → Momentum → ℂ} (h : Pay w f) (hc : Moderate u c) : Pay (fun i => u i*w i) fun i p => c i p • f i p :=
  ⟨fun i => mul_nonneg (hc.nonneg i) (h.site i),fun a b => hc.mul (h.tap a b)⟩
lemma times [Fintype β] {g : ι → Momentum → Matrix β γ ℂ} (hf : Pay w f) (hg : Pay u g) :
    Pay (fun i => w i*u i) fun i p => f i p * g i p := by
  have he (i : ι) : 0 ≤ w i*u i := mul_nonneg (hf.site i) (hg.site i)
  exact ⟨he,fun a b => Moderate.sum Finset.univ _ he fun i _ => (hf.tap a i).mul (hg.tap i b)⟩
lemma on_alias (hf : Pay w f) (L : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) :
    Pay w fun i p => f i (aliasAt p (l i)) := ⟨hf.site,fun a b => (hf.tap a b).on_alias L ho l⟩
lemma const (f : Matrix α β ℂ) : Pay (fun _ : ι => 1) fun _ _ => f := ⟨fun _ => zero_le_one, fun a b => Moderate.const (f a b)⟩
lemma diag [DecidableEq α] (c : ι → Momentum → α → ℂ) (hc : ∀ a, Moderate w fun i p => c i p a) (h : ∀ i, 0≤w i) :
    Pay w fun i p => Matrix.diagonal (c i p) := by
  refine ⟨h,fun a b => ?_⟩; by_cases he : a=b
  · subst b; simpa only [Matrix.diagonal_apply_eq] using hc a
  simpa only [Matrix.diagonal_apply_ne _ he] using Moderate.zero h
lemma pockets {f : ι → Momentum → α → ℂ} {s : Finset α} (h : ∀ a ∈ s, Moderate w fun i p => f i p a) :
    Moderate (fun i => w i ^ s.card) fun i p => ∏ a∈s, f i p a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.card_empty,pow_zero,Finset.prod_empty] using Moderate.const (ι:=ι) 1
  | insert a s ha ih =>
    have he := (h a (Finset.mem_insert_self ..)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.card_insert_of_notMem ha,pow_succ',Finset.prod_insert ha] using he
lemma expose_mask {t : ι → Momentum → Axis → ℂ} (r : ℕ) (h : ∀ a, Moderate w fun i p => t i p a) :
    Pay (fun i => (w i)^r) fun i p => mask r (t i p) := by
  have hh := (h 0).nonneg
  apply diag; swap; exact fun i => pow_nonneg (hh i) _
  intro a
  unfold inventory
  simpa only [a.property] using pockets (s:=a.val) (fun k _ => h k)
lemma expose_wedge {t : ι → Momentum → Axis → ℂ} (r : ℕ) (h : ∀ a, Moderate w fun i p => t i p a) :
    Pay w fun i p => wedge r (t i p) := by
  have hh := (h 0).nonneg
  refine ⟨hh,fun a b => ?_⟩
  simp only [wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Moderate.sum _ _ hh; intro j _; simpa only [mul_one] using (h j).mul (Moderate.const _)

lemma stapleMat [Fintype α] [Fintype β] (h : Pay w f) : Moderate (fun x : ι×α×β => w x.1) fun x p => f x.1 p x.2.1 x.2.2 := by
  apply Exists.elim (staple (κ:=α×β) (fun x η A => ∀ i, SafeCube η (A*w i) (fun p => f i p x.1 x.2))
    (fun x => h.tap x.1 x.2) (fun x _ _ _ _ h' he hp hb i => (h' i).mono he (mul_le_mul_of_nonneg_right hb (h.site i))))
  rintro η ⟨A,hp,hA,h⟩; exact ⟨η,A,hp,hA,fun i => h i.2 i.1⟩

end Pay

def record (f : Momentum → Matrix α β ℂ) : Row α β := fun a b => tape (fun p => f p a b)

variable {w : ι → ℝ} {f : ι → Momentum → Matrix α β ℂ}

lemma matrix_cover [Fintype α] [Fintype β] (h : Pay w f) {η : ℝ} (hp : 0 < η)
    (hh : ∀ i (p : Momentum), p∈realCube η → ∀ x, p+reciprocal x ∈ realCube η → f i (p+reciprocal x)=f i p) :
    ∃ σ C : ℝ, 0 < σ ∧ 0 < C ∧ ∀ i, (record (f i)).strip σ (C*w i) := by
  obtain ⟨σ,C,he,hc,h⟩ := tapes_sound h.stapleMat hp (fun i p hg x hx => by
    exact congr_fun (congr_fun (hh _ p hg x hx) _) _)
  exact ⟨σ,C,he,hc,fun i a b => h (i,a,b)⟩
lemma record_eq (h : Pay w f) {η : ℝ} (hp : 0 < η) (i : ι)
    (hh : ∀ i (p : Momentum), p∈realCube η → ∀ x, p+reciprocal x ∈ realCube η → f i (p+reciprocal x)=f i p)
    (hj : ∀ i (p : Momentum), p∈realCube η → (f i (-p)).map star=f i p) {p : Momentum} (he : p∈baseCube) :
    (record (f i)).read p=f i p := by
  ext a b
  obtain ⟨θ,hc,h⟩ := tapes_read (h.tap a b) hp (fun i p hg x hx => by
    exact congr_fun (congr_fun (hh _ p hg x hx) _) _) (fun i p hh => congr_fun (congr_fun (hj i p hh) _) _)
  exact h i p (base_subset_realCube hc he)
end YM.Next.Free
