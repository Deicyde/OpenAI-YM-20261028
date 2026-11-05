import YM.Bid.Kitchen
import YM.Progress.DIRECTED_RECIPE.Shelves


/-!
# All raw addresses on the shelves

E, forced kernels and the pre-fusion soft atoms. This is not startup or
an expansion of the effective energy. It shows the fixed dictionary can be
used without anticipating the supports, with full price and incidence *at
those supports* and across the band where required. In particular this part
of baking does not require rerunning ancestry/scheduling once one knows the
right flags.  (see also 9710--25).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
namespace Rack
open Function Set RG Ovens Ovens.Pipes Wilson Lattice MeasureTheory RG.Shoot Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side} (X : Pipes G n)

def up : Ovens.Label ↪ Ovens.Label := Embedding.sumMap (upK X) (upS X)


lemma up_right (i : ℕ) : up X (.inr i) = .inr (upS X i) := rfl

lemma same_patch (l : Ovens.Label) : (drawer G n).patch (up X l) = X.patch l := by
  cases l with
  | inl j =>
    change ((drawer G n).kernel (upK X j)).support = _
    rw [hard_up]; rfl
  | inr j => exact soft_up ..

lemma same_atom (d : Tap G n) (l : Ovens.Label) (U : Config G n) :
    reach (widen X d) (up X l) U = reach d l U := by
  cases l with
  | inl i => exact congr_fun (stuffed _ d.forced i) _
  | inr i => simp only [up_right, reach, Sum.elim_inr, widen,stuffed]

lemma zero_atom (d : Tap G n) (l : Ovens.Label) (U : Config G n) (hl : l ∉ range (up X)) :
    reach (widen X d) l U = 0 := by
  cases l with
  | inl i =>
    simp only [reach, Sum.elim_inl, widen]; rw [blank _ _ ?_]; rfl
    rintro ⟨j,rfl⟩; exact hl ⟨.inl j, rfl⟩
  | inr i =>
    simp only [reach, Sum.elim_inr, widen]; rw [blank _ _ ?_]; simp
    rintro ⟨j,rfl⟩; exact hl ⟨.inr j,rfl⟩

lemma same_log (d : Tap G n) (U : Config G n) :
    (∑' j, (widen X d).logarithm j U) = ∑' j, d.logarithm j U :=
  transferred_sum (upS X) (fun i => congr_fun (stuffed _ d.logarithm i) _) (fun _ hj =>
    congr_fun (blank _ d.logarithm hj) _)

lemma hits (B : ℕ) (f : Label → ℝ) (a γ : ℝ) (h : Ac.Hit X.patch B f a γ) :
    Ac.Hit (drawer G n).patch B (stuff (up X) f) a γ := by
  intro x
  refine transfer_budget (up X) ?_ ?_ (h x)
  · simp [stuffed,same_patch]
  intro j hj; simp [blank _ _ hj]

variable {X}
lemma atoms_budget {f : Label → ℝ} {d : Tap G n} {κ : ℝ} (h : ∀ i U,
    |reach d i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*f i) (X : Pipes G n) :
    ∀ (i : Label) U, |reach (widen X d) i U| ≤
      i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*(stuff (up X) f i) := by
  intro i U
  by_cases hi : i ∈ range (up X)
  · obtain ⟨i,rfl⟩ := hi
    rw [same_atom,stuffed]
    cases i <;> exact h _ _
  simp [blank _ _ hi, zero_atom X d i _ hi]

lemma positive {ι κ : Type*} (p : ι ↪ κ) (f : ι → ℝ) (h : ∀ i, 0 ≤ f i) : ∀ i, 0 ≤ stuff p f i := by
  intro i
  by_cases hi : i ∈ range p
  · obtain ⟨i,rfl⟩ := hi
    rw [stuffed]; exact h i
  rw [blank _ _ hi]

lemma absorbs {d : Tap G n} {P : BudgetPoint} {δ b : ℝ} (hg : X.Digests d P δ b) :
    (drawer G n).Digests (widen X d) P δ b := by
  have hh := hg.stamp
  have ht := preserves X d P
  refine ⟨⟨ht.regular hh.regular, ?_, fun s t => let M := (hh.moves s t).some; ⟨on_shelves M⟩,
    ht.Ebound hh.boundE,ht.Kbound hh.boundK⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ht.forced_family hh.forced (fun _ _ _ => Iff.rfl) (fun _ => MeasurableSet.univ)
      (fun _ _ _ _ _ => rfl)
  · intro i x
    by_cases hi : i ∈ range (upS X)
    · obtain ⟨i,rfl⟩ := hi
      rw [soft_up]
      simp only [widen,stuffed]; exact hg.visits i x
    simp [widen,blank _ _ hi]
  · obtain ⟨c,hc,H⟩ := hg.pays
    refine ⟨stuff (upS X) c,(transferred_summable _ (fun i => stuffed (upS X) c i) (fun i hi => blank _ _ hi)).2 hc, ?_⟩
    intro i U
    by_cases hi : i ∈ range (upS X)
    · obtain ⟨i,rfl⟩ := hi
      simp only [widen,stuffed]; exact H i U
    simp [widen,blank _ _ hi]
  · intro i
    by_cases hi : i ∈ range (upS X)
    · obtain ⟨i,rfl⟩ := hi
      simp only [widen,stuffed]; exact hg.steady i
    simp only [widen, blank _ d.logarithm hi]
    exact fun _ _ => rfl
  · intro i
    by_cases hi : i ∈ range (upS X)
    · obtain ⟨i,rfl⟩ := hi
      simp only [widen,stuffed,soft_up]; exact hg.looks i
    dsimp only [widen]; rw [blank _ _ hi]
    exact fun _ _ _ _ => rfl
  · intro i
    by_cases hi : i ∈ range (upS X)
    · obtain ⟨i,rfl⟩ := hi
      simp only [widen,stuffed]; exact hg.reads i
    simp only [widen,blank _ _ hi]; exact measurable_const
  intro s t; obtain ⟨p,ha,hb⟩ := hg.carries s t
  exact ⟨_,carries_log s t p ha hb⟩

lemma sells {d : Tap G n} {P : BudgetPoint} {κ γ : ℝ} (hg : X.Buys d P κ γ) :
    (drawer G n).Buys (widen X d) P κ γ := by
  obtain ⟨f,hv,hw,hp⟩ := hg.certificate
  exact ⟨hg.margin,stuff (up X) f, positive _ _ hv, atoms_budget hw X,hits X _ _ _ _ hp⟩

lemma uniform_atoms {d : ℝ → Tap G n} {P : BudgetPoint} {T : Set ℝ} (X : Pipes G n) (H : invariantJet P d T) :
    invariantJet P (fun a => widen X (d a)) T := by
  intro a ha i ε he
  by_cases hi : i ∈ range (up X)
  · obtain ⟨i,rfl⟩ := hi
    filter_upwards [H a ha i ε he] with b hb U
    simp only [same_atom]; exact hb U
  filter_upwards with b U
  simp [he.le,zero_atom X (d b) i U hi, zero_atom X (d a) i U hi]

lemma common_hit {f : ℝ → Tap G n} {P : BudgetPoint} {T : Set ℝ} (hg : X.little P f T) :
    (drawer G n).little P (fun a => widen X (f a)) T := by
  obtain ⟨κ,γ,c,ht,hp,hk,hr,h,H⟩ := hg
  exact ⟨κ,γ,stuff (up X) c,ht,hp,hk,positive (up X) c hr,fun a ha => atoms_budget (h a ha) X,
    hits X _ _ _ _ H⟩

lemma raw_eval {f : ℝ → Tap G n} (X : Pipes G n) (R : PathData G) (A : Clip) (P : BudgetPoint) (b : ℝ) :
    (Bid.Cake (fun i => widen X (f i)) (drawer G n) R A P b).eval = (Bid.Cake f X R A P b).eval := by
  have ht := preserves X (f b) P
  funext U; simp only [Bid.Cake, Rep.eval, Rep.exponent, ht.same_gas, ht.same_sum]

lemma raw_curve {f : ℝ → Tap G n} (X : Pipes G n) (R : PathData G) (A : Clip) (P : BudgetPoint) (T : Set ℝ)
    (h : Curve P (Bid.Cake f X R A P) T) :
    Curve P (Bid.Cake (fun i => widen X (f i)) (drawer G n) R A P) T := by
  refine ⟨h.beta,h.v,fun _ _ _ _ => rfl,fun _ _ _ _ => rfl,?_⟩
  intro ε hε x hx
  filter_upwards [h.continuous ε hε x hx] with y hy
  exact (preserves X (f x) P).compares (preserves X (f y) P) hy
end Rack
end YM.Progress.DirectedRecipe
