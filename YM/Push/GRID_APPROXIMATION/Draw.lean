import YM.Push.GRID_APPROXIMATION.Telescope
import YM.Work.C27

/-!
# Planted arrays: literally translate the probes within the Wilson field.

Integrals here and for `spent` always on **C**. Supports localized to
finite native windows at those centers, shrinking physically. No mesh-limit
prescription for touching a seam or a diagonal is required. Provide spent
bound on all separated h-cell placements at each sufficiently late torus.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Function Filter Set Cells OS
open scoped Topology BigOperators

variable {G : Gauge} {ι : Type*} [Fintype ι] {C : Family G} {v : ι → C.book.Token} {h : ℕ}
variable (Z : ∀ i, Figures C (v i) h)

def placed (x : ι → Cover) (q N p) (U : Config G (C.side N p)) :=
    ∏ i, (Z i).plot q N p (translate (location C.S h N p (x i)) U)

def literal (h : ℕ) (v : ι → C.book.Token) (x : ι → Cover) (N p : ℕ) (U : Config G (C.side N p)) :=
    ∏ i, C.seen (v i) (location C.S h N p (x i)) U

def cloud (h N p : ℕ) (x : ι → Cover) (w : ι → ℕ) : Set (Site (C.side N p)) :=
    {y | ∃ i, y∈window (location C.S h N p (x i)) (w i)}

def limitPrice (q) := ∏ i, (Z i).cap q

lemma literal_env (x : ι → Cover) (v : ι → C.book.Token) (h N p : ℕ) : Envelope (literal h v x N p) :=
    Envelope.prodC _ _ fun i _ => Envelope.compactC (C.continuousO N p (v i).fst (v i).snd _)

lemma pictured {f : Extraction.Order} (hz : ∀ i, (Z i).Gives f) (q) :
    f.late fun N p => ∀ i, PictureAt C (v i) h N p ((Z i).plot q N p) ((Z i).cap q) ((Z i).err q) ((Z i).radius q) := by
  have he (i) := (hz i).late q
  unfold Extraction.Order.late at *
  filter_upwards [eventually_all.mpr he] with k hk using eventually_all.mpr hk

lemma translated_window {n : Side} {F : Config G n → ℂ} {o : Site n} {w : ℕ} (t : Site n) (he : Interior (window o w) F) :
    Interior (window (o+t) w) (fun U => F (translate t U)) := by
  have hv : MapsTo (affine (1:Signed) t) (window o w) (window (o+t) w) := by
    have hh := window_affine o t (1:Signed) (r:=w); simpa [affine] using hh
  have ht := he.unchanged 1 t hv
  simp only [comp_def,pull_one] at ht; exact ht

lemma planted_outputs {f : Extraction.Order} (hz : ∀ i, (Z i).Gives f) (q) :
    f.late fun N p => ∃ w : ι → ℕ, (∀ i, C.S.a N * w i ≤ (Z i).radius q) ∧
      ∀ x, Interior (cloud (C:=C) h N p x w) (placed Z x q N p) ∧
      ∀ U, star (placed Z x q N p U) = placed Z x q N p U ∧ ‖placed Z x q N p U‖ ≤ limitPrice Z q := by
  have he := pictured Z hz q
  unfold Extraction.Order.late at *
  filter_upwards [he] with k hk
  filter_upwards [hk] with j hj
  let N := f.mesh j; let p := f.per k
  choose w hw hm using fun i : ι => (hj i).short
  refine ⟨w,hw,fun x => ?_⟩
  let t := fun i : ι => location C.S h N p (x i)
  let A (i : ι) (U : Config G (C.side N p)) := (Z i).plot q N p (translate (t i) U)
  have ha (i) : Interior (cloud (C:=C) h N p x w) (A i) := by
    have hh := translated_window (t i) (hm i)
    rw [zero_add] at hh
    exact hh.enlarges fun u hu => ⟨i,hu⟩
  refine ⟨Interior.combines A _ (fun i _ => ha i),fun U => ?_⟩
  unfold placed
  simp only [star_prod,norm_prod]
  exact ⟨Finset.prod_congr rfl fun i _ => (hj i).real _, Finset.prod_le_prod
    (fun i _ => norm_nonneg _) (fun i _ => (hj i).bound _)⟩

lemma placed_free {f : Extraction.Order} (hz : ∀ i, (Z i).Gives f) (q) :
    f.late fun N p => ∀ x, Envelope (placed Z x q N p) ∧
      ∀ U, star (placed Z x q N p U) = placed Z x q N p U ∧ ‖placed Z x q N p U‖ ≤ limitPrice Z q := by
  have he := planted_outputs Z hz q
  unfold Extraction.Order.late at *
  exact he.mono fun i hi => hi.mono fun j hj x => ⟨cylinder_env (hj.choose_spec.2 x).1,(hj.choose_spec.2 x).2⟩

/-- Price covers **all** translations x on that grid when they occupy
distinct cells on the torus; torus wrapping is the only distinctness test
needed for this comparison. -/
lemma spent {f : Extraction.Order} (H : C.Makes) (hz : ∀ i, (Z i).Gives f) (q) :
    f.late fun N p => ∀ x : ι → Cover, Injective (wrap (C.side h p) ∘ x) →
      ‖moment (C.beta N p) (placed Z x q N p)-moment (C.beta N p) (literal h v x N p)‖ ≤ expense Z q := by
  have he := pictured Z hz q
  have hm := pictured Z hz 0
  unfold Extraction.Order.late at *
  filter_upwards [he,hm] with k hk hh
  filter_upwards [hk,hh,f.mesh.cofinal.eventually_ge_atTop h] with j hj hl hp x hx
  let N := f.mesh j; let p := f.per k
  have ht := paid_at Z H q N p hp (by
    intro i a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with h|h <;> subst a; exacts [hj i,hl i])
      (fun i => ((hz i).cap_pos _).le) _ hx
  unfold literal placed location; simp only [dif_pos hp]; exact ht

section pair
variable {κ : Type*} [Fintype κ] {u : κ → C.book.Token}

def combined (D : ∀ i, Figures C (u i) h) : ∀ i : ι ⊕ κ, Figures C (Sum.elim v u i) h
  | Sum.inl i => Z i
  | Sum.inr i => D i

omit [Fintype ι] [Fintype κ] in
lemma combined_gives {f : Extraction.Order} (D : ∀ i, Figures C (u i) h)
    (hz : ∀ i, (Z i).Gives f) (hd : ∀ i, (D i).Gives f) : ∀ i, (combined Z D i).Gives f := by
  rintro (i|i); exacts [hz i,hd i]

lemma spent_pair {f : Extraction.Order} (H : C.Makes) (D : ∀ i, Figures C (u i) h)
    (hz : ∀ i, (Z i).Gives f) (hd : ∀ i, (D i).Gives f) (q) :
    f.late fun N p => ∀ (x : ι → Cover) (y : κ → Cover), Injective (wrap (C.side h p) ∘ (Sum.elim x y)) →
      ‖moment (C.beta N p) (placed Z x q N p * placed D y q N p)-
        moment (C.beta N p) (literal h v x N p * literal h u y N p)‖ ≤ expense (combined Z D) q := by
  have he := spent (combined Z D) H (combined_gives Z D hz hd) q
  have hp (N p : ℕ) (x : ι → Cover) (y : κ → Cover) :
      placed (combined Z D) (Sum.elim x y) q N p = placed Z x q N p * placed D y q N p := by
    funext U; unfold placed; rw [Fintype.prod_sum_type]; rfl
  have hx (N p : ℕ) (x : ι → Cover) (y : κ → Cover) :
      literal h (Sum.elim v u) (Sum.elim x y) N p = literal h v x N p * literal h u y N p := by
    funext U; unfold literal; rw [Fintype.prod_sum_type]; rfl
  unfold Extraction.Order.late at *
  refine he.mono fun k hk => hk.mono fun i hi x y hu => ?_
  rw [← hp,← hx]; exact hi _ hu
end pair
end YM.Push.GridApprox
