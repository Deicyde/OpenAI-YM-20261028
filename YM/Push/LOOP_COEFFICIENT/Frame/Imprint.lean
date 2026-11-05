import YM.Push.LOOP_COEFFICIENT.Block.Optimize
import YM.Push.LOOP_COEFFICIENT.Resolution

/-!
# Jet-norm calculus with at most one rough input of known spatial majorant
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter
open scoped Topology ContDiff BigOperators
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {k n : ℕ}
structure Scope (E : Type) where
  regular : Set E
  irregular : Set E
variable {s : Scope E} {m m' : E → ℝ} {A B D : ℝ} {x : E}

def Marked (s : Scope E) (w : Fin k → E) (j : Fin k) := w j∈s.irregular ∧ ∀ i, i≠j → w i∈s.regular
structure Imprint (s : Scope E) (m : E → ℝ) (f : (Fin k → E) → F) (A : ℝ) : Prop where
  nonneg : 0≤A
  plain w : (∀ i,w i∈s.regular) → ‖f w‖≤A
  uneven w j : Marked s w j → ‖f w‖≤A * m (w j)

abbrev Engrave (s : Scope E) (m : E → ℝ) (f : E → F) (x : E) (k : ℕ) (A : ℝ) := Imprint s m (iteratedFDeriv ℝ k f x) A
structure Legacy (s : Scope E) (m : E → ℝ) (f : E → F) (x : E) (k : ℕ) (A : ℝ) : Prop where
  levels i : i≤k → Engrave s m f x i A

namespace Imprint
variable {f g : (Fin k → E) → F}
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] in
lemma top (h : Imprint s m f A) (hm : ∀ i,0≤m i) (hA : A≤B) : Imprint s m f B := ⟨h.nonneg.trans hA,fun w hw => (h.plain w hw).trans hA,fun w j hw => (h.uneven w j hw).trans (by gcongr; exact hm _)⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] in
lemma majorize (h : Imprint s m f A) (hm : ∀ i, m i≤m' i) : Imprint s m' f A := ⟨h.nonneg,h.plain,fun w j hw => (h.uneven w j hw).trans (mul_le_mul_of_nonneg_left (hm _) h.nonneg)⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] in
lemma zero (s : Scope E) (m : E → ℝ) (hm : ∀ x, 0≤m x) (hA : 0≤A) : Imprint s m (fun _ : Fin k → E => (0:F)) A := ⟨hA,fun _ _ => by simpa,fun w j _ => by rw [norm_zero]; exact mul_nonneg hA (hm _)⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] in
lemma add (h : Imprint s m f A) (h' : Imprint s m g B) : Imprint s m (fun w => f w + g w) (A+B) := ⟨add_nonneg h.nonneg h'.nonneg,fun w hw => (norm_add_le ..).trans (add_le_add (h.plain w hw) (h'.plain w hw)),fun w j hw => (norm_add_le ..).trans ((add_le_add (h.uneven w j hw) (h'.uneven w j hw)).trans_eq (add_mul ..).symm)⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] in
lemma sum {ι : Type} (u : Finset ι) (f : ι → (Fin k → E) → F) (A : ι → ℝ) (h : ∀ i ∈ u, Imprint s m (f i) (A i)) : Imprint s m (fun w => ∑ i∈u, f i w) (∑ i∈u,A i) := ⟨Finset.sum_nonneg (fun i hi => (h i hi).nonneg),fun w hw => (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi => (h i hi).plain w hw),fun w j hw => (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i hi => (h i hi).uneven w j hw)).trans_eq (Finset.sum_mul ..).symm)⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F] [NormedSpace ℝ H] in
lemma prod {g : (Fin k → E) → H} (h : Imprint s m f A) (h' : Imprint s m g A) : Imprint s m (fun w => (f w,g w)) A := ⟨h.nonneg,fun w hw => max_le (h.plain w hw) (h'.plain w hw),fun w j hw => max_le (h.uneven w j hw) (h'.uneven w j hw)⟩
end Imprint
lemma Engrave.prod {f : E → F} {g : E → H} (h : Engrave s m f x k A) (h' : Engrave s m g x k A) (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) : Engrave s m (fun y => (f y,g y)) x k A := by unfold Engrave; rw [iteratedFDeriv_prodMk hf hg le_top]; exact Imprint.prod h h'

abbrev Bundle (c : OrderedFinpartition k) (f : E → F) (x : E) (g : F → H) := (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c

def pages (c : OrderedFinpartition k) (g : F → H) (y : F) (A : ℝ) := ‖iteratedFDeriv ℝ c.length g y‖ * A^c.length

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma marked_part (c : OrderedFinpartition k) {w : Fin k → E} {j} (hj : Marked s w j) : Marked s (w ∘ c.emb (c.index j)) (c.invEmbedding j) := by
  constructor; · simpa using hj.1
  intro i hi; exact hj.2 _ (fun h => hi ((c.emb_strictMono _).injective (h.trans (c.emb_invEmbedding j).symm)))
lemma imprinted_composition (c : OrderedFinpartition k) (g : F → H) (_hm : ∀ x,0≤m x) (hA : 0≤A) {f : E → F} (h : ∀ i, Engrave s m f x (c.partSize i) A) : Imprint s m (Bundle c f x g) (pages c g (f x) A) := by
  let B := ‖iteratedFDeriv ℝ c.length g (f x)‖; let v w (i : Fin c.length) := iteratedFDeriv ℝ (c.partSize i) f x (w ∘ c.emb i)
  have he w : ‖Bundle c f x g w‖ ≤ B * ∏ i, ‖v w i‖ := (iteratedFDeriv ℝ c.length g (f x)).le_opNorm _
  refine ⟨mul_nonneg (norm_nonneg _) (by positivity),fun w hw => ?_,fun w j hj => ?_⟩
  · exact (he w).trans (mul_le_mul_of_nonneg_left ((Finset.prod_le_prod (g:=fun _ => A) (fun _ _ => norm_nonneg _) (fun i _ => (h i).plain _ (fun j => hw _))).trans_eq (by simp)) (norm_nonneg _))
  let u (i : Fin c.length) := if i=c.index j then m (w j) else 1
  have hw (i : Fin c.length) : ‖v w i‖ ≤ A*u i := by
    unfold u; split; next he => subst i; simpa [v] using (h _).uneven _ _ (marked_part c hj)
    next he => rw [mul_one]; exact (h i).plain _ (fun l => hj.2 _ ((c.emb_ne_emb_of_ne he (a:=l) (b:=c.invEmbedding j)).imp (fun h => h.trans (c.emb_invEmbedding j).symm)))
  rw [pages,mul_assoc]; exact (he w).trans (mul_le_mul_of_nonneg_left ((Finset.prod_le_prod (g:=fun i => A*u i) (fun _ _ => norm_nonneg _) (fun i _ => hw i)).trans_eq (by rw [Finset.prod_mul_distrib]; simp [u])) (norm_nonneg _))

lemma smaller_parts {k : ℕ} (c : OrderedFinpartition (k+1)) (i : Fin c.length) (h : c.length ≠ 1) : c.partSize i≤k := by
  contrapose! h
  have he := (c.partSize_le i).antisymm h; have hs := Function.Injective.surjective_of_finite (finCongr he) (c.emb_strictMono i).injective
  haveI hn : Subsingleton (Fin c.length) := ⟨fun j j' => by
    suffices ht : ∀ j,j=i by rw [ht j,ht j']
    intro j; by_contra hj; let q : Fin (c.partSize j) := ⟨0,c.partSize_pos j⟩; obtain ⟨v,hv⟩ := hs (c.emb j q); exact c.emb_ne_emb_of_ne hj hv.symm⟩
  haveI : Inhabited (Fin c.length) := ⟨i⟩; letI := Unique.mk' (Fin c.length); simpa only [Fintype.card_fin] using Fintype.card_unique (α:=Fin c.length)

def opus (g : F → H) (y : F) (k : ℕ) (A : ℝ) := ∑ c : OrderedFinpartition k, pages c g y A
lemma composition_fee (g : F → H) {f : E → F} (hg : ContDiffAt ℝ ω g (f x)) (hf : ContDiffAt ℝ ω f x) (hm : ∀ x,0≤m x) (hA : 0≤A) (h : ∀ c : OrderedFinpartition k, (∀ i,Engrave s m f x (c.partSize i) A) ∨ iteratedFDeriv ℝ c.length g (f x)=0) : Engrave s m (g ∘ f) x k (opus g (f x) k A) := by
  unfold Engrave opus; rw [iteratedFDeriv_comp hg hf le_top, FormalMultilinearSeries.taylorComp]
  convert Imprint.sum (s:=s) (m:=m) Finset.univ (fun c : OrderedFinpartition k => (Bundle c f x g : (Fin k→E) → H)) _ (fun c _ => ?_) using 2
  · apply _root_.sum_apply
  rcases h c with h|h
  · exact imprinted_composition c g hm hA h
  rw [show (Bundle c f x g : (Fin k → E) → H) = fun _ => 0 from funext (fun v => by change (iteratedFDeriv ℝ c.length g (f x)) _ = 0; rw [h]; rfl),pages,h,norm_zero,zero_mul]; exact Imprint.zero s m hm le_rfl

lemma Legacy.muted {f : E → F} (g : F → H) (hg : ContDiffAt ℝ ω g (f x)) (hf : ContDiffAt ℝ ω f x) (h0 : fderiv ℝ g (f x)=0) (hm : ∀ x,0≤m x) (h : Legacy s m f x k A) : Engrave s m (g ∘ f) x (k+1) (opus g (f x) (k+1) A) := by
  refine composition_fee g hg hf hm (h.levels _ le_rfl).nonneg fun c => ?_; by_cases hc : c.length=1; swap; exact Or.inl fun i => h.levels _ (smaller_parts c i hc)
  right; rw [hc]; ext1; rw [iteratedFDeriv_one_apply,h0]; rfl


end YM.Push.Loops.Frames
