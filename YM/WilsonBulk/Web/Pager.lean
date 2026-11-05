import YM.WilsonBulk.Web.Patterns

/-!
# Periodization at fixed valence on connected sheets

This is NOT the finite-volume conditional Taylor recursion -- e.g. loops can
wind. We identify seam/pluck and pointwise multiply against an ALREADY
periodized factor; later use to recover Ward on the cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Equiv Lattice Bloch Pert.Bulk Filter

variable {X Y α β : Type} {c d : Side} {n m k : ℕ} {σ θ p q : ℝ} {D : Rule X}

-- for arbitrary projection on a representative space
abbrev Thesis (Λ : X→ Y) (i : Fin n) (x : X) (v : Legs Y n) :=
  {u : Legs X n // u i=x ∧ Λ ∘ u = v}
def page (Λ : X→ Y) (i : Fin n) (x : X) (u : Page X n) (v : Legs Y n) : ℝ :=
  ∑' a : Thesis Λ i x v,u a.val
lemma page_tsum (Λ : X→ Y) (i : Fin n) (x : X) (u : Page X n) (v : Legs Y n) : page Λ i x u v =
    ∑' a, (if a i=x ∧ Λ ∘ a=v then u a else 0) := by
  unfold page; erw [_root_.tsum_subtype {a|a i=x∧ Λ∘a=v} u]; apply tsum_congr; intro a
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
lemma page_money (Λ : X→ Y) (u : Page X n) (h : Within D σ p u) (hσ : 0≤σ) (i x v) :
    Summable fun a : Thesis Λ i x v=> u a.val := by
  refine ((within_total h hσ i x).subtype {a | a i=x ∧ Λ ∘ a=v}).congr ?_
  rintro ⟨a,ha⟩; simp [show a i=x from ha.1]

def Orates (Λ : X→ Y) (u : Page X n) (v : Page Y n) := ∀ i x w, w i=Λ x → v w= page Λ i x u w
namespace Orates
variable {Λ : X→ Y} {u u' : Page X n} {v v' : Page Y n}
lemma zero : Orates Λ (0:Page X n) 0 := by intro i x w _; simp [page]
lemma plus (he : Orates Λ u v) (hh : Orates Λ u' v') (hu : Within D σ p u) (hu' : Within D θ q u')
    (hp : 0 ≤ σ) (hq : 0≤θ) : Orates Λ (u+u') (v+v') := fun i x w h=> by
  rw [Pi.add_apply,he i x w h, hh i x w h]; exact ((page_money Λ u hu hp i x w).tsum_add (page_money Λ u' hu' hq i x w)).symm
lemma scale (he : Orates Λ u v) (r : ℝ) : Orates Λ (r • u) (r • v) := fun i x w h=> by
  rw [Pi.smul_apply,he i x w h]; simp [page,tsum_mul_left]
lemma minus (he : Orates Λ u v) (hh : Orates Λ u' v') (hu : Within D σ p u) (hu' : Within D θ q u')
    (hp : 0 ≤ σ) (hq : 0≤θ) : Orates Λ (u-u') (v-v') := fun i x w h=> by
  rw [Pi.sub_apply,he i x w h, hh i x w h]; exact ((page_money Λ u hu hp i x w).tsum_sub (page_money Λ u' hu' hq i x w)).symm
lemma gather {ι : Type} (s : Finset ι) (u : ι → Page X n) (v : ι → Page Y n) {p : ι→ℝ}
    (h : ∀ i∈s, Orates Λ (u i) (v i)) (hh : ∀ i∈s, Within D σ (p i) (u i)) (hp : 0≤σ) : Orates Λ (∑ i∈s,u i) (∑ i∈s,v i) := by
  intro i x w hx; rw [Finset.sum_apply]; unfold page; simp_rw [Finset.sum_apply]
  rw [Summable.tsum_finsetSum (by intro b hb; exact page_money Λ (u b) (hh b hb) hp i x w)]; exact Finset.sum_congr rfl fun a ha=>h a ha i x w hx
lemma reindex (h : Orates Λ u v) (e : Fin n ≃ Fin m) : Orates Λ (escort e u) (escort e v) := by
  intro i x w hx
  calc
    escort e v w = page Λ (e.symm i) x u (w ∘ e) := h _ x _ (by simp [hx])
    _ = _ := by
        rw [page_tsum,page_tsum,← (casesEquiv e (.refl _)).tsum_eq _]
        apply tsum_congr ; intro a
        have h₀ : casesEquiv e (.refl X) a=a ∘ e.symm := rfl
        rw [h₀]; simp only [comp_apply]
        have he : Λ ∘ (a ∘ e.symm) = w ↔ Λ ∘ a=w ∘ e := ⟨fun h=> by simpa [comp_assoc] using congr_arg (fun f=> f ∘ e) h,fun h=> by simpa [comp_assoc] using congr_arg (fun f=> f ∘ e.symm) h⟩
        simp [he,escort,comp_assoc]
lemma polished (h : Orates Λ u v) (he : Within D σ p u) (hh : 0≤σ) : Orates Λ (polish u) (polish v) :=
  (gather Finset.univ _ _ (fun e _=> h.reindex e) (fun e _=>he.reindex e) hh).scale _
-- tensor fiber against pulled-back *periodic* factor (e.g. loop line Γ)
lemma overlay (h : Orates Λ u v) {s : Legs X n → ℝ} {t : Legs Y n → ℝ}
    (hs : ∀ a,s a=t (Λ ∘ a)) : Orates Λ (u*s) (v*t) := by
  intro i x w hx; rw [Pi.mul_apply,h i x w hx]; simp only [page,Pi.mul_apply]; rw [← tsum_mul_right]
  exact tsum_congr fun a=> by rw [hs,a.property.2]
lemma uniq (h : Orates Λ u v) (he : Orates Λ u v') (hΛ : Surjective Λ) (hn : n ≠ 0) : v=v' := by
  ext1 x; let i : Fin n:=⟨0,by omega⟩; obtain ⟨a,ha⟩:= hΛ (x i); exact (h i a x ha.symm).trans (he i a x ha.symm).symm
lemma regular (h : Orates Λ u v) (hs : Regular u) (hΛ : Surjective Λ) (hn : n≠0) : Regular v := fun e=> (hs e ▸ (h.reindex e) : Orates Λ u (escort e v)).uniq h hΛ hn
end Orates

def small (c : Side) (α : Type) : Market α→Co c α := fun x=> (wrap c x.1,x.2)
def print (c : Side) (u : Text α (n+1)) : Page (Co c α) (n+1) := fun w=>
  page (small c α) 0 (lift (w 0).1,(w 0).2) u w
lemma small_onto (c : Side) (α : Type) : Surjective (small c α) := fun ⟨v,t⟩ => ⟨(lift v,t),by simp [small]⟩
lemma small_roll (c : Side) (α : Type) (b : Cover) (v : Market α) : small c α (roll b α v)=rolls (wrap c b) α (small c α v) := by simp [roll_apply,rolls_apply,small]

section reroot
-- one true translation orbit, can hold any representative of any slot
variable {x y : Market α} {i j : Fin n} {v : Legs (Co c α) n} {u : Text α n}

def relocate (a : Legs (Market α) n) (x : Market α) (j : Fin n) : Legs (Market α) n := roll (x.1-(a j).1) α ∘ a
lemma relocate_at (x : Market α) (a : Legs (Market α) n) (j : Fin n) :
    relocate a x j j=(x.1,(a j).2) := by simp only [relocate,comp_apply,roll_apply]; congr 1; abel
lemma thesis_move (h : v j=small c α y) (a : Thesis (small c α) i x v) :
    relocate a.val y j j=y ∧ small c α ∘ relocate a.val y j=v := by
  have he : small c α (a.val j)=small c α y := (congr_fun a.property.2 j).trans h
  have hk : wrap c (a.val j).1 = wrap c y.1 := congr_arg Prod.fst he
  refine ⟨by rw [relocate_at]; exact Prod.ext rfl (show (a.val j).2 = y.2 from (have e := congr_arg Prod.snd he; e)),?_⟩
  refine Eq.trans ?_ a.property.2; ext1 t; simp only [relocate, comp_apply, roll_apply, small]; rw [map_add,map_sub,hk,sub_self,add_zero]
def rotor (h : v i=small c α x) (he : v j=small c α y) : Thesis (small c α) i x v ≃ Thesis (small c α) j y v where
  toFun a := ⟨relocate a.val y j, thesis_move he a⟩
  invFun a := ⟨relocate a.val x i, thesis_move h a⟩
  left_inv a := by
    apply Subtype.ext; ext1 t; simp only [relocate,comp_apply,roll_apply]; rw [a.property.1]; refine Prod.ext ?_ rfl; dsimp only; abel
  right_inv a := by
    apply Subtype.ext; ext1 t; simp only [relocate,comp_apply,roll_apply]; rw [a.property.1]; refine Prod.ext ?_ rfl; dsimp only; abel
lemma page_move (hU : Pervasive u) (h : v i=small c α x) (he : v j=small c α y) : page (small c α) i x u v = page (small c α) j y u v := by
  unfold page
  rw [← (rotor h he).tsum_eq _]; exact tsum_congr fun b=> (hU (y.1-(b.val j).1) b.val).symm
lemma Orates.one {w : Page (Co c α) n} (hU : Pervasive u) (j : Fin n)
    (h : ∀ v : Legs (Co c α) n, ∃ x,v j=small c α x ∧ w v=page (small c α) j x u v) : Orates (small c α) u w := by
  intro i x v hx; obtain ⟨y,H,H'⟩:= h v; exact H'.trans (page_move hU H hx)
lemma reads {u : Text α (n+1)} (h : Pervasive u) : Orates (small c α) u (print c u) :=
  Orates.one h 0 (fun v=> ⟨(lift (v 0).1,(v 0).2), Prod.ext (by simp [small]) rfl,rfl⟩)
end reroot
end YM.WilsonBulk.Sheet
