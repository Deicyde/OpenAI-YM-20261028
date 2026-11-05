import YM.RG08.Packets.Norm

/-!
# Rooted coefficient tensor norms for connected Fk graph operations

diameter weights (comparable with an all-stubs sum at any fixed arity) are particularly useful
for allocating across PDE trace and join with NO width loss.
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false

variable {I M : Type} {n k : ℕ}

abbrev Tape (n : ℕ) (I : Type) := Fin n → I
abbrev Flake (n : ℕ) (I : Type) := Tape n I → ℝ

structure Ground (I : Type) where
  span : I→I→ℝ
  stay : ∀ i, span i i=0
  left : ∀ i j, span i j = span j i
  slope : ∀ i j k, span i k ≤ span i j+span j k

namespace Ground

variable (d : Ground I)
theorem nn (i j) : 0 ≤ d.span i j := by
 have h:=d.slope i j i
 rw [d.stay,d.left j i] at h; linarith

def paper (x : Tape n I) := insert 0 ((univ ×ˢ univ : Finset (Fin n × Fin n)).image (fun ij=> d.span (x ij.1) (x ij.2)))

def radius (x : Tape n I) := (paper d x).max' (insert_nonempty ..)

theorem radius_nn (x : Tape n I) : 0 ≤ d.radius x := le_max' _ _ (mem_insert_self ..)
 theorem le_radius (x : Tape n I) (i j : Fin n) : d.span (x i) (x j) ≤ d.radius x := le_max' (paper d x) _ (mem_insert_of_mem (mem_image.mpr ⟨(i,j),by simp,rfl⟩))
theorem radius_le (x : Tape n I) {a} (ha : 0 ≤ a) (h : ∀ i j, d.span (x i) (x j) ≤ a) : d.radius x ≤ a := by
 apply max'_le; intro i hi
 obtain he|he:=mem_insert.mp hi
 · exact he ▸ ha
 obtain ⟨⟨j,k⟩,_,rfl⟩:=mem_image.mp he;exact h j k

theorem radius_comp (x : Tape n I) (f : Fin k→Fin n) : d.radius (x ∘ f) ≤ d.radius x := d.radius_le _ (d.radius_nn _) (fun i j=> d.le_radius x (f i) (f j))
theorem radius_perm (x : Tape n I) (f : Equiv.Perm (Fin n)) : d.radius (x ∘ f)=d.radius x := le_antisymm (d.radius_comp ..) (by
  have h := d.radius_comp (x ∘ f) (f.symm : Fin n→Fin n)
  rwa [show ((x ∘ f) ∘ (f.symm : Fin n→Fin n))=x by ext i;simp] at h)

theorem radius_map {d' : Ground M} {f : I → M} (h : ∀ i j, d'.span (f i) (f j)=d.span i j) (x : Tape n I) : d'.radius (f ∘ x)=d.radius x := le_antisymm (d'.radius_le _ (d.radius_nn _) fun _ _=> by rw [comp_apply,comp_apply,h]; exact d.le_radius ..) (d.radius_le _ (d'.radius_nn _) fun i j=> by rw [← h]; exact d'.le_radius (f ∘ x) i j)

end Ground

/-- Hold any specified external slot fixed. Does NOT bound the scalar part (no slot, no assertion).
For constants use a separate per-cell density, or discard only after including
conditional denominator in source uses. -/
def hung (F : Flake n I) : Sheet (J:=Fin n × I) (fun _ => Tape n I) ℝ := fun a x=> if x a.1 = a.2 then F x else 0

def hike (d : Ground I) (n : ℕ) (σ : ℝ) : Expense (J:=Fin n × I) (fun _=> Tape n I) := fun _ x=> σ*d.radius x

def Held (d : Ground I) (σ p : ℝ) (F : Flake n I) := Ticket (hike d n σ) (hung F) p

def deck (d : Ground I) (σ : ℝ) (F : Flake n I) := amount (hike d n σ) (hung F)

variable {d : Ground I} {σ τ p q : ℝ} {F F' : Flake n I}

theorem deck_nn : 0 ≤ deck d σ F := amount_nonneg ..

theorem Held.uses (h : Held d σ p F) : Held d σ (deck d σ F) F := Ticket.uses h

/-- Total majorant of a single coefficient. -/
def mark (d : Ground I) (σ : ℝ) (F : Flake n I) (x : Tape n I) := bill (F x) (σ*d.radius x)

def row (V : Tape n I→ℝ≥0∞) (i : Fin n) (z : I) (x : Tape n I) := if x i=z then V x else 0

def Ensign (V : Tape n I→ℝ≥0∞) (p : ℝ≥0∞) := ∀ i z, ∑' x,row V i z x ≤ p

lemma ensign : Held d σ p F ↔ Ensign (mark d σ F) (ENNReal.ofReal p) := by
 have he (i z x): stamp (hung F (i,z) x) (hike d n σ (i,z) x)=row (mark d σ F) i z x:= by
  rw [stamp_real,hung,row,hike,mark]; dsimp only;split_ifs <;> simp [bill]
 constructor
 · rintro h i z
   simpa only [earning,he] using h (i,z)
 · rintro h ⟨i,z⟩; simpa only [earning,he] using h i z

lemma Ensign.mono {V U : Tape n I→ℝ≥0∞} {p q : ℝ≥0∞} (h : Ensign V p) (hU : U≤V) (hp : p≤q): Ensign U q := fun i z=> (ENNReal.tsum_le_tsum fun x=> by unfold row; split_ifs <;> [exact hU _;exact le_refl _]).trans ((h i z).trans hp)

lemma Ensign.point {V : Tape n I→ℝ≥0∞} {P : ℝ≥0∞} (h : Ensign V P) (hn : 0<n) (x) : V x ≤ P := by
 let i : Fin n:=⟨0,hn⟩
 simpa only [row,if_pos] using (ENNReal.le_tsum (f:=row V i (x i)) x).trans (h i (x i))

lemma Held.check (h : Held d σ p F) (hp : 0 ≤ p) (hn : 0<n) (x) : |F x| * Real.exp (σ*d.radius x) ≤ p := (ENNReal.ofReal_le_ofReal_iff hp).mp ((ensign.mp h).point hn x)

lemma Held.plain (h : Held d σ p F) (hp : 0≤p) (hs : 0≤σ) (hn : 0<n) (x) : |F x| ≤ p := (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hs (d.radius_nn x)))).trans (h.check hp hn x)

lemma mark_mono (ht : τ ≤ σ) (h : ∀ x, |F x| ≤ |F' x|) (x) : mark d τ F x ≤ mark d σ F' x := bill_mono (h x) (mul_le_mul_of_nonneg_right ht (d.radius_nn _))
lemma Held.mono (h : Held d σ p F') (ht : τ≤σ) (hp : p≤q) (hf : ∀ x,|F x|≤|F' x|) : Held d τ q F := ensign.mpr ((ensign.mp h).mono (mark_mono ht hf) (by gcongr))

lemma zero_held : Held d σ p (0 : Flake n I) := ensign.mpr fun i z=> by simp [row,mark,bill]
lemma Held.add (h : Held d σ p F) (hf : Held d σ q F') (hp : 0 ≤ p) (hq : 0≤q) : Held d σ (p+q) (F+F') := by
 have he:hung (F+F')=fun i x=> hung F i x+hung F' i x := by ext i x; dsimp [hung]; split_ifs<;>simp
 exact show Ticket _ _ _ from he ▸ Ticket.add h hf hp hq -- ▸ direction?
lemma Held.neg (h : Held d σ p F) : Held d σ p (-F) := h.mono le_rfl le_rfl (by simp)
lemma Held.sub (h : Held d σ p F) (hf : Held d σ q F') (hp : 0 ≤ p) (hq : 0≤q) : Held d σ (p+q) (F-F') := by
 rw [sub_eq_add_neg]; exact h.add hf.neg hp hq
lemma Held.smul (c : ℝ) (h : Held d σ p F) : Held d σ (|c| * p) (c • F) := by
 have he:hung (c • F)=fun i x=> c • hung F i x := by ext i x; dsimp only [hung]; split_ifs <;> simp
 rw [← Real.norm_eq_abs]; unfold Held; rw [he]; exact Ticket.smul h c

lemma Held.sum {M : Type} (s : Finset M) (F : M→Flake n I) (p : M→ℝ) (hp : ∀ i∈s, 0≤p i) (h : ∀ i∈s,Held d σ (p i) (F i)) : Held d σ (∑ i ∈ s,p i) (∑ i∈s,F i) := by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact zero_held
 | @insert a s ha ih=>
    simp only [sum_insert ha]
    have he : ∀ i∈s,0≤p i:=fun _ hi=>hp _ (by simp [hi])
    exact (h a (mem_insert_self ..)).add (ih he (fun i hi=>h _ (by simp [hi]))) (hp a (mem_insert_self ..)) (Finset.sum_nonneg he)

/-- Underlying scale-1 coordinates of analytic cells and meshes alike. -/
def carpet (I : Type) : Ground (Market I) where
 span x y:=sep x.1 y.1
 stay _:=sep_self _
 left _ _:=sep_comm ..
 slope _ _ _:=sep_triangle ..

end YM.RG08.Forms
