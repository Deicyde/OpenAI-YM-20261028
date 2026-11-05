import YM.Next.RANK.Exponential
import YM.Overlay.Terminal


/-!
# Array marker algebra

No packing factors from the *number of replicated cells* in the convolution
for one slot pattern. Each reflected copy has independent marker indices (not
hypothesizing independent cylinders). `Glyph` specializes to all subsets. We use
`deck` of total/corrected polynomials, so selecting even a single-mode coefficient
per copy is selecting it in one polynomial that had every insertion and every mask
simultaneously. In particular this keeps all cases with a unit insertion.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Next.Rank
open Marker
open scoped BigOperators
namespace Glyph

variable {V : Type*} [DecidableEq V] [Fintype V]
abbrev modes (V : Type*) [DecidableEq V] [Fintype V] := (Stock.census V).Mode
abbrev veil (V : Type*) [DecidableEq V] [Fintype V] := Poly (Stock.census V)

def scene (x : Finset V) : modes V := ⟨x,Finset.mem_univ _⟩
abbrev quiet (V : Type*) [DecidableEq V] [Fintype V] : modes V := (Stock.census V).quiet
abbrev slot (v : V) := (Stock.census V).fire v

@[simp] lemma same_scene (x y : Finset V) : scene x=scene y ↔ x=y := Subtype.ext_iff
@[simp] lemma scene_of (x : modes V) : scene x.val=x := rfl
@[simp] lemma scene_nil : scene ∅=quiet V := rfl
@[simp] lemma scene_single (v : V) : scene {v}=slot v := rfl

lemma part_mul (a b : veil V) (T : modes V) : (a*b).part T =
    ∑ s ∈ T.val.powerset,a.part (scene s)*b.part (scene (T.val \ s)) := by
  rw [Poly.part_mul]
  let X := Finset.univ.filter (fun s : modes V => s.val ⊆ T.val)
  have he (s : modes V) (hs : s.val ⊆ T.val) : ∀ y, Poly.merges s y T ↔ y=scene (T.val \ s.val) := by
    intro y; constructor
    · rintro ⟨h₁,h₂⟩; apply Subtype.ext
      change y.val=T.val \ s.val;rw [← h₂,Finset.union_sdiff_cancel_left h₁]
    rintro rfl; exact ⟨Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hs⟩
  rw [← Finset.sum_subset (Finset.subset_univ X) ?_]
  · let F (x y : modes V) := if Poly.merges x y T then a.part x*b.part y else 0
    change ∑ x∈ X, (∑ y, F x y)=_
    rw [show X=T.val.powerset.image scene by
      ext x; constructor
      · intro h; exact Finset.mem_image.mpr ⟨_,Finset.mem_powerset.mpr (Finset.mem_filter.mp h).2,rfl⟩
      intro h; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_powerset.mp hy⟩,
      Finset.sum_image (fun _ _ _ _ h => (same_scene ..).mp h)]
    refine Finset.sum_congr rfl fun y hy => ?_
    have h y' : Poly.merges (scene y) y' T ↔ y'=scene (T.val \ y) := he _ (Finset.mem_powerset.mp hy) _
    simp [F,h]
  intro i _ hi; apply Finset.sum_eq_zero; intro j _; split_ifs with h
  · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [← h.2]; exact Finset.subset_union_left⟩))
  rfl

/-- Multiply by one monomial. -/
lemma plate (x : modes V) (c : ℂ) (P : veil V) (T : modes V) :
    (Poly.send x c * P).part T = if x.val ⊆ T.val then c * P.part (scene (T.val \ x.val)) else 0 := by
  rw [part_mul]; split_ifs with hx
  · rw [Finset.sum_eq_single x.val]
    · simp
    · intro b _ hb; rw [Poly.part_send,if_neg (fun h => hb (Subtype.ext_iff.mp h)),zero_mul]
    simp [hx]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Poly.part_send, if_neg (fun h => hx (by rw [← h]; exact Finset.mem_powerset.mp hi)),zero_mul]

lemma plate_pair (x y : modes V) (c b : ℂ) : Poly.send x c * Poly.send y b =
    if Disjoint x.val y.val then Poly.send (scene (x.val ∪ y.val)) (c*b) else 0 := by
  by_cases h : Disjoint x.val y.val
  · rw [if_pos h]; ext i
    change (Poly.prod _ _).part _=_; rw [Poly.cart,Poly.part_send]
    simp only [show Poly.merges x y i ↔ i = scene (x.val ∪ y.val) by simp [Poly.merges,h,Subtype.ext_iff,scene,eq_comm]]
  rw [if_neg h];ext i; exact (Poly.cart x y i c b).trans (if_neg (fun hx => h hx.1))

private def rawPoly (S : Finset V) (x : V → ℂ) : veil V := ∏ i∈ S,(1+Poly.send (slot i) (x i))



private lemma raw_eval (S : Finset V) (x : V → ℂ) (T : modes V) : (rawPoly S x).part T =
    if T.val ⊆ S then ∏ i∈T.val,x i else 0 := by
  induction S using Finset.induction_on generalizing T with
  | empty =>
    simp only [rawPoly, Finset.prod_empty,Poly.one_part,Finset.subset_empty]
    simp only [show T= Census.quiet (Stock.census V) ↔ T.val=∅ from Subtype.ext_iff]; split <;> simp [*]
  | @insert i S hi ih =>
    rw [rawPoly, Finset.prod_insert hi]; change ((1+_) * rawPoly _ _).part _=_
    rw [add_mul,one_mul,Poly.part_plus,plate,ih]
    change _+(if {i}⊆T.val then x i*(rawPoly S x).part (scene (T.val \ {i})) else 0)=_
    by_cases ht : i∈T.val
    · have h : ¬ T.val ⊆ S := fun hc => hi (hc ht)
      have h₁ : T.val \ {i} = T.val.erase i := by ext; simp [and_comm]
      have h₂ : T.val ⊆ insert i S ↔ (T.val.erase i) ⊆ S := by
        constructor
        · intro H x hx
          exact (Finset.mem_insert.mp (H (Finset.mem_erase.mp hx).2)).resolve_left (Finset.mem_erase.mp hx).1
        intro H
        rw [← Finset.insert_erase ht]; exact Finset.insert_subset_insert _ H
      rw [if_neg h,zero_add,if_pos (Finset.singleton_subset_iff.mpr ht),h₁,ih]
      simp only [h₂]
      change x i*(if _ ⊆ S then (∏ j∈ T.val.erase i,x j) else 0)=_
      split
      · rw [if_pos (by assumption)]; exact Finset.mul_prod_erase _ x ht
      · rw [if_neg (by assumption),mul_zero]
    have h (hh : T.val ⊆ insert i S) : T.val ⊆ S := fun a ha =>
      (Finset.mem_insert.mp (hh ha)).resolve_left (fun hx => ht (hx ▸ ha))
    simp only [if_neg (show ¬ {i} ⊆ T.val from (mt Finset.singleton_subset_iff.mp ht)),add_zero,show T.val ⊆ insert i S ↔ T.val ⊆ S from ⟨h,fun H => H.trans (Finset.subset_insert _ _)⟩]

def raw (X : V → ℂ) : veil V := rawPoly Finset.univ X
lemma expand (X : V → ℂ) (s) : (raw X).part s=∏ i∈s.val,X i := by simp only [raw,raw_eval,Finset.subset_univ,↓reduceIte]
@[simp] lemma raw_part (X : V → ℂ) : (raw X).part (quiet V)=1 := by simp [expand,quiet,Census.quiet]

-- ordinary coefficient conjugation

def shade : veil V →+* veil V where
  toFun a := Poly.inject fun x => star (a.part x)
  map_add' a b := Poly.ext fun i => by simp only [Poly.part_plus]; exact star_add ..
  map_mul' a b := by
    apply Poly.ext; intro i
    change star ((a*b).part i) = _
    rw [part_mul,part_mul,star_sum]
    exact Finset.sum_congr rfl fun _ _ => star_mul' ..
  map_one' := Poly.ext fun i => by
    change star ((1 : veil V).part i) = (1 : veil V).part i; rw [Poly.one_part]; split <;> simp
  map_zero' := Poly.ext fun i => by change star (0:ℂ) = 0; exact star_zero _

@[simp] lemma shade_part (a : veil V) (s) : (shade a).part s=star (a.part s) := rfl
lemma shade_pass (a : veil V) : shade (Poly.pass a)=Poly.pass (shade a) := by
  have he (c : ℂ) (x : veil V) : shade (c • x)=star c • shade x := by ext; simp
  simp [Poly.pass,he]

variable {W : Type*} [DecidableEq W] [Fintype W]

def push (x : W) (T : modes V) : modes (W×V) := scene ({x} ×ˢ T.val)
def homes (S : Finset W) (T : modes (W×V)) := T.val.image Prod.fst ⊆ S
instance (S : Finset W) (T : modes (W×V)) : Decidable (homes S T) := by unfold homes; infer_instance

def fibre (x : W) (T : modes (W×V)) : modes V := scene (Finset.univ.filter fun v => (x,v)∈T.val)
@[simp] lemma fibre_mem (w : W) (x : modes (W×V)) (v : V) : v∈(fibre w x).val ↔ (w,v)∈x.val := by simp [fibre,scene]
@[simp] lemma push_mem (w y : W) (x : modes V) (v : V) : (y,v)∈(push w x).val ↔ y=w ∧ v∈x.val := by simp [push,scene,and_comm, eq_comm]
@[simp] lemma push_injective (w : W) (s t : modes V) : push w s=push w t ↔ s=t := by
  constructor
  · intro h; apply Subtype.ext; ext i; simp only [← show (w,i)∈(push w s).val ↔ i∈s.val by simp, h]
    simp
  exact congr_arg _

@[simp] lemma dock (w : W) (s : modes V) : fibre w (push w s)=s := by apply Subtype.ext; ext i; simp
@[simp] lemma empty_dock (w : W) : push w (quiet V)=quiet (W×V) := by apply Subtype.ext; ext ⟨i,t⟩; simp [quiet,scene,Census.quiet,push]

lemma settle (x : W) (s : modes V) : homes {x} (push x s) := by
  intro i hi; obtain ⟨⟨a,b⟩,ht,rfl⟩ := Finset.mem_image.mp hi; rw [(push_mem .. |>.mp ht).1]; exact Finset.mem_singleton.mpr rfl

/-- one local algebra as subalgebra of the big array. -/
private def piece (w : W) (a : veil V) : veil (W×V) := ∑ i : modes V, Poly.send (push w i) (a.part i)
private lemma piece_add (w : W) (a b : veil V) : piece w (a+b)=piece w a +piece w b := by ext; simp only [piece,Poly.part_plus,Poly.part_sum,Poly.part_send,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; split <;> simp

def insertAt (w : W) : veil V →ₐ[ℂ] veil (W×V) := by
  have z : piece w (0 : veil V) = 0 := by simp [piece]
  let k : veil V →+ veil (W×V) := { toFun := piece w,map_zero' := z,map_add' := piece_add w }
  have he (a : modes V) (v : ℂ) : k (Poly.send a v)=Poly.send (push w a) v := by
    change ∑ i, Poly.send _ _ = _
    rw [Finset.sum_eq_single a]
    · simp only [Poly.part_send,↓reduceIte]
    · intro b _ hb; rw [Poly.part_send, if_neg hb, Poly.send_zero]
    simp
  have hp (a b : modes V) : Disjoint (push w a).val (push w b).val ↔ Disjoint a.val b.val := by
    simp only [Finset.disjoint_left]; constructor
    · intro h i hi hj; exact h (show (w,i)∈_ from (push_mem ..).mpr ⟨rfl,hi⟩) ((push_mem ..).mpr ⟨rfl,hj⟩)
    intro h ⟨t,y⟩ hi hj; exact h ((push_mem ..).mp hi).2 ((push_mem ..).mp hj).2
  refine { toFun := k,map_add' := fun _ _ => map_add k ..,map_zero' := z,map_mul' := ?_,map_one' := ?_, commutes' := fun r => ?_ }
  · change k (Poly.send (quiet V) 1)= Poly.send (quiet (W×V)) 1; rw [he,empty_dock]
  · have hx (i j : modes V) (a b : ℂ) : k (Poly.send i a * Poly.send j b)= k (Poly.send i a)*k (Poly.send j b) := by
      rw [plate_pair,he,he,plate_pair]; simp only [hp]
      split_ifs <;> first | exact z | skip
      rw [he]; congr 1
      apply Subtype.ext; ext ⟨t,w⟩; simp [push,scene]
    intro a b
    change k (a*b)= k a * k b
    rw [← Poly.studs a, ← Poly.studs b, Finset.sum_mul_sum]
    simp_rw [map_sum, hx]; rw [Finset.sum_mul_sum]
  change k (Poly.send _ r)=Poly.send _ r; rw [he,empty_dock]

lemma insert_part (w : W) (a : veil V) (T : modes (W×V)) : (insertAt w a).part T = if homes {w} T then a.part (fibre w T) else 0 := by
  change (piece w a).part T = _
  rw [piece, Poly.part_sum]; split_ifs with he
  · have hv : T=push w (fibre w T) := by
      apply Subtype.ext; ext ⟨i,t⟩
      rw [push_mem,fibre_mem]; constructor
      · intro hi
        have hx : i∈({w} : Finset W) := he (Finset.mem_image_of_mem Prod.fst hi)
        rw [Finset.mem_singleton] at hx; subst i; exact ⟨rfl,hi⟩
      rintro ⟨rfl,hi⟩; exact hi
    -- avoid substituting T inside fibre
    rw [Finset.sum_eq_single (fibre w T)]
    · rw [Poly.part_send, if_pos hv]
    · intro j _ hj; exact (Poly.part_send ..).trans (if_neg (fun h => hj ((push_injective ..).mp (h.symm.trans hv))))
    simp
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Poly.part_send, if_neg (fun (ht : T=push w i) => he (ht.symm ▸ settle w i))]

lemma insert_send (w : W) (x : modes V) (c : ℂ) : insertAt w (Poly.send x c)=Poly.send (push w x) c := by
  change (piece w _) = _
  unfold piece; rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; rw [Poly.part_send,if_neg hy,Poly.send_zero]
  simp

lemma insert_quiet (w : W) (x : veil V) : (insertAt w x).part (quiet (W×V))=x.part (quiet V) := by
  rw [insert_part, if_pos, show fibre w (quiet (W×V))=quiet V by rw [← empty_dock w,dock]]
  simp [homes,quiet,Census.quiet]

lemma insert_pass (w : W) (x : veil V) (h : x.part (quiet V)=0) : Poly.pass (insertAt w x)=insertAt w (Poly.pass x) := by
  let d := max (Fintype.card (W×V)) (Fintype.card V)
  have h' : (insertAt w x).part (quiet (W×V))=0 := (insert_quiet ..).trans h
  rw [Exponential.pass_extend h' d (le_max_left ..),Exponential.pass_extend h d (le_max_right ..)]
  simp only [map_sum,map_smul,map_pow]

/-- This is a single polynomial, all coefficients independent names. -/
def deck (X : W → veil V) : veil (W×V) := ∏ i, insertAt i (X i)

-- Hand calculation including missing slots and unsupported modes.
private lemma content (X : W → veil V) (P : Finset W) (s : modes (W×V)) :
    (∏ i∈P, insertAt i (X i)).part s =
      if homes P s then ∏ i∈P,(X i).part (fibre i s) else 0 := by
  induction P using Finset.induction_on generalizing s with
  | empty =>
    simp only [Finset.prod_empty,Poly.one_part,homes,Finset.subset_empty]
    simp [Census.quiet,Subtype.ext_iff]
  | @insert w t ht ih =>
    rw [Finset.prod_insert ht, show insertAt w (X w)=piece w (X w) from rfl, piece, Finset.sum_mul, Poly.part_sum]
    by_cases hp : homes (insert w t) s
    · let b := push w (fibre w s)
      have hb : b.val ⊆ s.val := by
        rintro ⟨i,v⟩ h; obtain ⟨rfl,he⟩ := (push_mem ..).mp h; exact (fibre_mem ..).mp he
      rw [if_pos hp, Finset.sum_eq_single (fibre w s)]
      · have hu : homes t (scene (s.val \ b.val)) := by
          intro i hi
          obtain ⟨⟨j,v⟩,hj,rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨h,hv⟩ := Finset.mem_sdiff.mp hj
          have he : j∈insert w t := hp (Finset.mem_image_of_mem Prod.fst h)
          refine (Finset.mem_insert.mp he).resolve_left (fun hk => hv ?_)
          exact (push_mem ..).mpr ⟨hk,(fibre_mem ..).mpr (hk ▸ h)⟩
        rw [plate, if_pos hb,ih,if_pos hu,Finset.prod_insert ht]
        congr 1
        apply Finset.prod_congr rfl; intro i hi
        congr 1
        apply Subtype.ext; ext v; rw [fibre_mem,fibre_mem]
        change (i,v)∈ s.val \ b.val ↔ _; rw [Finset.mem_sdiff]; exact ⟨And.left,fun hx => ⟨hx,fun he => ht (((push_mem ..).mp he).1 ▸ hi)⟩⟩
      · intro c _ hc; rw [plate]; split_ifs with h
        · rw [ih]; split_ifs with hq
          · exfalso; apply hc
            apply Subtype.ext; ext x; rw [fibre_mem]; constructor
            · intro he; exact h ((push_mem ..).mpr ⟨rfl,he⟩)
            intro he; by_contra H
            exact ht (hq (Finset.mem_image_of_mem Prod.fst (show (w,x)∈ (scene (s.val \ (push w c).val)).val from
              Finset.mem_sdiff.mpr ⟨he,fun a => H ((push_mem ..).mp a).2⟩)))
          rw [mul_zero]
        rfl
      simp
    rw [if_neg hp]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [plate]; split_ifs with h
    · rw [ih,if_neg (show ¬ homes t _ from ?_), mul_zero]
      intro hv; apply hp
      intro x hx; obtain ⟨⟨j,v⟩,hj,rfl⟩ := Finset.mem_image.mp hx
      rcases eq_or_ne j w with g|g
      · exact g ▸ Finset.mem_insert_self ..
      refine Finset.mem_insert_of_mem (hv (Finset.mem_image_of_mem Prod.fst ?_))
      exact (show (j,v) ∈ (scene _).val from Finset.mem_sdiff.mpr ⟨hj,fun a => g ((push_mem ..).mp a).1⟩)
    rfl

lemma deck_part (X : W → veil V) (s) : (deck X).part s=∏ i,(X i).part (fibre i s) := by rw [deck,content,if_pos (show homes Finset.univ s from Finset.subset_univ _)]
lemma deck_mul (F P : W → veil V) : deck F*deck P=deck (fun i => F i*P i) := by simp only [deck,map_mul,Finset.prod_mul_distrib]
lemma deck_pass (X : W → veil V) (h : ∀ i,(X i).part (quiet V)=0) : deck (fun i => Poly.pass (X i)) = Poly.pass (∑ i,insertAt i (X i)) := by
  rw [Exponential.pass_sum]; unfold deck
  · simp only [insert_pass _ _ (h _)]
  intro i _; exact (insert_quiet i (X i)).trans (h i)

def allCells (W : Type*) [DecidableEq W] [Fintype W] (x : modes V) : modes (W×V) := scene (Finset.univ ×ˢ x.val)

@[simp] lemma each (s : modes V) (w : W) : fibre w (allCells W s)=s := by apply Subtype.ext; ext i; simp [fibre, allCells, scene]
lemma all_price (s : modes V) (a : ℝ) : Poly.toll (fun _ : W × V => a) (allCells W s) =
    (a^s.val.card)^Fintype.card W := by simp [Poly.toll, allCells, scene,← pow_mul,mul_comm]

end Glyph
end YM.Next.Rank
