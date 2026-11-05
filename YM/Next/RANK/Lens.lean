import YM.Next.RANK.Beamers
import YM.Next.RANK.LegBlock

/-! Exact finite sampling by coefficient dual rows at this stamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice Wilson CellsInt Maxwell Labels Tensor Function Finset Configuration
open scoped Classical Topology BigOperators

variable {G : Gauge} {n k a b d : ℕ}

abbrev Hub (G : Gauge) (d : ℕ) (j : ℕ) := {p : Degree G // p.point=0 ∧ j ≤ p.degree ∧ p.degree+2≤d}
noncomputable instance (G : Gauge) (d j : ℕ) : Fintype (Hub G d j) := by
  let Q := (i : Fin (d+1)) × (Fin i.val → Axis) × PlaqAxes × G.ColorIndex
  let f (h : Hub G d j) : Q := ⟨⟨h.val.degree,by have hp := h.property; omega⟩,h.val.layout,h.val.a,h.val.paint⟩
  let g (i : Q) : Degree G := ⟨i.2.2.1,i.2.2.2,0,i.1,i.2.1⟩
  have ht (x : Hub G d j) : g (f x)=x.val := by
    rcases x with ⟨⟨A,b,p,d,x⟩,h,h'⟩; change p=0 at h; subst p; rfl
  exact Fintype.ofInjective f fun i j h => Subtype.ext ((ht i).symm.trans (h ▸ ht j))

abbrev Shelf (G : Gauge) (d : ℕ) (j : ℕ) := {t : KeyIn G d // j≤ t.val.1}

-- Ingredient separation: j-th derivatives at 0 on positives see *all* Taylor j when restricted to closed. (No Shell yet.)

def focus (j : ℕ) := LinearMap.pi (fun i : Hub G d j => gesture i.val)
lemma lens (j : ℕ) (x : Horizon G) (hx : shutter x) : ∃ A : Taylor G j, ∀ L : Degree G,
    L.degree=j → L.point=0 → gesture L x=gesture L (sweep j A) := by
  have hu := sprout j (secured x hx); let A := contracted hu
  refine ⟨A,?_⟩; rintro ⟨a,i,p,k,t⟩ hk hp; change k=j at hk; change p=0 at hp; subst k; subst p
  let L : Degree G := ⟨a,i,0,j,t⟩
  rw [gesture_hits, gesture_hits,show sweep j A=inspect A from rfl]
  change _=jumps j t (polar (inspect A) _ _) 0 i
  rw [inspected,test_top, show takeCurl A=leaf j (polar x) from curl_inverse hu]
  simp only [leaf,fertile, smul_smul, mul_inv_cancel₀ (show (j.factorial:ℝ) ≠ 0 by positivity), one_smul]

lemma judges (j : ℕ) (h : j+2≤d) (A B : Taylor G j) (he : focus (d:=d) j (sweep j A)=focus j (sweep j B)) : A=B := by
  have ht (a b : Axis) (hab : a<b) : takeCurl A a b = takeCurl B a b := by
    apply seedEq; intro t
    let e : PlaqAxes := ⟨(a,b),hab⟩
    apply smul_right_injective G.Color (show (j.factorial:ℝ) ≠ 0 by positivity); apply PiLp.ext; intro i
    let L : Degree G := ⟨e,i,0,j,t⟩
    have hx D : gesture L (sweep j D)= ((↑j.factorial:ℝ) • takeCurl D a b (basis ∘ t)) i := by
      rw [gesture_hits, show sweep j D=inspect D from rfl, inspected]; change jumps j t (test D a b) (0:Cover) i=_; rw [test_top]
    rw [← hx, ← hx]; exact congr_fun he ⟨L,rfl,le_rfl,h⟩
  apply Maxwell.potential.injective; apply Subtype.ext; change takeCurl A = takeCurl B
  funext a b; rcases lt_trichotomy a b with h|u|h
  · exact ht a b h
  · subst b; apply Tensor.ext_diag _ _ ((closedCurl _).coeffSym a a) ((closedCurl _).coeffSym a a)
    rw [takeCurl_diag,takeCurl_diag, sub_self, sub_self]
  rw [(closedCurl A).antisymmetric a b, (closedCurl B).antisymmetric a b,ht b a h]

-- synthesize segment versions. Convenient to sum over ALL keys with arbitrary coefficient v grouped by grade. Focus j reads only gen≥j.
def piano (G : Gauge) (d a : ℕ) (r : Shelf G d a → ℝ) : Horizon G := ∑ i,r i • tester i.val.val

def fan (k : Fin (Labels.dim G n)) (h : n+2 ≤ d) (hp : a ≤ n) : Shelf G d a := ⟨⟨⟨n,k⟩,h⟩,hp⟩
lemma lists (h : n+2 ≤ d) (hp : a ≤ n) :
    univ.filter (fun p : Shelf G d a => p.val.val.1=n) = univ.image (fun i : Fin (Labels.dim G n) => fan i h hp) := by
  ext ⟨⟨⟨s,v⟩,hh⟩,hg⟩; simp only [mem_filter,mem_univ,true_and,mem_image]
  refine ⟨fun he => ?_,?_⟩
  · subst s; exact ⟨v,rfl⟩
  rintro ⟨p,H⟩; exact (congr_arg (fun q : Shelf G d a => q.val.val.1) H).symm

lemma rank_name (h : n+2≤ d) (hp : a ≤ n) (r : Shelf G d a → ℝ) (L : Degree G) (hv : L.degree=n)
    (hz : ∀ i : Shelf G d a, n < i.val.val.1 → r i=0) :
    let A := ∑ k,r (fan k h hp) • axes G n k
    gesture L (piano G d a r)=gesture L (sweep n A) := by
  intro A; unfold piano
  rw [map_sum]; let f (i : Shelf G d a) := gesture L (r i • tester i.val.val)
  change ∑ i,f i= _
  let J := univ.filter (fun p : Shelf G d a => p.val.val.1=n)
  have he : ∑ i∈J,f i=∑ i,f i := by
    apply sum_subset (subset_univ J); intro i _ hi
    have ht : i.val.val.1 ≠ n := fun H => hi (mem_filter.mpr ⟨mem_univ _,H⟩)
    rcases lt_or_gt_of_ne ht with H|H
    · unfold f; rw [map_smul,tester, gesture_over L (show i.val.val.1<L.degree from hv ▸ H), smul_zero]
    unfold f; rw [hz i H,zero_smul,map_zero]
  rw [← he,show J= _ from lists (G:=G) h hp,sum_image]
  · unfold A; rw [map_sum,map_sum]; simp_rw [f,tester,map_smul]; rfl
  intro i _ j _ h₁; exact eq_of_heq ((Sigma.mk.inj (congr_arg (fun p : Shelf G d a => p.val.val) h₁)).2)

lemma keyboard (G : Gauge) (d a : ℕ) (x : Shelf G d a→ℝ)
    (h : focus (G:=G) (d:=d) a (piano G d a x)=0) : x=0 := by
  classical
  let z (i) := ∀ u : Shelf G d a, i ≤ u.val.val.1 → x u=0
  have H : ∀ i, i≤d → z i := by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self => rintro ⟨⟨⟨v,j⟩,h⟩,hp⟩ hj; change d≤v at hj; change v+2 ≤ d at h; omega
    | of_succ i hi IH =>
      intro u hu; rcases eq_or_lt_of_le hu with he|he
      · have ha : a ≤ i := he.symm ▸ u.property
        have hp : i+2≤d := he.symm ▸ u.val.property
        let A : Taylor G i := ∑ k,x (fan k hp ha) • axes G i k
        have hz : (focus (d:=d) i) (sweep i A) = focus (d:=d) i (sweep i (0 : Taylor G i)) := by
          rw [map_zero, map_zero]; funext p
          obtain ⟨u,hu,hk,hp'⟩ := p
          change gesture u (sweep i A) = 0
          rcases lt_or_eq_of_le hk with hz|hz
          · exact gesture_over u hz A
          rw [show gesture u (sweep i A) = gesture u (piano G d a x) from (rank_name hp ha x u hz.symm (fun b hb => IH b hb)).symm]
          exact congr_fun h ⟨u,hu,ha.trans hk,hp'⟩
        have ht := judges i hp A 0 hz
        have hs (k : Fin (Labels.dim G i)) : (axes G i).repr A k=x (fan k hp ha) := by simp [A,Finsupp.single_apply]
        have hx (k) : x (fan k hp ha)=0 := by rw [← hs k,ht,map_zero]; rfl
        rcases u with ⟨⟨⟨w,k⟩,hr⟩,h₁⟩; change i=w at he; subst w; exact hx _
      exact IH u he
  funext i; exact H 0 (Nat.zero_le _) i (Nat.zero_le _)
end YM.Next.Rank.Beamer
