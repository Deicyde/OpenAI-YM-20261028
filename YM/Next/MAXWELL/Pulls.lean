import YM.Next.MAXWELL.Recurse

/-!
# List-of-factors version of the same free moments

Entries in a real one-leg component. On equal positions we *forbid* an
edge; this lets us state useful covariance and order facts for pulled
raw factor lists. Evaluating an actual composite label still only on
conf; the equal-positions convention then only applies to repeated
positions of legs of one polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis Wick
open scoped Topology ContDiff BigOperators

section list
variable {β γ R S : Type*} [AddCommMonoid R] [AddCommMonoid S]

def pulls (u : List β) (f : β → List β → R) := ∑ i : Fin u.length, f (u.get i) (u.eraseIdx i.val)

lemma pulls_cons (a : β) (u : List β) (f : β → List β → R) :
    pulls (a::u) f = f a u + pulls u (fun b v => f b (a::v)) := by
  let F (i : Fin (u.length+1)) := f ((a::u).get i) ((a::u).eraseIdx i.val)
  change (∑ i : Fin (u.length+1), F i) = _
  rw [Fin.sum_univ_succ]
  rfl

lemma pulls_nil (f : β → List β → R) : pulls [] f = 0 := by
  haveI : IsEmpty (Fin ([] : List β).length) := inferInstanceAs (IsEmpty (Fin 0))
  exact Finset.sum_of_isEmpty ..

lemma pulls_zero (L : List β) : pulls L (fun _ _ => (0:R))=0 := by simp [pulls]

lemma pulls_congr (u : List β) {f g : β → List β → R}
    (h : ∀ i : Fin u.length, f (u.get i) (u.eraseIdx i.val) = g (u.get i) (u.eraseIdx i.val)) :
    pulls u f = pulls u g := Finset.sum_congr rfl fun i _ => h i

lemma pulls_map (h : β → γ) (u : List β) (f : γ → List γ → R) :
    pulls (u.map h) f = pulls u (fun a b => f (h a) (b.map h)) := by
  induction u generalizing f with
  | nil => rw [List.map_nil,pulls_nil,pulls_nil]
  | cons a u ih => rw [List.map_cons,pulls_cons,pulls_cons,ih]; rfl

lemma sum_from_pulls (u : List β) (f : β → List β → R) (L : R →+ S) :
    L (pulls u f) = pulls u (fun b p => L (f b p)) := map_sum ..

lemma pulls_twice (u : List β) (f : β → β → List β → R) :
    pulls u (fun a v => pulls v (fun b w => f a b w)) =
      pulls u (fun b v => pulls v (fun a w => f a b w)) := by
  induction u generalizing f with
  | nil => rw [pulls_nil,pulls_nil]
  | cons a u ih =>
    simp_rw [pulls_cons]
    have he := ih fun a' b w => f a' b (a::w)
    unfold pulls at *; simp_rw [Finset.sum_add_distrib,he]
    ac_rfl

lemma pulls_append (u v : List β) (f : β → List β → R) :
    pulls (u++v) f = pulls u (fun x p => f x (p++v)) + pulls v (fun x p => f x (u++p)) := by
  induction u generalizing f with
  | nil => rw [List.nil_append,pulls_nil,zero_add]; simp
  | cons a u ih => rw [List.cons_append,pulls_cons,pulls_cons,ih]; simp [add_assoc]

lemma pulls_short {L : List β} (i : Fin L.length) : (L.eraseIdx i.val).length < L.length := by
  have := List.length_eraseIdx_add_one i.isLt
  omega
end list

section Match
variable {ι κ R : Type*} [CommSemiring R]

/-- Evaluate scalar matching sum with kernel E (uses list order; don't
assert any symmetry before proving it). -/
def pairCost (E : ι → ι → R) : (L : List ι) → R
  | [] => 1
  | a::l => ∑ i : Fin l.length, E a (l.get i) * pairCost E (l.eraseIdx i.val)
termination_by L => L.length
decreasing_by exact lt_trans (pulls_short _) (by simp)

lemma pair_step (E : ι → ι → R) (a : ι) (L : List ι) :
    pairCost E (a::L) = pulls L (fun b p => E a b * pairCost E p) := by rw [pairCost]; rfl

lemma pair_transfer (f : κ → ι) (E : ι → ι → R) (L : List κ) :
    pairCost E (L.map f) = pairCost (fun a b => E (f a) (f b)) L := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
    subst n; cases L with
    | nil => simp only [List.map_nil,pairCost]
    | cons a l =>
      rw [List.map_cons,pair_step,pair_step,pulls_map]; apply pulls_congr
      intro i; rw [ih _ (lt_trans (pulls_short i) (by simp)) _ rfl]
end Match

variable {G : Gauge} {n : ℕ}

/-- One real probe. -/
abbrev Factor (G : Gauge) := (j : ℕ) × Probe G j

def letter (p : Factor G) := symbol p.1 p.2

def coordF (s : Slot G) : Factor G := ⟨s.1, coordinateLeg s⟩
lemma letter_coord (s : Slot G) : letter (coordF s) = MvPolynomial.X s := symbol_coordinate _

def bag {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (p : List ι) (a : α) : WickPol G :=
  (p.map fun i => if a=q i then letter (L i) else 1).prod

lemma bag_cons {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (i : ι) (p : List ι) (a : α) :
    bag q L (i::p) a = (if a=q i then letter (L i) else 1) * bag q L p a := by simp [bag]

lemma bag_merge {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (p l : List ι) (a : α) :
    bag q L (p++l) a = bag q L p a * bag q L l a := by simp [bag]

lemma bag_pick {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (p : List ι) (a : α) (i : Fin p.length) :
    bag q L p a = (if a=q (p.get i) then letter (L (p.get i)) else 1) * bag q L (p.eraseIdx i) a := by
  induction p with
  | nil => exact Fin.elim0 i
  | cons b p ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact bag_cons ..
    change bag q L (b::p) a = (if a=q (p.get _) then _ else _) * bag q L (b::p.eraseIdx j.val) a
    rw [bag_cons,bag_cons,ih j,mul_left_comm]; rfl

abbrev Limb (G : Gauge) := E4 × Factor G

def linkEntry (p q : Limb G) : ℂ := open scoped Classical in if p.1=q.1 then 0 else (K p.2.2 q.2.2 p.1 q.1 : ℂ)

lemma link_eq (x y : E4) (p q : Factor G) (h : x ≠ y) :
    linkEntry (x,p) (y,q) = (K p.2 q.2 x y : ℂ) := if_neg h

lemma link_zero (x : E4) (p q : Factor G) : linkEntry (x,p) (x,q) = 0 := if_pos rfl

lemma eat_bag {ι : Type*} (q : ι → Fin n) (L : ι → Factor G) (p : List ι) {x : Points n} (hx : x ∈ conf n)
    (a b : Fin n) (hab : a ≠ b) (u : Factor G) :
    eat u.2 (x a) (x b) (bag q L p b) = pulls p (fun t r =>
      if b=q t then linkEntry (x a,u) (x b,L t) • bag q L r b else 0) := by
  induction p with
  | nil => rw [pulls_nil]; exact Derivation.map_one_eq_zero _
  | cons i p ih =>
    rw [bag_cons,pulls_cons]; split_ifs with h
    · have HK := eat_symbol u.2 (L i).2 (show x a ≠ x b from (show Injective x.ofLp from hx).ne hab)
      rw [Derivation.leibniz,ih]
      rw [show eat u.2 (x a) (x b) (letter (L i)) = MvPolynomial.C _ from HK,
        link_eq _ _ _ _ ((show Injective x.ofLp from hx).ne hab)]
      simp only [smul_eq_mul,pulls,Finset.mul_sum]; rw [add_comm]; congr 1
      · rw [mul_comm,MvPolynomial.C_mul']
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [bag_cons,if_pos h]; split_ifs
      · rw [mul_smul_comm]

      rw [mul_zero]
    rw [one_mul,ih,zero_add]; apply pulls_congr; intro t; rw [bag_cons,if_neg h,one_mul]

/-- Arbitrary arity, each label is the product of all its listed real legs
(empty = unit), no factorials attached. -/
theorem bag_rec {ι : Type*} (q : ι → Fin n) (L : ι → Factor G) (p : List ι) {x : Points n} (hx : x ∈ conf n) :
    moment G x (bag q L p) = pairCost linkEntry (p.map fun i => ((x (q i),L i) : Limb G)) := by
  induction h : p.length using Nat.strong_induction_on generalizing p with
  | h m ih =>
    subst m; cases p with
    | nil => rw [List.map_nil,pairCost,show bag q L [] = fun _ => 1 from rfl]; exact constants _
    | cons a p =>
      have he : bag q L (a::p) = update (bag q L p) (q a) (letter (L a) * bag q L p (q a)) := by
        ext1 i; by_cases h : i=q a <;> simp_all [bag]
      rw [List.map_cons,pair_step,pulls_map, he,letter,moment_one _ _ _ hx]
      let A := fun i => ((x (q i),L i) : Limb G)
      let B := bag q L p
      let S := Finset.univ.erase (q a)
      let u := (L a).snd
      have hh (b : Fin n) (hb : b∈ S) : moment G x (update B b (eat u (x (q a)) (x b) (B b))) =
          pulls p (fun t r => moment G x (update B b (if b=q t then linkEntry (x (q a),L a) (x b,L t) • bag q L r b else 0))) := by
        change moment G x (update B b (eat (L a).2 _ _ (bag q L p b))) = _
        rw [eat_bag _ _ p hx _ b (Ne.symm (Finset.mem_erase.mp hb).1),pulls, MultilinearMap.map_update_sum]; rfl
      change (∑ b ∈ S, moment G x (update B b (eat _ _ _ (B b)))) = pulls p _
      calc
        _ = pulls p (fun t r => ∑ b ∈ S, moment G x (update B b (if b=q t then linkEntry (A a) (x b,L t) • bag q L r b else 0))) := by
          unfold pulls; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b hb => hh b hb
        _ = _ := by
          apply pulls_congr; intro i
          let z := p.get i
          let r := p.eraseIdx i.val
          have hn : r.length < (a::p).length := lt_trans (pulls_short i) (by simp)
          change (∑ b ∈ S,moment G x (update B b (if b=q z then _ else 0))) = linkEntry (A a) (A z) * pairCost linkEntry (r.map A)
          by_cases hw : q z=q a
          · rw [show linkEntry (A a) (A z)=0 from by dsimp only [A]; rw [hw]; exact link_zero ..,zero_mul]
            apply Finset.sum_eq_zero; intro b hb
            rw [if_neg (fun ha => (Finset.mem_erase.mp hb).1 (ha.trans hw))]; exact MultilinearMap.map_coord_zero _ _ (update_self ..)
          rw [Finset.sum_eq_single_of_mem (q z) (Finset.mem_erase.mpr ⟨hw,Finset.mem_univ _⟩)];
          · rw [if_pos rfl,MultilinearMap.map_update_smul,show update B (q z) (bag q L r (q z))= bag q L r from ?_,ih _ hn r rfl]; rfl
            ext1 b; by_cases he : b=q z
            · rw [he, update_self]
            rw [update_of_ne he]; change bag q L p b = _; rw [bag_pick q L p b i,if_neg he,one_mul]
          intro b hb he
          rw [if_neg he]; exact MultilinearMap.map_coord_zero _ _ (update_self ..)

end YM.Maxwell.Free
