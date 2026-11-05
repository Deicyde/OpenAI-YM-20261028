import YM.Next.RANK.Common
import YM.Next.RANK.LegBlock

/-!
# Vertex error bound ON calibrated data

An overloaded arrangement of all endpoint coordinates. Charge admits exact
low readout on key-facing substitutions. Cost powers in Efficiency go on weights
$v,u$ in previous phases, here expose the vertex bounds needed after normal ordering
with all actual sign conventions and folded kernel/m labels. Result: genuine
finite free comparison for total Wick output at this polynomial portion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Particle
open MvPolynomial Normal Configuration Rise Function Finset Glyph Labels Common Maxwell.Wick
open scoped Topology BigOperators Classical

variable {A V W : Type*} {G : Gauge} {n d : ℕ}
variable {r R a b c B E : ℝ} {i j k : ℕ}
-- V old array; W residual test directions. No shell at endpoint assumed, pull via finite keys and projections.

section
-- lifts all tags injectively, signs only at reads.
def polar (i : A × V) : A × (V ⊕ W) := (i.1,Sum.inl i.2)
def grip (z : A × V) := Finsupp.single (polar (W:=W) z) (1:ℂ)
def ferry (Q : Normal.Symmetric (A × (V ⊕ W))) := scope grip Q

theorem tide (q : Normal.Symmetric (A × (V ⊕ W))) (m : A × (V ⊕ W) → ℂ) (p : Finset A) (P : A → poly V) :
    blend q m (pot p (fun i => rename Sum.inl (P i)))=blend (ferry q) (m ∘ polar) (pot p P) := by
  let M := fun x : V => Finsupp.single (Sum.inl x : V ⊕ W) (1:ℂ)
  have he : pot p (fun i => rename Sum.inl (P i))=exchange (grip (W:=W)) (pot p P) := by
    unfold grip; rw [← Normal.labelled (polar : A × V → A × (V ⊕ W))]
    unfold pot; rw [map_prod]; refine prod_congr rfl fun i _ => ?_
    unfold post; simp only [rename_rename]; rfl
  rw [he,wets]; rw [show reads grip m=m ∘ polar by ext i; simp [grip,reads,Finsupp.linearCombination_single]]; rfl
end

-- current joint pulled covariance and reference tag. B bounds ambient W nodes, both Q and F.

private lemma bracket {A : Type*} (R : poly V) : totalDegree R ≤ totalDegree (rename (Sum.inl : V → V ⊕ A) R) := by
  let M : V ⊕ A → V →₀ ℂ := Sum.elim (fun i => Finsupp.single i 1) (fun _ => 0)
  have hf : (exchange M).comp (rename (Sum.inl : V→ V ⊕ A))= AlgHom.id ℂ (poly V) := by ext1 i; simp [M]
  exact le_trans (show totalDegree R = totalDegree (exchange M (rename Sum.inl R)) from congr_arg MvPolynomial.totalDegree (DFunLike.congr_fun hf R).symm).le (Rise.ascent ..)

private lemma ceiling (Z : Finset (Fin n)) (Q : Fin n → poly A) (h : ∀ i,totalDegree (Q i)≤k) : totalDegree (pot Z Q) ≤ n*k := by
  apply (totalDegree_finsetProd ..).trans; calc
    _ ≤ ∑ _∈Z,k := sum_le_sum fun i _ => (totalDegree_rename_le _ (Q i)).trans (h _)
    _ ≤ _ := by rw [sum_const]; exact Nat.mul_le_mul_right _ (by simpa using card_le_univ Z)

-- output tolerance R. Spine = ℓ¹ of base label. Fall = unused inverse p.
structure Spend (n : ℕ) (k : ℕ) where
  ξ : ℝ
  base : ℝ
  pos : 0 ≤ ξ
  home : 1 ≤ base
  collision : ℝ
  B : ℝ
  cost : ℝ
  enough : (n:ℝ)*ξ*(base+ξ)^n * priced B (n*k) + base^n * (collision*priced B (n*k)) ≤ cost

def cast (M : Fin n → V → (KeyIn G d ⊕ W) →₀ ℂ) (P : Fin n → poly V) (i : Fin n) := Normal.exchange (M i) (P i)

-- undo weighted proof
structure Tolls (X : Spend n k) (M : Fin n → V → (KeyIn G d ⊕ W) →₀ ℂ) (P : Fin n → poly V) (F : Fin n→Label G d) (r a b : ℝ) : Prop where
  radius : 1 ≤ r
  base i : coin (P i)≤a
  words i : totalDegree (P i)≤k
  price i : coin (thawKey (F i)) ≤ X.base
  seats i z : cents (Normal.glyph (M i z)) bear r≤b
  renew : 1 ≤ b
  mark i : trim (cast M P i) bear d = rename Sum.inl (thawKey (F i))
  upper : a*b^k ≤ X.ξ*r^(d+1)

variable {X : Spend n k} {M : Fin n → V → (KeyIn G d ⊕ W) →₀ ℂ} {P : Fin n → poly V} {F : Fin n→Label G d}
variable (T : Tolls X M P F r a b)
include T
lemma paid (i : Fin n) : coin (cast M P i-rename Sum.inl (thawKey (F i))) ≤ X.ξ := by
  apply le_of_mul_le_mul_right (a:=r^(d+1)) _ (pow_pos (zero_lt_one.trans_le T.radius) _)
  rw [← T.mark i]; apply (Rise.ridge _ _ _ T.radius).trans
  exact (Rise.rise _ _ (zero_le_one.trans T.radius) T.renew (T.seats i) (P i) (T.words _)).trans ((mul_le_mul_of_nonneg_right (T.base i) (pow_nonneg (zero_le_one.trans T.renew) _)).trans T.upper)

private lemma decks (i : Fin n) : coin (rename (Sum.inl : _ → KeyIn G d ⊕ W) (thawKey (F i))) ≤ X.base := by
  rw [labelled]
  have hx:= Rise.rise (fun z => Finsupp.single (Sum.inl z:KeyIn G d⊕W) (1:ℂ)) 0 zero_le_one (c:=1) le_rfl (by simp) (thawKey (F i)) le_rfl
  simp only [one_pow,mul_one] at hx; exact hx.trans (T.price i)

-- compare products AFTER drawing on paid bounds. Includes switch and output at same weights.
private lemma vertices (D : Finset (Fin n)) :
    coin (pot D (cast M P)-pot D (fun i => rename Sum.inl (thawKey (F i)))) ≤ D.card*X.ξ*(X.base+X.ξ)^D.card := by
  let Y := fun i => rename (Sum.inl : _ → KeyIn G d ⊕ W) (thawKey (F i))
  let H := cast M P
  have hb : 0<X.base := zero_lt_one.trans_le X.home
  have hF := X.pos
  let v := X.base+X.ξ
  have hv : 1 ≤ v := X.home.trans (le_add_of_nonneg_right hF)
  have hz : 0 < v := zero_lt_one.trans_le hv
  have he i : coin (post i (Y i))≤v := (Rise.port ..).trans ((decks T i).trans (le_add_of_nonneg_right hF))
  have hX i : coin (post i (H i)) ≤ v := by
    have hh : H i=Y i+(H i-Y i) := by abel
    apply (Rise.port i _).trans; conv_lhs => rw [hh]
    exact (Rise.taller _ zero_le_one _ _).trans (add_le_add (decks T i) (paid T i))
  induction D using Finset.induction_on with
  | empty => simp [pot,coin]
  | @insert i D hi IH =>
    change coin (pot _ H-pot _ Y) ≤ _*v^_
    unfold pot; rw [prod_insert hi,prod_insert hi, card_insert_of_notMem hi]; push_cast
    have hh (p q f g : poly (Fin n × (KeyIn G d ⊕ W))) : p*f-q*g=(p-q)*g+p*(f-g) := by ring
    rw [hh]; apply (Rise.taller _ zero_le_one _ _).trans
    have hq : coin (pot D Y) ≤ v^D.card := by
      apply (purchased _ zero_le_one ..).trans; refine (Finset.prod_le_prod (fun i _ => Rise.sign _ (post i _) zero_le_one) (fun i _ => he i)).trans ?_; simp
    rw [← map_sub]
    apply (add_le_add (le_trans (funds _ zero_le_one ..) (mul_le_mul ((Rise.port ..).trans (paid T i)) hq
      (Rise.sign _ (pot D Y) zero_le_one) X.pos)) ((funds _ zero_le_one ..).trans (mul_le_mul (hX i) IH (Rise.sign _ (pot D H-pot D Y) zero_le_one) hz.le))).trans
    change X.ξ * v^D.card + v * (D.card*X.ξ*v^D.card) ≤ _
    have hg := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv (Nat.le_succ D.card)) X.pos
    rw [pow_succ] at hg ⊢; linarith only [hg]

variable {x : Points n} (hx : x ∈ conf n) (p : Finset (Fin n))
variable (Q : Normal.Symmetric (Fin n × (KeyIn G d ⊕ W))) (μ : Fin n × (KeyIn G d ⊕ W) → ℂ)

theorem accuracy (Tset : modes (Fin n)) (Q₀ : Normal.Symmetric (Fin n × V)) (m : Fin n × V → ℂ)
    (hp : Q₀=Normal.scope (perSlot M) Q) (hμ : m=Normal.reads (perSlot M) μ)
    (h : Sorts Q μ X.B)
    (he : Nearby (ferry Q) (Configuration.currentX hx G d) (μ∘polar) 0 X.B X.collision) :
    ‖blend Q₀ m (pot Tset.val P)- Maxwell.Wick.moment G (Read.portion Tset x) (fun i => Maxwell.observable G d (F ((Read.project Tset) i).val))‖ ≤ X.cost := by
  let Z := Tset.val
  have hZ : Z.card ≤ n := by simpa using card_le_univ Z
  let X' := fun i => thawKey (F i)
  let H := cast M P
  let Y := fun i => rename (Sum.inl : _ → KeyIn G d ⊕ W) (X' i)
  have hz : blend Q₀ m (pot Z P)=blend Q μ (pot Z H) := by
    rw [hp,hμ, ← wets]; apply congr_arg
    unfold pot; rw [map_prod]; exact prod_congr rfl fun i _ => Normal.posts M i (P i)
  have hc i : totalDegree (H i)≤k := (ascent ..).trans (T.words i)
  have hy i : totalDegree (Y i)≤k := by unfold Y X'; rw [← T.mark i]; exact (below_degree ..).trans (hc i)
  have hC i : totalDegree (X' i) ≤ k := le_trans (bracket ..) (hy i)
  rw [hz, Configuration.G_subset hx]; refine (norm_sub_le_norm_sub_add_norm_sub _ (blend Q μ (pot Z Y)) _).trans ?_
  have hh := zero_lt_one.trans_le he.small.paid; have hD : 0≤ Common.priced X.B (n*k) := by dsimp only [Common.priced]; positivity
  apply le_trans _ X.enough; apply add_le_add
  · rw [← map_sub]; apply (Common.width (pot Z H-pot Z Y) (n*k) h ?_).trans
    · apply mul_le_mul_of_nonneg_right _ hD
      have hp : 1 ≤ X.base+X.ξ := X.home.trans (le_add_of_nonneg_right X.pos)
      exact (vertices T Z).trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hZ) X.pos)
        (pow_le_pow_right₀ hp hZ) (pow_nonneg (zero_le_one.trans hp) _) (mul_nonneg (Nat.cast_nonneg _) X.pos))
    rw [sub_eq_add_neg,show -(pot Z Y)=(-1:ℂ) • (pot Z Y) by simp]; exact (totalDegree_add (pot Z H) _).trans (max_le (ceiling Z H hc) ((totalDegree_smul_le (-1:ℂ) (pot Z Y)).trans (ceiling Z Y hy)))
  · change ‖blend Q μ _-_‖ ≤ _
    rw [show blend Q μ (pot Z Y)=_ from tide Q μ Z X']
    refine (Common.differs (pot Z X') (n*k) he (ceiling Z _ hC)).trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg he.pos hD))
    refine (Rise.purchased _ zero_le_one ..).trans ?_
    have hh := prod_le_prod (s:=Z) (fun i _ => Rise.sign _ (post i (X' i)) zero_le_one) (fun i _ => (Rise.port i (X' i)).trans (T.price i))
    rw [prod_const] at hh; exact hh.trans (pow_le_pow_right₀ X.home hZ)
end YM.Next.Rank.Particle
