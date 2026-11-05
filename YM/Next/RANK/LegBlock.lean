import YM.Next.RANK.Finite
import YM.Next.RANK.GaussLeg
import YM.Next.RANK.GaussTags



/-!
# Taylor batch endpoint port on FINITE keys

Restrict to keys of generation ≤ d before embedding. Free moment uses real
curl kernel on separated coordinates already on C; no basis choices at infinity.
Prove representation of Maxwell.profile by these ambient radial coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Configuration
open Normal Lattice MvPolynomial Function Labels Finset Maxwell  Glyph
open scoped Topology BigOperators Classical

variable {G : Gauge} {Z : Type*} {n d : ℕ}

-- Constrained potentials. Restriction to polynomial jets with degree bound.

abbrev KeyIn (G : Gauge) (d : ℕ) := {i : Key G // generation i≤d}
noncomputable instance (G : Gauge) (d : ℕ) : Fintype (KeyIn G d) := by
  let Z := (i : Fin (d+1)) × Fin (Labels.dim G i.val)
  let p (i : KeyIn G d) : Z := ⟨⟨i.val.1,by have h:= i.property; unfold generation at h; omega⟩,i.val.2⟩
  let w : Z → Key G := fun i => ⟨i.1,i.2⟩
  exact Fintype.ofInjective p fun i j h => Subtype.ext (congr_arg w h)

def boundKey (G : Gauge) (d : ℕ) : poly (Key G) →ₐ[ℂ] poly (KeyIn G d) :=
    aeval fun i => if h : generation i≤d then MvPolynomial.X (⟨i,h⟩ : KeyIn G d) else 0

def thawKey (p : Label G d) := boundKey G d p.val
lemma eases (p : Label G d) {i : Key G →₀ ℕ} (hi : i∈p.val.support) {z : Key G} (hz : z∈i.support) : generation z≤d := by
  have hp : height i ≤ d := ((MvPolynomial.mem_restrictSupport_iff ℂ).mp (show p.val ∈ limited G d from p.property.1)) hi
  have ht : 1 ≤ i z := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
  apply le_trans ?_ hp; unfold Labels.height
  rw [Finsupp.weight_apply,Finsupp.sum]; refine le_trans ?_ (single_le_sum (f:=fun v => i v • generation v) (fun k _ => Nat.zero_le _) hz)
  exact Nat.le_mul_of_pos_left (generation z) ht
lemma returns (p : Label G d) : rename (Subtype.val : KeyIn G d → Key G) (thawKey p)=p.val := by
  let f := (Subtype.val : KeyIn G d → Key G)
  let F := (rename f).comp (boundKey G d)
  have he m (hm : m∈p.val.support) : F (monomial m (coeff m p.val)) = monomial m (coeff m p.val) := by
    rw [monomial_eq,map_mul,show F (C _)=C _ from F.commutes _]; congr 1
    rw [Finsupp.prod,map_prod]; apply prod_congr rfl
    intro i hi; rw [map_pow]; congr 1
    unfold F boundKey; rw [AlgHom.comp_apply,aeval_X,dif_pos (eases p hm hi),rename_X]
  change F p.val=p.val
  suffices h : F p.val=∑ i∈p.val.support, monomial i (coeff i p.val) by rw [h,support_sum_monomial_coeff]
  nth_rw 1 [p.val.as_sum]; rw [map_sum]; exact sum_congr rfl he

-- actual transformation to Maxwell Leg coordinates. even 0 positions summed exactly.

def mapper (z : KeyIn G d) : Maxwell.Slot G →₀ ℂ := ∑ j : Fin (legDim G z.val.1),
    ((((Labels.axes G z.val.1).repr (Maxwell.gaugeJet (Maxwell.frame G z.val.1 j)) z.val.2 : ℝ) : ℂ)) •
      Finsupp.single (⟨z.val.1,j⟩ : Slot G) (1:ℂ)
lemma gathered (p : Labels.Label G d) : Normal.exchange (mapper (d:=d) (G:=G)) (thawKey p)=observable G d p := by
  have ht : Normal.exchange (mapper (d:=d) (G:=G))=(reduceEq (G:=G)).comp (rename (Subtype.val : KeyIn G d → Key G)) := by
    ext1 i
    rw [Normal.exchange_x,mapper,map_sum, AlgHom.comp_apply,rename_X, Maxwell.reduceEq,aeval_X]; simp only [Normal.glyph, map_smul,Finsupp.linearCombination_single,one_smul,C_mul']
  rw [ht, AlgHom.comp_apply,returns]; rfl

def bear (x : KeyIn G d ⊕ Z) := Sum.elim (fun k : KeyIn G d => generation k.val) (fun _ => d+1) x

-- full covariance for low keys (before adding residual directions; cross derivatives in Cone frame).

def currentX {x : Points n} (hx : x∈ conf _) (G : Gauge) (d : ℕ) : Normal.Symmetric (Fin n × KeyIn G d) :=
    Normal.scope (perSlot fun _ => mapper) (Normal.frameX hx)

-- attention: restrict to any subset BEFORE projecting.

lemma G_moment {x : Points n} (hp : x∈conf _) (p : Fin n → Labels.Label G d) :
    Wick.moment G x (fun i => observable G d (p i))=blend (currentX hp G d) 0 (pot univ (fun i => thawKey (p i))) := by
  let M := perSlot (fun _ : Fin n => mapper (G:=G) (d:=d))
  rw [Wick_reads hp]; simp_rw [← gathered]
  have hx : (∏ i, rename (fun y => (i,y)) (Normal.exchange mapper (thawKey (p i))))=Normal.exchange M (pot univ (fun i => thawKey (p i))) := by
    rw [pot,map_prod]; exact Finset.prod_congr rfl fun i _ => (posts (fun _ : Fin n => mapper (d:=d) (G:=G)) i (thawKey (p i))).symm
  rw [hx,wets, show (reads M 0) = 0 from funext fun i => Finsupp.linearCombination_zero_apply ..]; rfl

-- same G across subset (place i)

lemma G_subset {x : Points n} (hp : x∈conf _) (p : Fin n → Labels.Label G d) (T : modes (Fin n)) :
    Wick.moment G (Read.portion T x) (fun i => observable G d (p ((Read.project T) i).val))=
      blend (currentX hp G d) 0 (pot T.val (fun i => thawKey (p i))) := by
  let e := Read.project T
  let f := fun i => (e i).val
  let U := fun i => thawKey (p i)
  let M : Fin T.val.card × KeyIn G d → (Fin n × KeyIn G d) := fun j => (f j.1,j.2)
  let R : Fin T.val.card × Maxwell.Slot G → Fin n × Maxwell.Slot G := fun i => (f i.1,i.2)
  let P := fun l : ℕ => Normal.perSlot (fun _ : Fin l => mapper (G:=G) (d:=d))
  let q : Normal.Symmetric (Fin n × Maxwell.Slot G) := frameX hp
  have ht : pot T.val U= rename M (pot univ (fun i => U (f i))) := by
    have hv (i : Fin T.val.card) : rename M (post i (U (f i)))=post (f i) (U (f i)) := MvPolynomial.rename_rename ..
    unfold pot; rw [← Finset.prod_attach,map_prod]; symm
    exact Fintype.prod_equiv e _ (fun i => post i.val (U i.val)) hv
  rw [G_moment (Read.portion_free T x hp), show pot T.val _ = rename M _ from ht,labelled M,wets]
  dsimp only [currentX]
  let w : Points T.val.card := Read.portion T x
  let H := fun i => Finsupp.single (M i) (1:ℂ)
  let B := fun i => Finsupp.single (R i) (1:ℂ)
  have he : frameX (G:=G) (Read.portion_free T x hp) = Normal.scope B q := by
    apply Normal.Symmetric.ext; funext i j
    rw [match_name R]
    change (if _ = _ then 0 else _)=(if f _=f _ then 0 else _)
    simp only [(show Injective f from Subtype.val_injective.comp e.injective).eq_iff]; rfl
  have ha : (fun i => Finsupp.linearCombination ℂ B (P T.val.card i))=fun i => Finsupp.linearCombination ℂ (P n) (H i) := by
    funext i; simp only [H,M,P,Finsupp.linearCombination_single,one_smul]
    unfold Normal.perSlot
    rw [Finsupp.linearCombination_mapDomain]
    -- rename per slot
    have hf (z : (Slot G →₀ ℂ)) : Finsupp.linearCombination ℂ (B ∘ (fun x => (i.1,x))) z = Finsupp.mapDomain (fun x => (f i.1,x)) z := by
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add a b h1 h2 => rw [map_add,Finsupp.mapDomain_add,h1,h2]
      | single a c => rw [Finsupp.linearCombination_single, Finsupp.mapDomain_single]
                      simp [Function.comp_apply,B,R]
    exact hf _
  change blend (Normal.scope (P T.val.card) _) 0 _=blend (Normal.scope H (Normal.scope (P n) q)) (reads H 0) _
  rw [he,← scopes,ha, scopes, show (reads H 0) = (0 : Fin T.val.card × KeyIn G d → ℂ) from funext fun i => Finsupp.linearCombination_zero_apply ..]
end YM.Next.Rank.Configuration
