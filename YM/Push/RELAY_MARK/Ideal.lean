import YM.Push.RELAY_MARK.Pi

/-!
# Generation of the equation ideal

Exactly the `Maxwell.equationIdeal` subspace of Section  normalized
on radial jets. Factorize each homogeneous component into terms with a
*literal equation factor*. This decomposition is on polynomials, not
requiring individual factors invariant (invariant lifts will be made later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace Pointwise
variable {G : Gauge} {d n : ℕ}

section

abbrev Ink (G : Gauge) := (j : ℕ) × AtomAt G j

def badge (i : Ink G) : ℕ × ℕ := (i.1+2,1)
def verse (a : List (Ink G)) : Pol G := (a.map (fun j=> literal j.2)).prod
def syntaxRank (a : List (Ink G)) := (a.map badge).sum
lemma rank_verse (a : List (Ink G)) : verse a∈sector (syntaxRank a) := by
  induction a with
  | nil => simp only [verse,syntaxRank, List.map_nil,List.prod_nil,List.sum_nil]; exact MvPolynomial.isWeightedHomogeneous_one ℂ bidegree
  | cons b a ih => simp only [verse,syntaxRank, List.map_cons,List.prod_cons,List.sum_cons]; exact sector_mul (literal_tier b.2) ih

private lemma scripted (m : Key G →₀ ℕ) : ∃ a : List (Ink G), verse a=MvPolynomial.monomial m 1 ∧ syntaxRank a=weight m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => exact ⟨[],by simp [verse],by simp [syntaxRank,weight]⟩
  | add v w hv hw =>
    obtain ⟨a,ha,he⟩ := hv; obtain ⟨b,hb,hf⟩ := hw
    exact ⟨a++b,by rw [show verse (a++b)=verse a*verse b by simp [verse],ha,hb,MvPolynomial.monomial_mul,mul_one],
      by rw [weight_plus,← he,← hf]; simp [syntaxRank]⟩
  | single a b =>
    exact ⟨List.replicate b ⟨a.1,(axes G a.1).coord a.2⟩,by
      rw [← MvPolynomial.X_pow_eq_monomial]; simp [verse, ← literal_x],by simp [syntaxRank,weight,badge,Finsupp.weight_single,bidegree,generation]⟩

def Gap (x : Ink G) := ∀ y ∈ LinearMap.range Maxwell.gaugeJet,x.2 y=0

def multiplied (G : Gauge) (m : ℕ × ℕ) := Submodule.span ℂ {p : Pol G |
    ∃ x : Ink G, Gap x ∧ ∃ b : List (Ink G), m=badge x+syntaxRank b ∧ p=literal x.2 * verse b}

lemma multiplied_add {f : Pol G} {m : ℕ × ℕ} (h : f∈multiplied G m) (x : Ink G) : literal x.2 * f∈ multiplied G (badge x+m) := by
  refine Submodule.span_induction (s:=_) (p:=fun f _ => literal x.2*f∈_) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨y,hY,b,hb,rfl⟩; rw [hb]
    refine Submodule.subset_span ⟨y,hY,x::b,?_,?_⟩
    · simp only [syntaxRank,List.map_cons,List.sum_cons]; abel
    simp only [verse,List.map_cons,List.prod_cons]; ring
  · simp
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  intro a b _ hb; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb

def eraseShell (G : Gauge) (j : ℕ) := let f := Maxwell.gaugeJet (G:=G) (j:=j); f ∘ₗ f.leftInverse
lemma erase_shell (p : Label G d) : p∈Maxwell.equationIdeal G d ↔ changed (eraseShell G) p.val=0 := by
  rw [Maxwell.ideal_meaning]
  constructor
  · intro h; refine eval_ext _ _ (fun A=>?_)
    rw [eval_changed,map_zero]; exact h (fun j=> (Maxwell.gaugeJet (G:=G) (j:=j)).leftInverse (A j))
  intro h A
  let J : Jet G := fun i=> Maxwell.gaugeJet (A i)
  have hi : changedJet (eraseShell G) J=J := funext (fun j=> congr_arg Maxwell.gaugeJet
    (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Maxwell.leg_injective (G:=G) (j:=j))) (A j)))
  change read J p.val=_
  rw [← hi,← eval_changed,h,map_zero]

lemma split_literal (x : Ink G) : ∃ y z : Ink G, badge y=badge x ∧ badge z=badge x ∧ Gap y ∧
    literal x.2-changed (eraseShell G) (literal x.2)=literal y.2 ∧ changed (eraseShell G) (literal x.2)=literal z.2 := by
  let q : AtomAt G x.1 := x.2 ∘ₗ eraseShell G x.1
  refine ⟨⟨x.1,x.2-q⟩,⟨x.1,q⟩,rfl,rfl, ?_,?_,?_⟩
  · rintro j ⟨v,hv⟩; subst j
    change (x.2-q) (Maxwell.gaugeJet v)=0
    simp [q,eraseShell,LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Maxwell.leg_injective (G:=G) (j:=x.1)))]
  · refine eval_ext _ _ (fun J=>?_); rw [map_sub,eval_changed,read_literal,read_literal,read_literal]
    simp only [changedJet]; simp [q]
  refine eval_ext _ _ (fun J=>?_); rw [eval_changed,read_literal,read_literal]; rfl

lemma split_verse (a : List (Ink G)) : verse a-changed (eraseShell G) (verse a)∈multiplied G (syntaxRank a) := by
  induction a with
  | nil => simp [verse]
  | cons b l ih=>
    obtain ⟨q,p,hq,hp,H,he,H'⟩ := split_literal b
    rw [show verse (b::l)=literal b.2 * verse l by simp [verse],map_mul,
      show syntaxRank (b::l)=badge b+syntaxRank l by simp [syntaxRank]]
    rw [H'] at he ⊢
    have hv : literal b.2=literal p.2+literal q.2 := by rw [← he]; abel
    rw [hv, show (literal p.2+literal q.2)*verse l - _ = literal q.2*verse l+literal p.2*(verse l-changed (eraseShell G) (verse l)) by ring]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨q,H,l,by rw [hq],rfl⟩) (hp ▸ multiplied_add ih p)

lemma generation_ready (p : Label G d) (h : p∈Maxwell.equationIdeal G d) (m : ℕ × ℕ) (hp : p∈Grade m) : p.val∈multiplied G m := by
  classical
  let a := p.val
  change a∈_
  have ht : a-changed (eraseShell G) a=a := by rw [(erase_shell p).1 h,sub_zero]
  rw [← ht]
  -- Use expansion once, coefficients frozen
  let l := a.support
  let f (b : Key G →₀ ℕ) := (MvPolynomial.monomial b (1:ℂ))
  let y (b) := MvPolynomial.coeff b a
  have hx : a-changed (eraseShell G) a = ∑ b∈l,y b • (f b-changed (eraseShell G) (f b)) := calc
    _ = (∑ b∈l,y b • f b)-changed (eraseShell G) (∑ b∈l,y b • f b) := by
      have he : (∑ b∈l,y b • f b)=a := by
        unfold f; simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]; exact a.support_sum_monomial_coeff
      rw [he]
    _ = _ := by simp only [map_sum, map_smul, smul_sub,Finset.sum_sub_distrib]
  rw [hx]; refine Submodule.sum_mem _ fun i hi=> Submodule.smul_mem _ _ ?_
  have hv : weight i=m := (pure_grade m p).mp hp (MvPolynomial.mem_support_iff.mp hi)
  obtain ⟨v,hv',he⟩ := scripted i
  rw [← hv,← he,show f i=verse v from hv'.symm]; exact split_verse v

lemma clip_sectors (p : Label G d) (h : p∈Maxwell.equationIdeal G d) (m : ℕ × ℕ) : gradePart m p∈Maxwell.equationIdeal G d := by
  apply (erase_shell _).mpr
  change changed (eraseShell G) (piece m p.val) = 0
  rw [component_change, (erase_shell p).1 h, map_zero]

lemma no_unit (p : Label G d) (h : p∈Maxwell.equationIdeal G d) (i : ℕ) (hv : p∈Grade (i,0)) : p=0 := by
  obtain ⟨c,hc⟩ := scalar_grade i hv
  have he := (Maxwell.ideal_meaning (A:=p)).1 h (fun _=>0)
  rw [hc] at *; have hl : c * (1:ℂ)=0 := by
    simpa only [Submodule.coe_smul_of_tower,map_smul,unit,map_one,smul_eq_mul] using he
  rw [mul_one] at hl; simp [hl]
end
end YM.Push.Mark
