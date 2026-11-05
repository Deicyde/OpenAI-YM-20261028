import YM.Next.SCHEDULE.SlotPay

/-!
# One atom all repeats/fixed order

Cost reference PRE L. Invokes path bound of the actual input shape (if
verified). Simultaneous sup test through the stage order, genuine left
ordered derivatives in any directions from the resulting anchor. With
this support-length polynomial tested we can move to a shorter width,
not needing any j-dependent growth threshold from post-L for these
factors. Subsequent interacting or integral-estimate costs are
not this lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Wages
open Work.G07 Lattice RG Wilson Finset
open scoped Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side} {k : ℕ}

private lemma constPay {D : Directions G n → Prop} {Z : Config G n → Prop} (f : ℝ) (k : ℕ) :
    LeftBound k D Z 1 |f| (fun _ => f) := LeftBound.const zero_le_one _

private lemma pairs {D : Directions G n → Prop} {Z : Config G n → Prop} (k : ℕ) {m : ℕ} (q : Finset (Fin m))
    {x : Fin m → Config G n → ℝ} {f : ℝ} (h : ∀ i, LeftBound k D Z 1 f (x i)) :
    LeftBound k D Z 1 ((2^k*f)^q.card) (fun U => ∏ i∈q,x i U) := by
  induction q using Finset.induction_on with
  | empty => simpa using constPay (D:=D) (Z:=Z) 1 k
  | @insert i v hi ih =>
    have he := (h i).mul ih (by norm_num)
    rw [card_insert_of_notMem hi, pow_succ']; simp_rw [prod_insert hi]; exact he

private lemma lanes {D : Directions G n → Prop} {Z : Config G n → Prop} (k : ℕ) {ι : Type*} [DecidableEq ι]
    (q : Finset ι) (x : ι → Config G n → ℝ) (f : ι → ℝ) (h : ∀ i, LeftBound k D Z 1 (f i) (x i)) :
    LeftBound k D Z 1 (∑ i∈q, f i) (fun U => ∑ i∈q,x i U) := by
  induction q using Finset.induction_on with
  | empty => simpa using constPay (D:=D) (Z:=Z) 0 k
  | @insert i v hi ih =>
    have he := (h i).add ih; simpa [hi,Finset.sum_insert] using he

theorem extracts {f : Config G n → G.Color} {D Z c} (h : LeftBound k D Z 1 c f) (i : G.ColorIndex) :
    LeftBound k D Z 1 c fun U => f U i := by
  let L := (EuclideanSpace.proj i : G.Color →L[ℝ] ℝ)
  refine ⟨h.smooth.postcomp L,h.nonneg,fun l hl hd U hU => ?_⟩
  have ht : leftDerivs (fun U => f U i) l U=(leftDerivs f l U) i := congr_fun (left_linear h.smooth L hl) U
  rw [ht]; refine le_trans ?_ (h.bound l hl hd U hU)
  let X:=leftDerivs f l U
  have hh := abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) X
  rw [OrthonormalBasis.norm_eq_one, one_mul,EuclideanSpace.basisFun_inner] at hh; exact hh

def price (b : BudgetPoint) (a : Atom G k) :=
    let v:=slotCost G b.power b.order a.length; let c : ℝ:=2^b.order
    a.magnitude*c*((c*v*b.threshold)^k)

theorem fin (b : BudgetPoint) (a : Atom G k) (o : Site n) :
    LeftBound b.order (b.dirBound o) (Healthy b.threshold (a.footprint o)) 1 (price b a) fun U => a.unmasked U o := by
  let d:=(slotCost G b.power b.order a.length)
  let c:= (2^b.order : ℝ)
  have hs i : LeftBound (G:=G) b.order (b.dirBound o) (Healthy b.threshold (a.footprint o)) 1 (d*b.threshold) fun U => (a.leg i).atSite U o := by
    have hx : (a.leg i).length ≤ a.length := Finset.single_le_sum (f:=fun i => (a.leg i).length) (fun _ _=>Nat.zero_le _) (mem_univ i)
    refine slotPays (a.leg i) a.stencil ?_ a.length hx o b
    exact fun x hh => mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ i,hh⟩)
  let u := fun i (U : Config G n) => a.coeff i*∏ j,(a.leg j).atSite U o (i j)
  let z := fun i => |a.coeff i| *c*(c*d*b.threshold)^k
  have hi i : LeftBound b.order (b.dirBound o) (Healthy b.threshold (a.footprint o)) 1 (z i) (u i) := by
    have he := (constPay (a.coeff i) b.order).mul (pairs b.order univ fun j => extracts (hs j) (i j)) zero_le_one
    rw [card_univ,Fintype.card_fin] at he
    dsimp only [z,u]; rw [mul_comm _ c,mul_assoc c d]; exact he
  have he : ∑ i,z i=price b a := by unfold z; simp only [← sum_mul]; rfl
  rw [← he]; exact lanes b.order univ u z hi

lemma total (b : BudgetPoint) (a : Atom G k) (o : Site n) : b.supBounds o (a.footprint o) (fun U => a.unmasked U o) (price b a) := by
  have h:= fin b a o; exact ⟨h.nonneg,fun U hU l hl hD => by simpa using h.bound _ hl hD U hU⟩

/-- Express c*threshold^k*magnitude*(1+length)^degree exactly with PURE
constant c. -/
def startup (G : Gauge) (k P i : ℕ) : ℝ := 2^i*(2^i*slotCost G P i 0)^k

def grade (k P i : ℕ) := ((P+1)*i)*k

private lemma slotCost_shape (G : Gauge) (k P l : ℕ) :
    slotCost G P k l = slotCost G P k 0 *((l:ℝ)+1)^((P+1)*k) := by simp only [slotCost,margin]; simp [mul_pow,pow_mul,mul_assoc]

lemma scan (b : BudgetPoint) (a : Atom G k) : price b a=startup G k b.power b.order * b.threshold^k *
    a.magnitude *((a.length:ℝ)+1)^grade k b.power b.order := by
  unfold price startup grade
  simp only
  rw [slotCost_shape G b.order b.power a.length, pow_mul (n:=k)]; simp only [mul_pow]; ring
end YM.Next.Scheduling.Wages
