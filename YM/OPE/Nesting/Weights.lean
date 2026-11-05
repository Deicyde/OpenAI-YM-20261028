import YM.OPE.Nesting.NestRates

/-! Successive powers on declared tree scales. The parent of a root in
`ratios` is charged at virtual scale 1, i.e., its "ratio" is just the
request's root length. The rates need not be strict; only the *sum* of the
advances needs to be positive when comparing losses, ensuring enough slack for
all prefactors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
namespace Tree

/-- Nonnegative engineering exponent advance at an admissible request. -/
def step : (t:Tree)→ ℝ→(t.Inner→ℝ)→ (t.Inner→ℝ)
 | bud,_,_,v=>nomatch v
 | fork n f,k,a, Sum.inl ()=> a (Sum.inl ())-k
 | fork n f,k,a, Sum.inr ⟨i,v⟩=>step (f i) (a (Sum.inl ())) (childAge i a) v

/-- Leaf weight charged as a normalization when entering parent cluster. -/
def headSum : (t:Tree)→(t.Leaf→ℝ)→(t.Inner→ℝ)
 | bud,_,v=>nomatch v
 | fork n f,a,Sum.inl ()=> ∑ v:Σ i:Fin n,(f i).Leaf,a v
 | fork n f,a,Sum.inr ⟨i,v⟩ => headSum (f i) (childWages i a) v

def ratios : (t:Tree)→ℝ→(t.Inner→ℝ)→(t.Inner→ℝ)
 | bud,_,_,v=>nomatch v
 | fork n f,p,a, Sum.inl ()=>a (Sum.inl ())/p
 | fork n f,p,a, Sum.inr ⟨i,v⟩=> ratios (f i) (a (Sum.inl ())) (childAge i a) v

variable {n:ℕ}{f:Fin n→Tree}

lemma sum_inner {M:Type}[AddCommMonoid M](u:(fork n f).Inner→M):∑ v,u v = u (Sum.inl ()) + ∑ i:Fin n,∑ j:(f i).Inner,u (Sum.inr ⟨i,j⟩):=by
    change (∑ v:Unit ⊕ Σ i:Fin n,(f i).Inner,u v)=_
    rw [Fintype.sum_sum_type u,Fintype.sum_sigma,Fintype.sum_unique]
lemma prod_inner {M:Type}[CommMonoid M](u:(fork n f).Inner→M): (∏ v,u v) = u (Sum.inl ()) * ∏ i:Fin n,∏ j:(f i).Inner,u (Sum.inr ⟨i,j⟩):=by
    change (∏ v:Unit ⊕ Σ i:Fin n,(f i).Inner,u v)=_
    rw [Fintype.prod_sum_type u,Fintype.prod_sigma,Fintype.prod_unique]
lemma sum_wages_fork {w:(fork n f).Leaf→ℝ}: (∑ i:Fin n,∑ j:(f i).Leaf,w ⟨i,j⟩)=∑ j,w j:= by rw [← Fintype.sum_sigma]; rfl

section
variable (L:Type)
lemma budget_expansion (t:Tree)(w:t.Leaf→ℝ)(k:ℝ)(a:t.Inner→ℝ): t.cost k a w = k*(∑ i,w i) + ∑ v:t.Inner,(t.headSum w v)*(t.step k a v):=by
    induction t generalizing k with
    | bud=>change k*w ()= k * (∑ j:Unit, w j)+∑ j:Empty,_; rw [@Fintype.sum_unique _ Unit,Fintype.sum_empty,add_zero]
    | fork n f ih=>
       let y:=∑ j,w j
       have hpos:(fork n f).headSum w (Sum.inl ())=y:=rfl
       rw [Tree.cost_fork,sum_inner (fun v:(fork n f).Inner=>((fork n f).headSum w v)*((fork n f).step k a v))]
       conv_lhs => enter[2,i]; rw [ih i]
       rw [Finset.sum_add_distrib,← Finset.mul_sum]; dsimp [childWages]; rw [sum_wages_fork]
       rw [hpos]; dsimp [childAge,step,headSum]; change a (Sum.inl ()) * y + _ = k*y + (y* (a (Sum.inl ()) - k)+_); ring

lemma adequate_cost (t:Tree) {k:ℝ}{a:t.Inner→ℝ}(h:t.ordered k a)(v:t.Inner):0≤t.step k a v:=by induction t generalizing k with
 | bud=>cases v
 | fork n f ih=>rcases v with u | ⟨i,t⟩
                · cases u; exact sub_nonneg.mpr h.1
                exact ih i (h.2 i) t
lemma step_sum_bound (t:Tree){k:ℝ}{a:t.Inner→ℝ}(h:t.ordered k a)(v:t.Inner) : a v ≤ k+∑ p:t.Inner,t.step k a p:=by induction t generalizing k with
 | bud=>cases v
 | fork n f ih =>
    obtain u | ⟨i,p⟩:=v
    · cases u; have he:(fork n f).step k a (Sum.inl ()) ≤ ∑p:(fork n f).Inner, Tree.step _ _ _ p:= single_le_sum (fun v _=> adequate_cost _ h v) (mem_univ _)
      change a (Sum.inl ())-k ≤ _ at he; linarith only [he]
    change childAge i a p ≤ _
    refine (ih i (h.2 i) p).trans (?_)
    have he: ∑ p:(f i).Inner,(f i).step (a (Sum.inl ())) (childAge i a) p ≤ ∑ i:Fin n,∑ p:(f i).Inner,((f i).step (a (Sum.inl ())) (childAge i a) p) := single_le_sum (fun j _=>sum_nonneg (s:=Finset.univ) fun t _=>adequate_cost (f j) (h.2 j) t) (mem_univ i)
    rw [sum_inner (fun p:(fork n f).Inner=> step _ _ _ p)]; change _ ≤ k + (a (Sum.inl ()) - k + ∑ i:Fin n,∑ p:(f i).Inner,((f i).step (a (Sum.inl ())) (childAge i a) p))
    linarith only [he]

/-- Bounds at a fork, using root radius stored with the positions,
read at engineering shift m (weight for coefficients, `D+1` for kernel tail). -/
def scaleFee (w:(fork n f).Leaf→ℝ) (s:(fork n f).Inner→ℝ)(eps m:ℝ) :ℝ :=
    (s (Sum.inl ()))^m * ∏ v,(fork n f|>.ratios 1 s v)^(-(fork n f).headSum w v-eps)

variable {L:Type}{t:Tree}{l:Filter L}{T p:L→ℝ}{s:L→t.Inner→ℝ}{a:t.Inner→ℝ}{k:ℝ}
lemma rate_ratios (hp:RateIs l T p (-k))(h:∀ v, RateIs l T (fun i=>s i v) (-a v)) (v:t.Inner) :RateIs l T (fun i=>t.ratios (p i) (s i) v) (-(step t k a v)):=by
     induction t generalizing k p with
     | bud=>cases v
     | fork n f ih => rcases v with u | ⟨j,v⟩
                      · cases u; exact (h _ |>.div hp).swap (by rw [step]; ring)
                      exact ih j (h ..) (fun v=> h _) v

lemma incidence {I:Type}{α:I→ℝ}{F:I→L→ℝ} (hT:Tendsto T l atTop)(V:Finset I)(h:∀ v∈V,RateIs l T (F v) (α v)) : RateIs l T (fun i=>∏ v∈V,F v i) (∑ v∈V,α v):=by
       induction V using Finset.induction with
       | empty=>simpa only [Finset.sum_empty, Finset.prod_empty] using (RateIs.const hT zero_lt_one)
       | @insert b v hb hv => simpa only [sum_insert hb,prod_insert hb] using ((h b (mem_insert_self b v)).mul (hv (fun i hi=> h i (mem_insert_of_mem hi))))

lemma rate_base {s:L→(fork n f).Inner→ℝ}{a:(fork n f).Inner→ℝ}
       (hT:Tendsto T l atTop)(hs:∀ v,RateIs l T (fun i=>s i v) (-a v))(w:(fork n f).Leaf→ℝ)(ε m:ℝ):
    RateIs l T (fun i=>scaleFee w (s i) ε m) (m*(-a (Sum.inl ())) + (fork n f).cost 0 a w + ε*∑ v:(fork n f).Inner,(fork n f).step 0 a v):=by
         have hp(v:(fork n f).Inner):=rate_ratios (p:=fun _=>1) (t:=fork n f) (a:=a) (k:=0) (by simpa using RateIs.const hT one_pos) hs v
         unfold scaleFee
         have h':= (hs (Sum.inl ())|>.rpow m).mul (incidence hT (Finset.univ: Finset (fork n f).Inner) (fun v _=>(hp v).rpow (-(fork n f).headSum w v-ε)))
         refine h'.swap (?_)
         rw [budget_expansion, zero_mul,zero_add, add_assoc,Finset.mul_sum,← sum_add_distrib]; apply congr_arg (_+·) (Finset.sum_congr rfl (fun v _=>by ring))

/-- RHS using a sum of gains over nonroot internals (may equal zero if
there are none, so no exponential comparator can pay it in general). -/
def nestPrice (s:(fork n f).Inner→ℝ)(D:(fork n f).Inner→ℕ):ℝ :=
      ∑ v:Σ i:Fin n,(f i).Inner, ((fork n f).ratios 1 s (Sum.inr v))^(D (Sum.inr v)+1)
lemma nest_price_add (D:(fork n f).Inner→ℕ) {s:(fork n f).Inner→ℝ} (h:∀ i:(fork n f).Inner,0 < (fork n f).ratios 1 s i) (v:Σ i:Fin n,(f i).Inner): (fork n f|>.ratios 1 s (Sum.inr v))^(D (Sum.inr v)+1) ≤ nestPrice s D:= Finset.single_le_sum (fun t ht=> pow_nonneg (h (Sum.inr t)).le (D (Sum.inr t)+1)) (mem_univ v)
end
end Tree
end YM.OPE.Nesting
