import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das


/-!
# Jet costs of relative projected determinant

 No Ξ† diagonal-only quotient. Buy full polynomial in rank of *projection*,
 not `det C` on CPU/exponent volume. Even spinning along F.Bind.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ}

private lemma lupine (i : ℕ) (s : Finset ι) (f : ι→E→ℝ) (p : ∀ u∈s, Bud i 1 (f u) x) : Bud i s.card (fun y=>∏ u∈s,f u y) x := by
  induction s using Finset.induction_on with
  | empty=> simp only [prod_empty]; exact ⟨contDiffAt_const,fun i _ hi=>by rw [card_empty] at hi; omega⟩
  | insert j s hj h=> simp_rw [prod_insert hj,card_insert_of_notMem hj,Nat.add_comm s.card]; exact
                       (p _ (mem_insert_self ..)).shoot (h fun i hi=> p _ (mem_insert_of_mem hi))

variable [Fintype ι] [DecidableEq ι] {A : E→ Matrix ι ι ℝ} {v w : ℝ}
lemma combs (M : Matrix ι ι ℝ) : (M+1).det = ∑ i : Finset ι, (Pond.circuit i M).det := by
  have he:= Matrix.detRowAlternating (R:=ℝ) (n:=ι) |>.map_add_univ (fun i=> M i) (fun i=> (1:Matrix ι ι ℝ) i)
  refine he.trans ?_
  refine sum_congr rfl (fun i _=>?_); exact Matrix.det_piecewise_one_eq_submatrix_det M i

private lemma signed_pay (p : Equiv.Perm ι) (Q : E→ℝ) (h : Brush j v w Q x) : Brush j v w (fun x=> Equiv.Perm.sign p • Q x) x := by
  let c:= Equiv.Perm.sign p
  rcases Int.units_eq_one_or c with hc|hc
  · simp_rw [show Equiv.Perm.sign p=1 from hc,one_smul]; exact h
  · simp_rw [show Equiv.Perm.sign p= -1 from hc]; change Brush _ _ _ (fun x=> (-1:ℤ) • Q x) x; simpa using! h.opposite

omit [Fintype ι] in
private lemma costly_prices (A : E→ Matrix ι ι ℝ) (s : Finset ι) (i j : ℕ) (hi : s.card ≤ i) (hv:0≤v)
    (h : ∀ i j', Brush j v 1 (fun x=> A x i j') x) : Brush j (((i.factorial:ℕ):ℝ)*(1+v)^i) i (fun i=> (circuit s (A i)).det) x := by
  let f (p:E) := Pond.circuit s (A p)
  simp_rw [Matrix.det_apply]; refine (Brush.spree _ _ (fun _=> (1+v)^i) (Nat.cast_nonneg i) (fun p _ =>?_)).climb ?_ le_rfl
  ·
    have ht:= Brush.all_prod univ (fun j:↥s=>fun x' => f x' (p j) j) _ _ (fun j _=> h _ _)
    simp only [prod_const,sum_const, card_univ,Fintype.card_coe, nsmul_eq_mul,mul_one] at ht
    exact (signed_pay p _ ht).climb (calc
      v^s.card ≤ (1+v)^s.card := by gcongr; linarith
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hv) hi) (by exact_mod_cast hi)
  rw [sum_const,nsmul_eq_mul,card_univ, Fintype.card_perm,Fintype.card_coe]; gcongr

omit [Fintype ι] in
private lemma dear (A : E→ Matrix ι ι ℝ) (s : Finset ι) (hp : j<s.card) (_hv : 0≤v) (he : A x=0)
    (h : ∀ i j', Brush j v 1 (fun x=> A x i j') x) : Brush j 0 j (fun i=> (circuit s (A i)).det) x := by
  simp_rw [Matrix.det_apply]; apply (Brush.spree _ _ (fun _=>0) (Nat.cast_nonneg j) (fun p (_:p∈univ)=>?_)).climb (by simp) le_rfl
  let f(p':↥s)(x':E):= circuit s (A x') (p p') p'; refine signed_pay p _ ?_
  have hv : Bud j s.card (fun x' => ∏ i:↥s,f i x') x := by
    rw [← Fintype.card_coe s,← Finset.card_univ]; apply lupine
    intro i _; refine ⟨(h (p i).val i.val).smooth,?_⟩
    intro k hk hi; obtain rfl : k=0 := by omega
    rw [normJ,norm_iteratedFDeriv_zero]; simp [f,Pond.circuit,he]
  exact ⟨hv.1,Nat.cast_nonneg _,fun i hi=> by rw [zero_mul]; exact (hv.2 i hi (hi.trans_lt hp)).le⟩

lemma jewels (h : ∀ i j', Brush j v 1 (fun x=> A x i j') x) (he : A x=0) (hv : 0 ≤ v) :
    let B := j.factorial*(1+v)^j
    Brush j ((↑(j+1:ℕ):ℝ)*(1+Fintype.card ι)^j*B) j (fun x=> (A x+1).det) x := by
  intro B; let f (i : Finset ι) := if i.card ≤ j then B else 0; let X := univ.filter (fun i : Finset ι=> i.card ≤ j)
  simp_rw [combs]
  have h (i : Finset ι) : Brush j (f i) j (fun k=>(circuit i (A k)).det) x := by
    unfold f; split
    next hp=> exact costly_prices A i j j hp hv h
    next hp=> exact dear A i (lt_of_not_ge hp) hv he h
  refine (Brush.spree _ _ _ (Nat.cast_nonneg _) (fun i (_:i∈univ)=> h i)).climb ?_ le_rfl
  unfold f; rw [← sum_filter,sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (show 0≤B by unfold B; positivity)
  have hx: X.card≤ (j+1)*(1+Fintype.card ι)^j := by
    let f (i:ℕ):=(univ:Finset ι).powersetCard i
    have hg : X⊆ (Finset.range (j+1)).biUnion f := fun i hi=> mem_biUnion.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le
      (mem_filter.mp hi).2),mem_powersetCard.mpr ⟨subset_univ _,rfl⟩⟩
    refine ((card_le_card hg).trans card_biUnion_le).trans ((sum_le_sum (s:=Finset.range (j+1)) (f:=fun i=> (f i).card) (g:=fun _=> (1+Fintype.card ι)^j)
      fun i hi=>?_).trans_eq (by simp))
    rw [mem_range] at hi; unfold f; rw [card_powersetCard,card_univ]; exact (Nat.choose_le_pow ..).trans (by gcongr <;> omega)
  exact_mod_cast hx
end YM.ConnectedActivityE6.Blaze.Flux
