import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Next.WARD_BIN.Printing

/-!
# Precontract prices: Euler basis & all the lower fields we intend to compare

Finite w ≤ d here for the *target* weight d, and finite translations.
Actual simultaneity even across d/schedule gates is a producer obligation.
No pricing against table of downstream test count, max multiplicities or loops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter Wilson Lattice Labels RG Source Source.Drops Bid Work.G07 Ac
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {n : Side} {d l k P : ℕ} {b : BudgetPoint}
  {F : Labels.Frame G d} {H : Hol G} {T : Finset Cover}

def shifts (G : Gauge) (u : Cover) : Form G →ₗ[ℂ] Form G where
  toFun f := f ∘ Lattice.translate u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem zero_shift (f : Form G) : shifts G 0 f=f := by
  funext U; change f _=_; rw [show Lattice.translate 0 U=U by ext1 i; simp [Lattice.translate]]

def moves (u : Cover) (T : Finset Cover) := T.image fun i => i+u

lemma shift_local (u : Cover) {S : Finset Cover} {f : Form G} (h : LocalOn S f) : LocalOn (moves u S) (shifts G u f) := by
  intro U V hv
  apply h
  intro i hi hh; apply hv (i.1+u,i.2)
  · exact Finset.mem_image_of_mem _ hi
  change _+u+_ ∈ _; rw [add_right_comm]; exact Finset.mem_image_of_mem _ hh
lemma translate_gauge (t : Cover→G.El) (U : CoverConfig G) (u : Cover) : translate u (gauge t U) =
    gauge (fun x => t (x+u)) (translate u U) := by
  funext i; simp only [Lattice.gauge, translate]; rw [add_right_comm i.1 (step i.2) u]
lemma cov_shift (u : Cover) {f : Form G} (h : GaugeInvariant f) : GaugeInvariant (shifts G u f) := by
  intro t U; change f _=f _; rw [translate_gauge]; apply h


private lemma shrink_rates {S : Finset Cover} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : CoverConfig G → E} (h : Rate k P S 0 1 v) : Rate k P S 0 0 v := by
  obtain ⟨g,hg,h⟩ := h
  refine ⟨g,hg,fun b hb n o => ?_⟩; obtain ⟨he,hp,hB⟩ := h b hb n o
  refine ⟨he,hp,fun l hl hu U hU => ?_⟩
  apply (hB l hl hu U hU).trans
  simp only [pow_one,pow_zero,one_pow,mul_one]
  exact mul_le_of_le_one_right (by simpa using hp) (pow_le_one₀ b.threshold_pos.le b.threshold_le)

private lemma powBase (f : CoverConfig G → ℂ) (h : Rate k P T 0 0 f) (i : ℕ) : Rate k P T 0 0 fun U => f U ^ i := by
  induction i with
  | zero => simp; exact Rate.const _
  | succ i ih => simp only [pow_succ]; exact ih.mul h

lemma shift_rates (S : Finset Cover) (j : Cover) (f : Formula G S) :
    Rate k P (moves j S) 0 0 (fun U : CoverConfig G => MvPolynomial.aeval (entry (translate j U)) f) := by
  classical
  let s := moves j S
  let g := fun i U => entry (translate j U) (i : Source.Index G S)
  have hx (i) : Rate k P s 0 0 (g i) := by
    let e : Edge Cover := (i.1.val.1+j,i.1.val.2)
    let L := (Matrix.entryLinearMap ℝ ℂ i.2.1 i.2.2.1 (m:=Fin G.repDim) (n:=Fin G.repDim)).toContinuousLinearMap
    have hz := shrink_rates ((rate_link e (G:=G) (S:=s) (k:=k) (P:=P)).postcomp L)
    unfold g entry
    split; exact hz.postcomp (starL' ℝ (A:=ℂ)).toContinuousLinearMap; exact hz
  simp only [MvPolynomial.aeval_def,MvPolynomial.eval₂_eq]
  refine paid_sum _ (fun d U => (algebraMap ℂ ℂ (f.coeff d)) * ∏ i∈d.support, g i U ^ (d i)) ?_
  intro d hd
  have hm := paid_prod d.support (fun i U => g i U ^ (d i)) (fun _ => 0) (fun i _ => powBase _ (hx i) (d i))
  rw [Finset.sum_const_zero] at hm; exact (Rate.const _).mul hm

lemma shift_author (X : SectionData F) (u : Cover) (x : F.Coeff) : Affordable (moves u X.stencil) 0 (shifts G u (X.evaluate x)) :=
  Affordable.fromRate (i:=0) (shift_local _ (X.cylinder_local x)) fun _ _ => shift_rates ..
lemma shift_client (X : SectionData F) (hs : X.Sound H) (u : Cover) (F' : Labels.Frame G l) (k P : ℕ)
    (he : moves u X.stencil ⊆ T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (b : BudgetPoint), b.power=P → ∀ n, FitsIn T n → ∀ x : F.Coeff, ∀ o : Site n,
      ∃ q, Coin H F' T k b o (shifts G u (X.evaluate x)) q (c*‖x‖) := by
  classical
  let K := (shifts G u).comp (IsLinearMap.mk' X.evaluate X.eval_linear)
  let G0 (i : F.Index) : F.Coeff := Pi.single i 1
  let g (i : F.Index) := K (G0 i)
  have hZ (i : F.Index) : Affordable T ((↑(0:ℕ):ℤ)-(↑(0:ℕ):ℤ)) (g i) := by
    simpa only [sub_self] using! (shift_author X u (G0 i)).widen he
  have hg (i) : GaugeInvariant (g i) := cov_shift u (hs.gaugeInvariant _)
  let r (i) := readout l H (hZ i) (hg i)
  choose c hC hB using fun i => Coin.generator (Nat.zero_le l) 0 (g i) (r i) (hg i) (reading H (hZ i) (hg i) l)
    (hZ i) (fun _ _ _ _ hi => False.elim (Nat.not_lt_zero _ hi)) k P F'
  refine ⟨∑ i,c i, Finset.sum_nonneg fun i _ => hC _, fun b h n hn x o => ?_⟩
  have hi (x : F.Coeff) : (∑ i,x i • G0 i) = x := by ext j; simp [G0,Finset.sum_apply,Pi.single_apply]
  refine ⟨∑ i,x i • r i,?_⟩; change Coin _ _ _ _ _ _ (K x) _ _
  nth_rw 1 [← hi x]; simp_rw [map_sum, map_smul]
  refine Coin.gross x r g c (fun i => ?_); simpa using hB i n hn b h o

-- finite family of references: chosen sections up through d plus one-step shifts
def walt : Finset Cover := insert 0 (Finset.univ.image step)
lemma in_zero : 0∈walt := Finset.mem_insert_self ..


structure Gallery (d : ℕ) (H : Hol G) (F : Frames G) (X : ∀ i, SectionData (F.level i)) where
  basis : PureBasis G d
  rays : Rays G d H
  cover : Finset Cover
  sees : rays.FitsAt cover
  zone : ∀ i ≤ d, ∀ u∈walt, moves u (X i).stencil ⊆ cover

lemma populate (d : ℕ) (H : Hol G) (F : Frames G) (X : ∀ i, SectionData (F.level i)) : Nonempty (Gallery d H F X) := by
  obtain ⟨R⟩ := rays_exist d H
  obtain ⟨B⟩ := basisEq G d
  obtain ⟨S,hS⟩ := R.fitsAt_support
  let T := (Finset.range (d+1)).biUnion fun i => walt.biUnion fun u => moves u (X i).stencil
  refine ⟨B,R,S∪T, Rays.FitsAt.inclusion R hS (Finset.subset_union_left), fun i hi j hj => ?_⟩
  intro k hk; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr (Nat.lt_succ_of_le hi),
    Finset.mem_biUnion.mpr ⟨j,hj,hk⟩⟩)

variable {Z : Frames G} {X : ∀ i,SectionData (Z.level i)}
namespace Gallery
variable (A : Gallery d H Z X)
lemma holds {i} (hx : i≤d) : (X i).stencil ⊆ A.cover := by simpa [moves] using A.zone i hx 0 in_zero

structure Loans where
  -- Before filling any Paths or loops. Actual producer only calls at its
  -- param.order/.power etc. No c depending on i-level supplied ad hoc.
  sect : ℕ → ℕ → ℝ
  canon (k P : ℕ) : 1 ≤ sect k P ∧ ∀ n,FitsIn A.cover n → ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ o : Site n,
    stipend H (X d) b A.cover o (sect k P)
  score : ℕ → ℕ → ℝ
  bill (k P : ℕ) : 1 ≤ score k P ∧
    (∀ n,FitsIn A.cover n → ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ o : Site n, ∀ v, ∀ β : ℝ,0<β → β⁻¹/b.threshold^ (2:ℕ) ≤ 2 →
       Coin H (Z.level d) A.cover k b o (A.basis.tree A.rays β b.threshold v)
          (A.basis.xTree A.rays A.sees β b.threshold v) (score k P*‖v‖)) ∧
    (∀ n,FitsIn A.cover n → ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ o : Site n,
      ∀ i ≤ d, ∀ v∈walt, ∀ x, ∃ r, Coin H (Z.level d) A.cover k b o (shifts G v ((X i).evaluate x)) r (score k P*‖x‖))
  mark : ℝ
  live : 0<mark ∧ ∀ᶠ z in 𝓝 0, ∀ x, mark*‖x‖ ≤ ‖A.basis.linear A.rays A.sees (Z.level d) z x‖

lemma credits (h : ∀ i,(X i).Sound H) (hp : ∀ i,Bid.pop (X i)) : Nonempty (Loans A) := by
  classical
  obtain ⟨m,Hm,Hn⟩ := A.basis.lower_event A.rays A.sees (Z.level d)
  choose B hB hC using fun k P => tips (k:=k) (P:=P) _ (h d) (hp _) (A.holds (i:=d) le_rfl)
  have he (k P : ℕ) : ∃ r : ℝ, 1 ≤ r ∧
      (∀ n, FitsIn A.cover n → ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ o : Site n, ∀ v, ∀ β : ℝ,0<β → β⁻¹/b.threshold^ (2:ℕ) ≤ 2 →
       Coin H (Z.level d) A.cover k b o (A.basis.tree A.rays β b.threshold v) (A.basis.xTree A.rays A.sees β b.threshold v) (r*‖v‖)) ∧
      (∀ n, FitsIn A.cover n → ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ o : Site n,
        ∀ i ≤ d, ∀ v∈walt, ∀ x, ∃ a, Coin H (Z.level d) A.cover k b o (shifts G v ((X i).evaluate x)) a (r*‖x‖)) := by
    obtain ⟨a,hA,ha⟩ := eq_price A.basis A.rays A.sees (Z.level d) k P
    choose c hc hh using fun i : Fin (d+1) => fun j : walt => shift_client (X i.val) (h _) j.val (Z.level d) k P
      (A.zone i.val (Nat.le_of_lt_succ i.isLt) _ j.property)
    let C := ∑ i, ∑ j,c i j
    have hi : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc _ _
    refine ⟨1+a+C,by linarith,fun n hn b hb hk o v u hx hu => (ha b hk n hn o u hx hu v).raise
       (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),fun n hn b hb hk o i hp v hv x => ?_⟩
    obtain ⟨t,ht⟩ := hh ⟨i,Nat.lt_succ_of_le hp⟩ ⟨v,hv⟩ b hk n hn x o
    refine ⟨t,ht.raise (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
    refine le_trans ?_ (show C ≤ _ by linarith)
    exact (Finset.single_le_sum (fun j _ => hc _ j) (Finset.mem_univ ⟨v,hv⟩)).trans (Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => hc i j) (Finset.mem_univ ⟨i,Nat.lt_succ_of_le hp⟩))
  choose r hr hh using he
  exact ⟨B,fun k P => ⟨hB _ _, fun n hn b hb ht => hC _ _ _ hb ht n hn⟩,r,fun k P => ⟨hr _ _,hh _ _⟩,m,Hm,Hn⟩

end Gallery
end YM.WardBin
