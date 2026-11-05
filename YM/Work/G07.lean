import YM.Bid.Source
import YM.Work.G07.Stencil


/-!
# t^slot for G07

Rate k P S j 0 captures a t^j cost in fixed finite order and power
scopes, after wrapping anywhere. `pop` gives bona fide formulas with slot
filtration, so use the threshold cost of each slot (from health and the
link-derivative bounds) then finite polynomial calculus. Proving no uniformity
in the degree, chosen SectionData or k or P.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G07
open RG Lattice Wilson Source Bid
open scoped ContDiff Matrix.Norms.Frobenius BigOperators

variable {k P j : ℕ} {S : Finset Cover} {G : Gauge}

theorem Rate.zero_pay : Rate k P S j 0 fun _ : CoverConfig G => (0:ℂ) := by
  refine ⟨0,le_refl _,fun b _ n o => ?_⟩
  rw [zero_mul, pow_zero]
  rw [← norm_zero (E:=ℂ)]
  exact LeftBound.const (by norm_num) 0

theorem Rate.lower_pay {i : ℕ} {f : CoverConfig G → ℂ}
    (h : Rate k P S i 0 f) (hle : j ≤ i) : Rate k P S j 0 f := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c,hc,fun b hb n o => ?_⟩
  have H := h b hb n o
  have ht := b.threshold_pos.le
  refine ⟨H.smooth,mul_nonneg hc (pow_nonneg ht _),fun l hl hd U hU => (H.bound l hl hd U hU).trans ?_⟩
  simp only [pow_zero, one_pow, mul_one]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht b.threshold_le hle) hc

theorem paid_sum {ι : Type*} (I : Finset ι) (f : ι → CoverConfig G → ℂ)
    (h : ∀ i∈I, Rate k P S j 0 (f i)) : Rate k P S j 0 fun U => ∑ i∈I, f i U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Rate.zero_pay
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem paid_prod {ι : Type*} (I : Finset ι) (f : ι → CoverConfig G → ℂ) (q : ι → ℕ)
    (h : ∀ i∈I, Rate k P S (q i) 0 (f i)) :
    Rate k P S (∑ i∈I, q i) 0 fun U => ∏ i∈I, f i U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact Rate.const _
  | insert i I hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (by simp)).mul (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem Rate.paid_pow {f : CoverConfig G → ℂ} (h : Rate k P S 1 0 f) (i : ℕ) :
    Rate k P S i 0 fun U => f U ^ i := by
  induction i with
  | zero => simp only [pow_zero]; exact Rate.const _
  | succ i ih => simp only [pow_succ]; exact ih.mul h

theorem paid_lumin {m : ℕ} (p : Pose G m) (B : Fin m → Slot)
    (h : ∀ i, (B i).stencil ⊆ S) (hp : lows p j) : Rate k P S j 0 (lumin p ∘ mapped B) := by
  classical
  let x := fun (i : Fin m × G.ColorIndex) (U : CoverConfig G) => (((B i.1).eval U i.2 : ℝ) : ℂ)
  have hx (i) : Rate k P S 1 0 (x i) :=
    (((paid_slot (k:=k) (P:=P) (G:=G) _ (h i.1)).postcomp
      (EuclideanSpace.proj i.2)).postcomp Complex.ofRealCLM)
  simp only [Function.comp_def, lumin, MvPolynomial.aeval_def,MvPolynomial.eval₂_eq]
  refine paid_sum p.support (fun d U => (algebraMap ℂ ℂ (p.coeff d)) *
    ∏ i∈d.support, x i U ^ (d i)) ?_
  intro d hd
  have H := paid_prod d.support (fun i U => x i U ^ (d i)) d (fun i _ => (hx i).paid_pow _)
  -- include constant coefficient then lower the exponent
  exact ((Rate.const _).mul H).lower_pay (by rw [zero_add]; exact hp _ hd)

theorem answer : YM.Bid.G07 := by
  classical
  intro G H d F T hs hp k P
  have he (i : F.Index) : Rate k P T.stencil (F.grades i).2 0 (T.evaluate (Pi.single i 1)) := by
    obtain ⟨m,B,hB,p,hp,hi⟩ := hp i
    rw [hp]; exact paid_lumin p B hB hi
  unfold Rate at he
  choose c hc hx using he
  refine ⟨∑ i, c i, ?_⟩
  intro b hb hk n o i
  let u := T.places (Pi.single i 1) o
  have ht := b.threshold_pos.le
  have h : LeftBound k (b.dirBound o) (Healthy b.threshold (T.footprint o))
      (b.threshold^0) (c i * b.threshold^(F.grades i).2) u := hx i b hk n o
  refine ⟨⟨T.placed_local o _, (T.continuous_places _ o).measurable,
    T.placed_invariant hs o _,fun U _ => ?_,fun U _ A l hl => ?_⟩, ?_⟩
  · have Hz : ContDiff ℝ ∞ (fun v => u (increment U v)) := h.smooth [] (Nat.zero_le _) U
    exact (Hz.of_le (m:=(b.order : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  · exact h.smooth.has (hl.le.trans hb.le) U A
  refine ⟨mul_nonneg (Finset.sum_nonneg fun i _ => hc i) (pow_nonneg ht _),fun U hU l hl hD => ?_⟩
  apply (h.bound l (hl.trans hb.le) hD U hU).trans
  simp only [pow_zero, one_pow, mul_one]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun u _ => hc u) (Finset.mem_univ i))
    (pow_nonneg ht _)

end YM.Work.G07
