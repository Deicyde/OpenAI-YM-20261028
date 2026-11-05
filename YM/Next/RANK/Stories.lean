import YM.Bid.Loan
import YM.Next.RANK.LineBox
import YM.Next.RANK.Tuning

/-!
# Don't assert a finite list of regular coefficients

To aggregate a stencil polynomial from genuine absolute sum estimates. `Lists` keeps the
individual probes' coefficients even across masks and projectors, no hidden cancellation
in the norm or evaluation costs. Includes evaluation through regular caps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function MvPolynomial Normal Rise Common RG Source Wilson Lattice Filter Set Asymptotics
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius ContDiff

variable {n : Side} {p : RG.BudgetPoint} {o : Site n} {b : ℕ} {G : Gauge}
variable {ι V : Type*}
section guard
variable [Fintype V] (P : ι→poly V) (d : ℕ)

structure Lists (L : poly V) : Prop where
  words : ∀ i,totalDegree (P i)≤d
  degree : totalDegree L≤d
  charges : Summable fun i => coin (P i)
  cells i : Summable (fun k => coeff i (P k))
  traces i : coeff i L =∑' k, coeff i (P k)

-- aggregate by ordinary finite report support at fixed b.
private lemma survey : ∃ s : Finset (V →₀ ℕ), ∀ P : poly V, totalDegree P≤d → P.support ⊆ s := by
  let F:=restrictTotalDegree V ℂ d
  let B := Module.finBasis ℂ F
  let g i := (B i).val.support
  refine ⟨Finset.univ.biUnion g, fun p h => ?_⟩
  let q : F := ⟨p,(mem_restrictTotalDegree ..).mpr h⟩
  rw [show p= ∑ i,(B.repr q i) • (B i).val from (by
    have H := congr_arg F.subtype (B.sum_repr q); rw [map_sum] at H; simp_rw [map_smul] at H; exact H.symm)]
  exact Finset.Subset.trans MvPolynomial.support_sum (fun i h => by
    obtain ⟨j,hJ,h⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨j,hJ, MvPolynomial.support_smul h⟩)
variable (hP : ∀ i, totalDegree (P i)≤d) (hv : Summable fun i => coin (P i))
omit [Fintype V] in
private lemma nothing {f : ι → ℂ} (h : ∀ i,f i=0) : ∑' i,f i=0 := Eq.trans (tsum_congr (g:=fun _=>0) h) tsum_zero
include hP hv
lemma bindings : ∃ L, Lists P d L := by
  have hh (i : V →₀ ℕ) : Summable (fun k=> coeff i (P k)) := Summable.of_norm_bounded hv fun k=> notes_co _ _
  obtain ⟨s,hs⟩ := survey (V:=V) d
  let L := ∑ i ∈ s, monomial i (∑' k, coeff i (P k))
  have hx i : coeff i L=∑' k, coeff i (P k) := by
    unfold L; rw [coeff_sum]; by_cases h : i∈s
    · simp only [coeff_monomial, Finset.sum_ite_eq',h,↓reduceIte]
    simp only [coeff_monomial,Finset.sum_ite_eq',h,↓reduceIte]; rw [nothing (fun v => MvPolynomial.notMem_support_iff.mp fun he => h (hs _ (hP v) he))]
  refine ⟨L,hP,?_,hv,hh,hx⟩
  apply Finset.sup_le; intro i hi; have hv:= MvPolynomial.mem_support_iff.mp hi
  rw [hx] at hv
  by_contra hh
  exact hv (nothing fun v => MvPolynomial.notMem_support_iff.mp (fun he => hh ((MvPolynomial.le_totalDegree he).trans (hP v))))
end guard

section
variable [Fintype V] {P : ι→poly V} {L : poly V} {d : ℕ} (h : Lists P d L)
include h
lemma value_at (Y : poly V→ₗ[ℂ] ℂ) : HasSum (fun i => Y (P i)) (Y L) := by
  obtain ⟨s,hs⟩ := survey (V:=V) d
  have he (p : poly V) (hp : p.support⊆s) : Y p=∑ i∈s,coeff i p * Y (monomial i 1) := by
    nth_rw 1 [p.as_sum]; rw [map_sum]; calc
      _ = ∑ i∈p.support, coeff i p * Y (monomial i 1) := by
        apply Finset.sum_congr rfl; intro i _; rw [show monomial i (coeff i p)=coeff i p • monomial i 1 by rw [← map_smul,smul_eq_mul,mul_one],map_smul];rfl
      _ = _ := Finset.sum_subset hp (fun i _ he => by rw [MvPolynomial.notMem_support_iff.mp he, zero_mul])
  simp_rw [he (P _) (hs _ (h.words _)), he L (hs _ h.degree),h.traces]; exact hasSum_sum (fun i _ => (h.cells i).hasSum.mul_right _)
lemma texts (x : V→ℝ) : HasSum (fun i => text x (P i)) (text x L) := value_at h (aeval (R:=ℂ) (fun i => (x i:ℂ))).toLinearMap
omit [Fintype V] in
lemma billed : coin L ≤ ∑' k,coin (P k) := by
  rw [metal]; calc
    _ ≤ ∑ i∈ L.support, ∑' k,‖coeff i (P k)‖ := Finset.sum_le_sum fun i _ => (h.traces i) ▸ norm_tsum_le_tsum_norm (Summable.norm (h.cells i))
    _ ≤ _ := by
      rw [← Summable.tsum_finsetSum (f:=fun i k => ‖coeff i (P k)‖) (s:=L.support) (fun i _ => (h.cells i).norm)]
      apply Summable.tsum_le_tsum _ (summable_sum (s:=L.support) (fun i _ => (h.cells i).norm)) h.charges
      intro i; let p:= P i; rw [metal]; change (∑ x∈L.support, ‖coeff x p‖)≤_
      rw [show (∑ x∈L.support,‖coeff x p‖)=∑ x∈L.support ∩ p.support, ‖coeff x p‖ from Eq.symm (Finset.sum_subset Finset.inter_subset_left
        (fun j hj hk => by rw [MvPolynomial.notMem_support_iff.mp (fun H => hk (Finset.mem_inter.mpr ⟨hj,H⟩)),norm_zero]))]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => norm_nonneg _)

end

section terms
variable (S : Rules G) (o : Site n) (b : ℕ) (p : RG.BudgetPoint)

-- weighted family; no differentiation of masks included.

structure Teller (d : ℕ) (X : ι → Support n) (A : ι→Config G n→ℂ) (f : ι→ℂ) (e : ι→ℝ) (T : ℝ) (L : poly (links G o b)) : Prop where
  produced : ∃ E, Lists E d L ∧ ∀ i,
    coin (E i)≤ ‖f i‖*e i * T ∧
      ∀ x, ‖x‖ ≤ pane S → ‖f i*A i (net p o b x)-text (scan x) (E i)‖≤ ‖f i‖ * e i * ‖x‖^(d+1)
  smooth i : p.Regular (X i) (A i)
  contact i : p.supBounds o (X i) (A i) (e i)
  collects : Summable fun i => ‖f i‖ * e i

lemma till (S : Rules G) (d : ℕ) : ∃ c : ℝ, 0≤c ∧ ∀ (ι : Type) (n : Side) (o : Site n) (b : ℕ) (X : ι → Support n) (A : ι→Config G n → ℂ) (f : ι → ℂ) (p : RG.BudgetPoint),
    d+1≤p.order → (∀ i,p.Regular (X i) (A i)) → ∀ e : ι→ ℝ,(∀ i,p.supBounds o (X i) (A i) (e i)) →
      Summable (fun i=>‖f i‖*e i) → ∃ L,Teller S o b p d X A f e (((Fintype.card (links G o b):ℝ)+1)^d*c) L := by
  obtain ⟨C,hC,H⟩ := minted S d
  refine ⟨C,hC,fun ι n o b X A f p h hs e he hq => ?_⟩
  choose P hP Hp hr ht using fun i => H n o b (X i) (A i) p h (hs i) (e i) (he i)
  let E (i : ι) := f i • P i
  let v := (Fintype.card (links G o b):ℝ)
  have hv i : coin (E i)≤ ‖f i‖ * e i * ((v+1)^d*C) := ((retiring _ _).trans
    (mul_le_mul_of_nonneg_left (Hp i) (norm_nonneg _))).trans_eq (by ring)
  obtain ⟨L,hL⟩ := bindings E d (fun i => (totalDegree_smul_le ..).trans (hP i))
    ((hq.mul_right ((v+1)^d*C)).of_nonneg_of_le (fun i => Rise.sign _ _ zero_le_one) hv)
  refine ⟨L,⟨⟨E,hL, fun i => ⟨hv i, fun x hx=>?_⟩⟩,hs,he,hq⟩⟩
  unfold E text; rw [map_smul,smul_eq_mul,←mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (ht _ x hx) (norm_nonneg _)).trans_eq (by ring)

variable {X : ι→ Support n} {A : ι→ Config G n → ℂ} {f : ι→ℂ} {e : ι→ℝ} {d : ℕ} {T : ℝ} {p b o S} {L : poly (links G o b)}
    (h : Teller S o b p d X A f e T L)
include h
lemma Teller.charge : coin L ≤ (∑' i, ‖f i‖*e i)*T := by
  obtain ⟨P,H,ht⟩ := h.produced
  apply (billed H).trans; rw [← tsum_mul_right]; exact H.charges.tsum_le_tsum (fun i => (ht i).1) (h.collects.mul_right T)
lemma Teller.calls (x : Space G o b) (hx : ‖x‖≤pane S) : HasSum (fun i=> f i*A i (net p o b x)) (∑' i, f i*A i (net p o b x)) ∧
    ‖(∑' i, f i*A i (net p o b x))-text (scan x) L‖≤(∑' i, ‖f i‖* e i)*‖x‖^(d+1) := by
  obtain ⟨E,hE,ht⟩ := h.produced; let T i:= text (scan x) (E i); let C i:=f i*A i (net p o b x)
  let F i:= ‖f i‖* e i
  have hw : HasSum T _ := texts hE (scan x)
  have hF (i) := (ht i).2 x hx
  have he : Summable (fun i=>‖C i-T i‖) := (h.collects.mul_right _).of_nonneg_of_le (fun i => norm_nonneg _) hF
  have ha : Summable (fun i=> C i-T i) := he.of_norm
  have hp : Summable C := (ha.add hw.summable).congr (fun i => sub_add_cancel ..)
  refine ⟨hp.hasSum,?_⟩; change ‖(∑' i,C i)-text (scan x) L‖≤_; rw [← hw.tsum_eq, ← Summable.tsum_sub hp hw.summable]; apply (norm_tsum_le_tsum_norm he).trans; rw [← tsum_mul_right]; exact he.tsum_le_tsum hF (h.collects.mul_right _)
end terms
end YM.Next.Rank.Spindle
