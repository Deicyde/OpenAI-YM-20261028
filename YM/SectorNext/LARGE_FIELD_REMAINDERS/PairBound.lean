import YM.SectorNext.LARGE_FIELD_REMAINDERS.PairLocal


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Accounting the pair comparison

The subenergy below is on remote actual rows even in unassigned. No Hessian or
connected-component estimates assumed. Membership of plateaux used before booking
work terms; if integrating occurrences out of this order still need prerequisites
(e.g. after a Gaussian change). May lose a little Taylor error even between equal
configurations (suitable for integration bill; not a Lipschitz estimate).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Center
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def core (T : Tube G S) (A : Stores S) (x : ℝ) (V : Config G c) (U : Config G f) (k : S.Choices) :=
  (∑ i, (faceBill T A x V U i)^2)+(∑ i, (bondBill T A x V (S.prediction U k) i)^2)
lemma core_nn (T : Tube G S) (A x V U k) : 0 ≤ core T A x V U k := by unfold core; positivity

def pairCost (A : Stores S) (x : ℝ) (U V : Config G f) :=
  ∑ i ∈ Finset.univ.filter (isolated A (radiusB x)), G.chord (U i * (V i)⁻¹) ^ 2
lemma pairCost_nn (A : Stores S) (x U V) : 0 ≤ pairCost (G:=G) A x U V := by unfold pairCost; positivity

lemma drape_pair (A : Stores S) (x : ℝ) (F : Forest S.ratio) (a v : F.Slice G) :
    ∑ i∈regular A (2*radiusB x) F, G.chord (a i*(v i)⁻¹)^2 ≤ pairCost A x (F.drape a) (F.drape v) := by
  let g (i : Bond f) := if isolated A (radiusB x) i then G.chord (F.drape a i*(F.drape v i)⁻¹)^2 else 0
  have hg := sum_free_le F g (fun i => by unfold g; split; positivity; rfl)
  simpa only [regular, Finset.sum_filter, pairCost,g, isolated,Forest.off_tree] using! hg

private lemma from_links (T : Tube G S) (A : Stores S) (x : ℝ) (V : Config G c) (U U' : Config G f)
    (k k' : S.Choices) (C z : ℝ) (hC : 0≤C) (hz : 0≤z)
    (h : ∀ e : Bond f, isolated A (radiusB x) e →
          let R := macroR S.patch; let o := S.ratio.parent e.1
          let q i := faceBill T A x V U i+faceBill T A x V U' i
          let p := (o,e.2)
          G.chord (U e*(U' e)⁻¹) ≤ C*
            ((∑ z∈box R, ∑ j : PlaqAxes, q (patchAt S z o,j)) + (bondBill T A x V (S.prediction U k) p+bondBill T A x V (S.prediction U' k') p) + z)) :
    let Y := Work.F01.curlFactor S.patch.L (box (macroR S.patch)) C
    let B := Work.F01.probeFactor S.patch.L
    pairCost A x U U' ≤ (2*Y+4*C^2*B)*(core T A x V U k+core T A x V U' k'+z^2*Fintype.card (Bond c)) := by
  intro Y B
  let I := Equiv.prodCongr (Equiv.refl (Site f)) Exterior.plaqEquiv
  let J := Equiv.prodCongr (Equiv.refl (Site c)) Exterior.axisEquiv
  let K := fun u => faceBill T A x V u
  let N := fun u j => bondBill T A x V (S.prediction u j)
  let R q := K U (I.symm q)+K U' (I.symm q)
  let W p := C*(N U k (J.symm p)+N U' k' (J.symm p)+z)
  let t (e : Bond f) := if isolated A (radiusB x) e then G.chord (U e*(U' e)⁻¹) else 0
  let g := S.ratio
  have he e : 0 ≤ t e := by unfold t; split; exact G.chord_nonneg _; rfl
  have hw (p : Cell f) : I.symm (p.1,Exterior.plaquette p.2)=p := I.symm_apply_apply p
  have hv (b : Bond c) : J.symm (b.1,Exterior.coord b.2)=b := J.symm_apply_apply b
  have ht := Work.F01.sum_estimate g (box (macroR S.patch)) R W t C he fun e => by
    simp_rw [R,K, W,N, show ∀ (z : Site f) (p : PlaqAxes), I.symm (z,plaquette p) = (z,p) from
      fun z p => hw (z,p), show J.symm (_,coord _) = (g.parent e.1,e.2) from hv _]
    unfold t; split
    next j => exact (h e j).trans_eq (by dsimp only; unfold g patchAt; ring)
    next j =>
      have hr := Finset.sum_nonneg (fun (i : Cover) (_:i∈box (macroR S.patch)) => Finset.sum_nonneg
        (s:=Finset.univ) (fun b _ => add_nonneg (faceBill_nn T A x V U (patchAt S i (g.parent e.1),b)) (faceBill_nn T A x V U' (patchAt S i (g.parent e.1),b))))
      exact add_nonneg (mul_nonneg hC hr) (mul_nonneg hC (add_nonneg (add_nonneg (bondBill_nn ..) (bondBill_nn ..)) hz))
  rw [pairCost]; rw [Finset.sum_filter]; unfold t at ht; simp_rw [apply_ite (· ^ (2:ℕ)),zero_pow (by norm_num : 2≠0)] at ht
  apply ht.trans
  have hn : 0≤Y := by unfold Y Work.F01.curlFactor; positivity
  have hp : 0≤B := by unfold B Work.F01.probeFactor; positivity
  let m := core T A x V U k+core T A x V U' k'+z^2*(Fintype.card (Bond c):ℝ)
  have hm : 0≤m := add_nonneg (add_nonneg (core_nn ..) (core_nn ..)) (by positivity)
  -- R sums bound by face cores, W uses bond cores and cardinal.
  have hi (u l) : ∑ i, (K u i)^2 ≤ core T A x V u l := le_add_of_nonneg_right (by positivity)
  have hq (u l) : ∑ i, (N u l i)^2 ≤ core T A x V u l := le_add_of_nonneg_left (by positivity)
  have hR : ∑ i, (R i)^2 ≤ 2*m := by
    rw [← Equiv.sum_comp I (fun i => (R i)^2)]
    apply le_trans (b:=∑ i, (2*(K U i)^2+2*(K U' i)^2))
    · apply Finset.sum_le_sum; intro i _; unfold R; rw [Equiv.symm_apply_apply]
      nlinarith [sq_nonneg (K U i-K U' i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,← Finset.mul_sum]; unfold m
    nlinarith [hi U k,hi U' k', show 0 ≤ (Fintype.card (Bond c) : ℝ) by positivity]
  have hW : ∑ i, (W i)^2 ≤ 4*C^2*m := by
    rw [← Equiv.sum_comp J (fun i => (W i)^2)]; unfold W
    apply le_trans (b:=∑ i, C^2*(4*((N U k i)^2+(N U' k' i)^2+z^2)))
    · apply Finset.sum_le_sum; intro i _; rw [J.symm_apply_apply,mul_pow]
      let p := N U k i; let q := N U' k' i
      have he : (p+q+z)^2≤4*(p^2+q^2+z^2) := by
        nlinarith [sq_nonneg (p-q),sq_nonneg (p+q-z)]
      exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
    rw [← Finset.mul_sum,← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
    rw [mul_left_comm 4]
    change C^2* (4*_)≤ C^2*(4*m)
    apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg C) -- 4 first need reorder
    unfold m; nlinarith only [hq U k,hq U' k']
  change Y*(∑ i,(R i)^2)+B*(∑ i,(W i)^2) ≤ (2*Y+4*C^2*B)*m
  nlinarith [mul_le_mul_of_nonneg_left hR hn, mul_le_mul_of_nonneg_left hW hp]

/-- Pair gap without any supremum assumptions on v/w shifts, but with *both*
fields still under their respective actual sector occurrences at the same A,V.
Full physical comparisons even though thresholds fixed and independent.
-/
lemma pair_quote (P : Teller G) (L : Side) (W : ℝ) (hw : 0<W) :
    ∃ (C : ℝ) (l : ℝ → ℝ), 0<C ∧ (∀ᶠ x in atTop,0≤l x) ∧ (∀ n : ℕ, Tendsto
      (fun x : ℝ => b x ^ n * y G L x*l x) atTop (𝓝 0)) ∧
    ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (U U' : Config G f) (k k' : S.Choices) (V : Config G c),
        SliceSet S F U → SliceSet S F U' → Seeded A U k V x W → Seeded A U' k' V x W → Alive S U k → Alive S U' k' →
          pairCost A x U U' ≤ C*(core T A x V U k+core T A x V U' k'+l x*(Fintype.card (Site c):ℝ)) := by
  obtain ⟨C,hC,H⟩ := two_links P L W hw
  let N := (P.j+7)*L.val
  let D := Work.F01.curlFactor L (box N) C
  let E := Work.F01.probeFactor L
  have hD : 0≤D := by unfold D Work.F01.curlFactor; positivity
  have hE : 0≤E := by unfold E Work.F01.probeFactor; positivity
  let K := 2*D+4*C^2*E
  have hK : 0≤K := by unfold K; positivity
  let u : ℝ := Fintype.card Axis
  let l x := u*(b x^5*fiery G x L)^4
  have hl x : 0≤l x := by unfold l u; positivity
  refine ⟨K+1,l,by linarith,Eventually.of_forall hl,fun n => ?_,?_⟩
  · have ht := ((tally_g G L (n+20) 4).mul (minute G L)).const_mul u
    rw [mul_zero,mul_zero] at ht
    refine ht.congr' ?_
    filter_upwards [(year G L).eventually_gt_atTop 0] with x hx
    unfold l; rw [fi]
    have he := yg2 G L hx
    rw [show b x^n*y G L x*(u*(b x^5*(g G L x*p G L x))^4)=
      u*b x^(n+20)*p G L x^4 * g G L x * g G L x * (y G L x*(g G L x)^2) by rw [pow_add]; ring, he]
    ring
  filter_upwards [H] with x hx
  intro c f S T hL hn hT F A U U' k k' V h1 h2 h3 h4 h5 h6
  have he := hx c f S T hL hn hT F A U U' k k' V h1 h2 h3 h4 h5 h6
  let z := (b x ^ 5 * fiery G x L)^2
  have hh := from_links T A x V U U' k k' C z hC.le (by unfold z; positivity) he
  apply hh.trans
  have hk : macroR S.patch=N := by rw [Work.E01.macroR_eq,hT.atStep,hL]
  rw [hk,hL]
  change K*(core _ _ _ _ _ _ + core _ _ _ _ _ _+ _) ≤ (K+1)*_
  have hx (V : ℝ) : z^2*(Fintype.card (Bond c):ℝ)=l x * Fintype.card (Site c) := by
    unfold z l u Bond Edge; simp; ring
  rw [hx 0]
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact add_nonneg (add_nonneg (core_nn ..) (core_nn ..)) (mul_nonneg (hl _) (Nat.cast_nonneg _))
end YM.SectorNext.Remainder.Center
