import YM.Next.MULTISOURCE.Seat

/-! approximants from the output scalar bank. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice Marker Finset Filter MeasureTheory MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side}
variable {P : Rep G n} (T : Reservoir P I)

def sell (N : ℕ) (U : Config G n) := staves T.pay + ∑ j∈ range N,T.keeps j U

def trade (N : ℕ) (U : Config G n) (i : Pack n) := ∑ j∈ range N,T.records i j U

def displayU (N : ℕ) (U : Config G n) := vapor N (sell T N U) * chip P U (trade T N U)

variable {s r v p : ℝ} {K : Set (I→ℂ)} (H : T.Tested p K)
include H

lemma adequate (U : Config G n) (he : 0 < r) (ht : r<s) (hu : boxes s ⊆ K) :
    TendstoUniformlyOn (fun i z => eval z (displayU T i U)) (fun z => T.signal z U) atTop (boxes r) := by
  have hX : boxes r ⊆ boxes (I:=I) s := fun _ hz i => (hz i).trans ht.le
  have hk (j : Pack n) := dyed_K T H (hX.trans hu) U j
  simp only [displayU, map_mul,chip_eval,vapor_eval, Reservoir.signal, progeny]
  have hE := dyed_E T H (hX.trans hu) U
  apply uniform_mul (colors hE) ?_
  · refine condensate hE ?_; simp only [sell,Reservoir.tasteE,map_add,map_sum]
    exact (painting (boxes r) (fun z : I→ℂ => eval z _)).add (normal he ht
      (fun i => T.keeps i U) (fun z hz => several_H T H U z (hu hz)))
  · unfold baseJoint
    have hj (i : Finset (Pack n)) := tint_prod i (fun j => fun z : I→ℂ => incumbent P U j+T.tasteK j z U)
      (fun j => tint_add (tint_fix (boxes r) (incumbent P U j)) (hk j))
    refine uniform_mul (tint_fix (boxes r) _) (tint_sum _ _ hj) (painting _ _) ?_
    refine uniform_sum _ _ _ (fun i => ?_)
    refine uniform_prod i _ _ (fun j => (painting _ _).add ?_) fun j => tint_add (tint_fix _ _) (hk j)
    simp only [trade,Reservoir.tasteK,map_sum]
    exact normal he ht (fun i => T.records _ i U) (fun z hz => several_K T H U j z (hu hz))
  unfold baseJoint
  exact tint_mul (tint_fix ..) (tint_sum _ _ (fun i => tint_prod i _ fun j => tint_add (tint_fix ..) (hk j)))

omit [Fintype I] [DecidableEq I] in
lemma keeps_tem (i) U : coeff 0 (T.keeps i U)=0 := by
  unfold Reservoir.keeps; by_cases h : Healthy P.p.threshold (T.support i) U
  · rw [masked_eq _ _ _ _ h]; exact H.warm ..
  rw [masked_ne _ _ _ _ h]; simp
omit [Fintype I] [DecidableEq I] in
lemma records_tem (x i U) : coeff 0 (T.records x i U)=0 := by
  unfold Reservoir.records; split; exact H.temp ..; exact coeff_zero _
lemma sufficiently (R : Census I) (N U) : coeff 0 (sell T N U)=0 := by
  simp only [sell,MvPolynomial.coeff_add,MvPolynomial.coeff_sum,staves_zero R,keeps_tem T H,sum_const_zero,zero_add]
lemma spare (U : Config G n) (R : Census I) (q : R.Mode) (h : 0 < s) (hr : boxes s ⊆ K) :
    Tendsto (fun i => coeff (power q.val) (displayU T i U)) atTop (𝓝
      ((many P R (fun i => T.taste (power i.sites)) U).part q)) := by
  let F (i : Hot R) := T.taste (power i.sites)
  let f := lit R fun i => (F i).1 U
  let g x := lit R fun i => (F i).2 x U
  have hf : Tendsto (fun i => print R (sell T i U)) atTop (𝓝 f) := by
    refine tendsto_pi_nhds.mpr ?_; intro i
    change Tendsto (fun t => (print R (sell T t U)).part i) atTop (𝓝 (f.part i))
    simp_rw [print_coeff]
    by_cases hv : i.val.Nonempty
    · let t : Hot R := ⟨i,hv⟩
      change Tendsto _ _ (𝓝 (f.part t.val)); rw [show f.part t.val = (F t).1 U from part_lit ..]
      simp only [sell,MvPolynomial.coeff_add,MvPolynomial.coeff_sum]
      exact tendsto_const_nhds.add ((((nuclear (fun i => T.keeps i U) (fun z hz => several_H T H U z (hr hz))
        h (power t.sites)).2.1).of_norm).hasSum.tendsto_sum_nat)
    rw [show i=R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp hv)]
    simp only [f,part_lit_quiet]; simp only [Census.quiet,power_empty,sufficiently T H R]
    exact tendsto_const_nhds
  have hg x : Tendsto (fun i => print R (trade T i U x)) atTop (𝓝 (g x)) := by
    refine tendsto_pi_nhds.mpr ?_; intro j
    change Tendsto (fun t => (print R (trade T t U x)).part j) atTop (𝓝 ((g x).part j))
    simp_rw [print_coeff,trade, MvPolynomial.coeff_sum]
    by_cases hv : j.val.Nonempty
    · let t : Hot R := ⟨j,hv⟩
      change Tendsto _ _ (𝓝 ((g x).part t.val)); rw [show (g x).part t.val = (F t).2 x U from part_lit ..]
      exact (((nuclear (fun i => T.records x i U) (fun z hz => several_K T H U x z (hr hz))
        h (power t.sites)).2.1).of_norm).hasSum.tendsto_sum_nat
    rw [show j=R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp hv)]
    simp only [g,part_lit_quiet]; simp only [Census.quiet,power_empty,records_tem T H,Finset.sum_const_zero]
    exact tendsto_const_nhds
  have ht : Tendsto (fun i => print R (displayU T i U)) atTop (𝓝 (many P R F U)) := by
    let M i := composeAt P U (print R (sell T i U)) (fun x => print R (trade T i U x))
    have he : Tendsto M atTop (𝓝 (composeAt P U f g)) :=
      ((Filter.Tendsto.mul ((Poly.pass_cont.tendsto _).comp hf) (tendsto_finsetSum _ (fun i _ =>
        tendsto_finsetProd _ (fun j _ => tendsto_const_nhds.add (hg j))))).const_smul _)
    refine he.congr' ?_
    filter_upwards [eventually_ge_atTop (Fintype.card I)] with i hi
    exact (patch P U _ _ R hi (sufficiently T H R ..)).symm
  simp_rw [← print_coeff R]
  exact (Poly.part_cont q).continuousAt.tendsto.comp ht
end YM.Multi.Desk
