import YM.Next.WARD_BIN.Force

/-!
# The common support and estimate at each order

Use the same stencil for all reads (including divergence). Only need nonwrapped
placements at the physical side. Costs before pricing: through only finite order and
weight in each call. Do not charge these constants after picking L: proof of applications
later explicitly assumes column scheduling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G07 Work.G06 Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {H : Hol G} {d j : ℕ} {S : Finset Cover}

lemma affords_slot (a : Slot) : Affordable a.stencil 1 (a.eval (G:=G)) :=
  Affordable.fromRate (i:=1) a.covered (fun _ _ => paid_slot a le_rfl)

private lemma from_slanted (p : Walk) (a b : Step) (h : a.dir ≠ b.dir) :
    ∃ S, Affordable S 1 (slanted (G:=G) p a b) := by
  obtain ⟨c,r,-,hc⟩ := slanted_slot (G:=G) p a b h
  rw [funext hc]; exact ⟨_, (affords_slot (G:=G) c).postcomp (r • ContinuousLinearMap.id ℝ _)⟩

private lemma collect {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {l : ℤ} {ι : Type*}
    (I : Finset ι) (f : ι → CoverConfig G → X)
    (h : ∀ i∈I, ∃ S, Affordable S l (f i)) : ∃ S, Affordable S l fun U => ∑ i∈I, f i U := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨∅, by simp only [Finset.sum_empty]; exact Affordable.zero⟩
  | insert i s hi ih =>
    obtain ⟨S,hS⟩ := h i (by simp)
    obtain ⟨T,hT⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact ⟨S∪T,by simp_rw [Finset.sum_insert hi]; exact (hS.widen (Finset.subset_union_left)).add (hT.widen Finset.subset_union_right)⟩

-- Don't shrink the actual designated support to the bound proofs'
-- stencils; we'll also fit every wheel and the route itself, below.
lemma sampler_budget (e : Edge Cover) : ∃ S, Affordable S 1 (sample (G:=G) e) := by
  let p := route 0 e.1 1
  let f (i : Axis) (U : CoverConfig G) :=
    slanted p (posDir e.2) (posDir i) U + slanted p (posDir e.2) (negDir i) U
  have h : sample (G:=G) e = fun U => ∑ i : Axis with i ≠ e.2,f i U := by
    funext U; simp only [f,p,sample,slanted,toBond,wheel,route_end,euler, map_sum,map_add]
  rw [h]; apply collect; intro i hi
  have hu := Finset.mem_filter.mp hi
  obtain ⟨S,hS⟩ := from_slanted (G:=G) p (posDir e.2) (posDir i) hu.2.symm
  obtain ⟨T,hT⟩ := from_slanted (G:=G) p (posDir e.2) (negDir i) hu.2.symm
  exact ⟨S∪T,(hS.widen Finset.subset_union_left).add (hT.widen Finset.subset_union_right)⟩

private lemma rate_reduce {k P a : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : CoverConfig G → E} (h : Rate k P S a 1 v) : Rate k P S a 0 v := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c,hc,fun b hb n o => ?_⟩; obtain ⟨he,hp,hB⟩ := h b hb n o
  refine ⟨he,hp,fun l hl hu U hU => ?_⟩
  apply (hB l hl hu U hU).trans
  simp only [pow_one,pow_zero,one_pow,mul_one]
  exact mul_le_of_le_one_right hp (pow_le_one₀ b.threshold_pos.le b.threshold_le)

private lemma attach_cost (e : Edge Cover) (hx : (visits 0 (route 0 e.1 1)).toFinset ⊆ S)
    (a : G.Color) : Affordable S 0 fun U => G.adjoint (toBond e U) a := by
  refine Affordable.fromRate (i:=0) ?_ (fun k P => ?_)
  · intro U V he; change G.adjoint _ _=G.adjoint _ _
    rw [show toBond e U=toBond e V from
      travel_local (0:Cover) (route 0 e.1 1) _ _ fun l hi hk => he l (hx (List.mem_toFinset.mpr hi))
        (hx (List.mem_toFinset.mpr hk))]
  apply rate_reduce
  have ht : Rate k P S 0 1 fun U : CoverConfig G => G.mat (toBond e U) := rate_path ..
  have hg : Rate k P S 0 1 fun U : CoverConfig G => star (G.mat (toBond e U)) :=
    ht.postcomp (starL' ℝ).toContinuousLinearMap
  exact (((ht.mul (Rate.const (G.colorMat a))).mul hg).postcomp G.projectColor.toContinuousLinearMap)

namespace Rays
variable (R : Rays G d H)

-- Ancillary supports don't purport to say that a merger or history rep at N
-- already has free addresses of this size. That will be an input.
def tracesOf (e : Edge Cover) := (visits 0 (route 0 e.1 1)).toFinset ∪
  Finset.univ.biUnion fun i : Axis =>
    (visits e.1 (oriented (posDir e.2) (posDir i))).toFinset ∪
    (visits e.1 (oriented (posDir e.2) (negDir i))).toFinset

structure FitsAt (S : Finset Cover) : Prop where
  anchor : 0 ∈ S
  sampled (i : Fin R.k) : (R.slots i).stencil ⊆ S
  traces (e : R.edg) : tracesOf e.val ⊆ S
  seen (e : R.edg) : Affordable S 1 (sample (G:=G) e.val)

lemma FitsAt.inclusion {T : Finset Cover} (h : R.FitsAt S) (he : S⊆T) : R.FitsAt T :=
  ⟨he h.anchor,fun i => Finset.Subset.trans (h.sampled i) he,
    fun i => Finset.Subset.trans (h.traces i) he,fun i => (h.seen i).widen he⟩

lemma fitsAt_support : ∃ S : Finset Cover, R.FitsAt S := by
  classical
  choose T ht using fun e : R.edg => sampler_budget (G:=G) e.val
  let v := Finset.univ.biUnion fun e : R.edg => T e ∪ tracesOf e.val
  let w := Finset.univ.biUnion fun i : Fin R.k => (R.slots i).stencil
  let S := insert (0:Cover) (v∪w)
  refine ⟨S,by unfold S;simp,fun i => ?_,fun e => ?_,fun e => (ht e).widen ?_⟩
  · intro x hx; exact Finset.mem_insert_of_mem <| Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)
  · intro x hx; exact Finset.mem_insert_of_mem <| Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_right _ hx⟩)
  · intro x hx; exact Finset.mem_insert_of_mem <| Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_left _ hx⟩)

variable (f : R.FitsAt S) (M : Tensor.T (Snap G d) ℂ (j+1))
include f
lemma fitsAt_edge (e : R.edg) : e.val.1∈S ∧ e.val.1+step e.val.2∈S := by
  let s := (posDir e.val.2)
  have he (x : Cover) (he : x∈visits e.val.1 (oriented s (posDir 0))) : x∈S :=
    f.traces e <| Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(0:Axis),Finset.mem_univ _,
      Finset.mem_union_left _ (List.mem_toFinset.mpr he)⟩)
  exact ⟨he _ (List.mem_cons_self),he _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

lemma pays_affordable (e : R.edg) (a : G.Color) : Affordable S 0 (fun U => R.pays U e a) :=
  ((attach_cost (S:=S) e.val (Finset.Subset.trans Finset.subset_union_left (f.traces e)) a).postcomp
    (R.lifts.comp (ContinuousLinearMap.single ℝ (fun _ : R.edg => G.Color) e)))

lemma guess_affordable : Affordable S 1 R.guess := by
  have he := Affordable.array (fun i : Fin R.k => (R.slots i).eval (G:=G))
    (fun i => affords_slot (G:=G) (R.slots i)|>.widen (f.sampled i))
  exact he.postcomp R.read.toContinuousLinearMap

lemma gap_affordable : Affordable S 1 R.gap :=
  (Affordable.array (fun e : R.edg => sample (G:=G) e.val) f.seen).postcomp R.lifts


-- Use the telescope with **one** slot replaced by the direction call.
omit f in
private lemma slotCost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {x y z : CoverConfig G → E} (hu : Affordable S 1 x) (hv : Affordable S 1 y) (hz : Affordable S 0 z)
    (M : Tensor.T E ℂ (j+1)) (i : Fin (j+1)) : Affordable S (j:ℤ) fun U => factor M (x U) (y U) i (z U) := by
  let W := fun a : Fin (j+1) => if a=i then (0:ℤ) else 1
  let Z := fun k U => update (phased (x U) (y U) i.val) i (z U) k
  have hw : ∑ k, W k = j := by
    simp [W,Finset.sum_ite, show (Finset.univ.filter (fun x => ¬ x=i)) = Finset.univ.erase i by ext; simp]
  rw [← hw]; refine Affordable.multilinear Z W (fun k => ?_) M
  by_cases h : k=i
  · subst k; simpa [W,Z] using hz
  dsimp only [Z]; simp only [W,if_neg h,update_of_ne h,phased]
  split; exacts [hu,hv]

lemma coField_affordable (e : R.edg) : Affordable S (j:ℤ) (R.coField M e) := by
  classical
  refine Affordable.clm (R.coField M e) fun a => ?_
  have he (U) : R.coField M e U a =
      ∑ i : Fin (j+1), factor M (R.guess U) (R.guess U - R.gap U) i (R.pays U e a) :=
    sum_apply _ _ _
  rw [funext he]; refine Affordable.sum _ (fun i U => factor M _ _ i _) (fun i _ => ?_)
  exact slotCost (R.guess_affordable f) ((R.guess_affordable f).sub (R.gap_affordable f))
    (R.pays_affordable f e a) M i

lemma force_affordable : Affordable S ((j:ℤ)+1) (R.force M) := by
  have he (x : CoverConfig G → Snap G d) (hx : Affordable S 1 x) : Affordable S (j+1:ℤ) (Tensor.diagonal M ∘ x) := by
    convert Affordable.multilinear (fun _ : Fin (j+1) => x) (fun _ => 1) (fun _ => hx) M using 1
    simp
    rfl
  exact (he _ (R.guess_affordable f)).sub (he _ ((R.guess_affordable f).sub (R.gap_affordable f)))

lemma compression_affordable : Affordable S ((j:ℤ)-1) (R.compression M) := by
  refine Affordable.sum _ (fun (e : R.edg) => divergence e.val (R.coField M e)) (fun e _ => ?_)
  unfold divergence; refine Affordable.sum _ _ (fun i _ => ?_)
  change Affordable S _ (slope e.val (dirs G i) fun U => R.coField M e U (dirs G i))
  exact ((R.coField_affordable f M e).postcomp (ContinuousLinearMap.apply ℝ ℂ (dirs G i))).budget_slope
    (R.fitsAt_edge f e).1 (dirs G i) ((dirs G).norm_eq_one _).le

omit f in
lemma force_gauge (h : covariantTensor M) : GaugeInvariant (R.force M) := by
  intro t U; rw [R.force_eq, R.force_eq]; apply Finset.sum_congr rfl
  intro i _; rw [euler_gauge]; exact R.coField_gauge M h i _ t U

lemma compression_gauge (h : covariantTensor M) : GaugeInvariant (R.compression M) := by
  intro t U; unfold compression; apply Finset.sum_congr rfl
  intro i _; exact divergence_gauge _ (R.coField_gauge M h i) (fun V =>
    (((R.coField_affordable f M i).smooth_cover_slide (R.fitsAt_edge f i).1 V).differentiable (by simp) 0)) t U

variable {n : Side}

theorem equation_at (β : ℝ) (hn : FitsIn S n) (o : Site n) (e : R.edg) (U : Config G n) :
    places o (equation β e.val (R.coField M e)) U = equation β (edgeAt e.val o) (places o (R.coField M e)) U := by
  have ht : euler (expandAt o U) e.val=euler U (edgeAt e.val o) := euler_at ..
  dsimp only [equation,places, Function.comp_apply]; rw [ht]; apply congrArg (fun c : ℂ => _ - (β:ℂ)⁻¹ * c)
  unfold divergence
  apply Finset.sum_congr rfl; intro i _
  let a := dirs G i
  have hc := (R.coField_affordable f M e).postcomp (ContinuousLinearMap.apply ℝ ℂ a)
  exact (congrFun (slopes_at hc.uses hn o (R.fitsAt_edge f e).1 a) U).symm

/-- All spectators can be in `P`, even with no differentiability assumed
for them. Exact on the full torus measure. Need `$β\ne0$`; callers supply
positive running coupling when used through the sequence. -/
theorem unpaid_null (β : ℝ) (h : β ≠ 0) (P : Config G n → ℂ) (hp : Envelope P) (hn : FitsIn S n)
    (o : Site n) (hz : ∀ (e : R.edg) (a) (U : Config G n), P (slide (edgeAt e.val o) U a) = P U) :
    moment β (fun U => places o (R.unpaid M β) U * P U) = 0 := by
  let X (e : R.edg) := places o (R.coField M e)
  have he (e : R.edg) (i : G.ColorIndex) :=
    ((R.coField_affordable f M e).postcomp (ContinuousLinearMap.apply ℝ ℂ (dirs G i))).fitsFlow
      (dirs G i) ((dirs G).norm_eq_one i).le hn (R.fitsAt_edge f e).1 o
  have hq (U : Config G n) : places o (R.unpaid M β) U * P U =
      ∑ e : R.edg, equation β (edgeAt e.val o) (X e) U * P U := by
    rw [← Finset.sum_mul, places, Function.comp_apply,R.unpaid_eq]; refine congrArg (fun x : ℂ => x*P U) ?_
    exact Finset.sum_congr rfl fun e _ => R.equation_at f M β hn o e U
  unfold moment; simp_rw [hq]; rw [integral_finsetSum]; refine Finset.sum_eq_zero fun e _ => ?_
  · exact ward_null (X:=X e) (he e) β h hp (hz e)
  exact fun e _ => bound_int (bound_product (equation_bounded (e:=edgeAt e.val o) (X:=X e) (he e) β) hp) _
end Rays
end YM.WardBin
