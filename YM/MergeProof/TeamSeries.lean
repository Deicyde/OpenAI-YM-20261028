import YM.MergeProof.TeamPygmy
/-! # Mark to ReceiptM one-choice per Molecule. Blank read by occupancy, no support cuts. Includes summability exact. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)

def index (s : Side) : Finset (LogIndex s f):= M.logs.image (fun i=> Sum.inl (Sum.inl i))
lemma sign_spell : M.signs S=issue (S:=S) ∅ M.gasDue (∅,M.index c):=by
  let B:=issue (S:=S) ∅ M.gasDue (∅,M.index c)
  apply Finset.Subset.antisymm
  · intro p hp; obtain ⟨j,hj,rfl⟩:=mem_image.mp hp
    cases h:j.turn with
    | logKey i=> simp only [Wing.badge,issue,inr_mem_disjSum,inl_mem_disjSum]; exact mem_image.mpr ⟨_,M.sent _ |>.2 ⟨_,hj,h⟩,rfl⟩
    | gasKey i=> simp only [Wing.badge,issue,inr_mem_disjSum,inl_mem_disjSum]; exact (M.asked _).2 ⟨_,hj,h⟩
  intro p hp; rcases p with p|p|p|p <;> simp only [issue,inr_mem_disjSum,inl_mem_disjSum] at hp
  · exact False.elim (notMem_empty p hp)
  · obtain ⟨j,hj,h⟩:= (M.asked _).1 hp; exact mem_image.mpr ⟨_,hj,(congr_arg (·.badge S) h).trans rfl⟩
  · obtain ⟨i,hi,rfl⟩:= mem_image.mp hp; obtain ⟨j,hj,h⟩:= (M.sent _).1 hi; exact mem_image.mpr ⟨_,hj,(congr_arg (·.badge S) h).trans rfl⟩
  exact False.elim (notMem_empty p hp)
lemma spells (Y: Finset (Stores S)) (t:ListsAt c f) : M.signs S ⊆ issue Y k t ↔ M.gasDue ⊆ k ∧ M.index c ⊆ t.2:=by
  rw [M.sign_spell]; simp only [issue, disjSum_subset,toLeft_disjSum,toRight_disjSum, empty_subset,true_and,and_true]

variable (H:Cash W X.x μ L Q o C T R) (hk:X.width=o.K) (ht:X.manifest)
include H hk ht
lemma tons (Y : Finset (Stores S)) (hy : Layout X.seeds Q.halo X.B Y) (z : Air f G):
    HasSum (fun t : ListsAt c f=> M.premium X W o.a Q.table k Q.halo z (issue Y k t)) (M.salary X k W o.a Q.table Y z):=by
  let i t:= issue Y k t; let a:= M.signs S; let F t:= M.premium X W o.a Q.table k Q.halo z (i t)
  let U:= X.liftA R.beta z; let w:=M.paidU X o.a U; change HasSum F _
  let A:= ∏ B∈Y,X.Pack R Q.table k W o.a B U
  let B:=∏ i∈k\M.gasDue,X.bag R o.a U i
  let f' (t : Finset (WarningAt c f)) := ∏ i∈t,X.detect U W o.a R k i
  let g(t : ListsAt c f) := f' t.1*(w*A*B)*(∏ i∈t.2,X.raiseAir R o.a Q.table z i)
  let C' := Real.exp (∑' j,X.farLog R o.a Q.table z j)
  by_cases hv:M.gasDue ⊆ k
  swap; · rw [show F=0 from funext (fun t=> if_neg (show ¬M.signs S⊆ i t from fun h=>hv (((M.spells ..).1 h).1))), show M.salary X k W o.a Q.table Y z=0 from (by unfold salary comfortP; dsimp only; rw [if_neg hv]; ring)]; exact hasSum_zero
  have h0 (t:LogIndex c f)(hp:t∈ M.index c): X.raiseAir R o.a Q.table z t=0:=by
    obtain ⟨u,h,rfl⟩:= mem_image.mp hp; obtain ⟨j,hj,hy⟩:= (M.sent _).1 h
    have he p' : R.activities.regularOccurrence R.p u p'=0:=by
      by_cases h:Healthy R.p.threshold (R.activities.reg u).support p' <;> simp [Activities.regularOccurrence,h, show R.activities.E u=0 from (by simpa only [hy,Wing.blank] using j.blank)]
    change Real.exp (-R.activities.regularOccurrence R.p u _ * _)-1=0; rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
  have h : HasSum g (M.salary X k W o.a Q.table Y z):= by
    convert Raw.finite_start g (fun i=> f' i*(w*A*B)*C') (fun i => ((expense_series H X rfl hk ht z).2.2.mul_left (f' i*(w*A*B)))) using 1
    have hp : (∏ i : WarningAt c f,(1+X.detect U W o.a R k i))=∑ t,f' t:= _root_.Finset.prod_one_add _
    unfold salary comfortP; dsimp only; rw [if_pos hv]; rw [hp,← Finset.sum_mul,← Finset.sum_mul]; unfold f' w A B C' U; ring
  let T₀:= {t: ListsAt c f | Disjoint t.2 (M.index c)}
  let j(t : T₀): ListsAt c f:= (t.val.1,t.val.2 ∪ M.index c)
  have hp(t:T₀) : M.signs S⊆ i (j t):= (M.spells ..).2 ⟨hv,subset_union_right⟩
  have hT(t:T₀) : (j t).2\ M.index c=t.val.2:=by
    ext z
    simp only [j,Finset.mem_sdiff,Finset.mem_union]; constructor; · grind
    intro hz; exact ⟨Or.inl hz,fun h=>disjoint_left.mp t.prop hz h⟩
  have hi:Injective j:=fun x y hh=>Subtype.ext (Prod.ext (show (j x).1=(j y).1 from congr_arg Prod.fst hh) ((hT x).symm.trans ((congr_arg (fun (t:ListsAt c f)=> t.2\M.index c) hh).trans (hT y))))
  apply (hi.hasSum_iff (f:=F) ?_).1
  · refine ((hasSum_subtype_iff_of_support_subset (s:=T₀) ?_).2 h).congr_fun ?_
    · intro i (hv:g i≠0); change Disjoint _ _; apply disjoint_left.mpr; intro z hz hy; exact right_ne_zero_of_mul hv (prod_eq_zero hz (h0 _ hy))
    intro t
    have he : i (j t) \ M.signs S=issue Y (k\M.gasDue) t.val:=by
      rw [M.sign_spell]; ext z; rcases z with z|z|z|z <;> simp only [issue,i,Finset.mem_sdiff,inl_mem_disjSum,inr_mem_disjSum,notMem_empty,and_true,not_false_eq_true] -- edit
      · have ht:=Finset.ext_iff.mp (hT t) z; simpa only [Finset.mem_sdiff] using ht
      rfl
    have h l (hl : l∈Y) : X.vertex R Q.table W o.a k Q.halo z (.inl l) = X.Pack R Q.table k W o.a l U := if_pos (hy.checkpoints _ hl)
    unfold Function.comp F premium; rw [if_pos (hp t),he]; unfold Coat.term issue; simp only [prod_disjSum]; rw [show (∏ i∈Y,X.vertex R Q.table W o.a k Q.halo z (.inl i))=A from prod_congr rfl h]
    unfold g f' B w U; simp only [vertex,Sum.elim]; ring
  intro t ht; unfold F premium; apply if_neg; intro hF
  have hx := ((M.spells ..).1 hF).2; let z:T₀:=⟨(t.1,t.2\ M.index c),show Disjoint (t.2 \ M.index c) (M.index c) from disjoint_sdiff_self_left⟩; exact ht ⟨z, Prod.ext rfl (sdiff_union_of_subset hx)⟩

omit H hk ht in
private lemma issue_injective (Y : Finset (Stores S)) (k : Finset ℕ) : Injective (issue Y k) := by
    intro x y h
    apply Prod.ext; · simpa [issue,blaze] using congr_arg blaze h -- unfold
    simpa only [issue,toRight_disjSum,toLeft_disjSum] using congr_arg (fun z:Molecule S=>z.toRight.toRight.toLeft) h
lemma tithes (Y : Finset (Stores S)) (hy : Layout X.seeds Q.halo X.B Y) :
    let D:= (F.order G).prod X.dice; let f(g:F.Slice G×Air f G) := M.salary (X.wrapY g.1) k W o.a Q.table Y g.2
    Integrable f D ∧ HasSum (fun t=> ∫ g, M.into X W o.a Q.table k Q.halo (issue Y k t) g ∂D) (∫ g,f g ∂D):=by
  intro D f'; let u(t:ListsAt c f):= M.into X W o.a Q.table k Q.halo (issue Y k t)
  have hm t:= M.tip X k H hk ht (issue Y k t)
  have hp:Summable H.text:= Summable.sum _ (hasSum_fintype _).summable (budgets_arr H)
  let b:= crowns H.text M.weight (M.signs S)
  have he: Summable b := crowns_has M.weight _ hp H.positive
  have hh t : Integrable (u t) D:= (hm t).2.1
  have hz:= Summable.of_nonneg_of_le (fun t=> integral_nonneg (μ:=D) (show 0 ≤ fun v=> ‖u t v‖ from fun _=>norm_nonneg _)) (fun t=> (hm t).2.2) (he.comp_injective (issue_injective Y k))
  have hl g : ∑' j,u j g=f' g := (M.tons (X.wrapY g.1) k H hk ht Y hy g.2).tsum_eq
  have hA : Summable (fun t=> crowns H.fair M.weight (M.signs S) (issue Y k t)):= (crowns_has M.weight _ H.fair_summable H.fair_price).comp_injective (issue_injective Y k)
  have hD: Dominated u := by
    refine ⟨_,hA,fun t i=>?_⟩
    unfold crowns; split
    next ha=>
      let A':= issue Y k t; unfold u into premium; rw [if_pos ha, norm_mul]; exact mul_le_mul ((M.coin (X.wrapY i.1) o.a _ )) (H.every X rfl hk ht k _ i.1 i.2) (norm_nonneg _) M.profit
    next ha=> unfold u into premium; rw [if_neg ha,norm_zero]
  rw [← funext hl]; exact ⟨(show Envelope _ from (⟨Measurable.tsum (f:=u) (fun i=> (hm i).1.meas),hD.bound⟩:Envelope (fun i=>∑' t, u t i))).integrable _,hasSum_integral_of_summable_integral_norm hh hz⟩
end Team
end YM.PhysicalNext.Repeat.Lotus
