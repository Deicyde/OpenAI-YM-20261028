import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pygmy
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
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
private lemma delete_has {s : Type*} [DecidableEq s] {p : Finset s} {V : Finset s} {f : s} (h : f∈p) (hp : f ∈ V) (he : p.erase f= V.erase f):p=V:= by rw [← insert_erase h,he, insert_erase hp]
-- support cost map ages all. root always within marked supports.
def crowns {i : Type*} [DecidableEq i] (X : i→ℝ) (v : ℝ) (p:i) : Finset i → ℝ:=fun F=> if p∈F then v*∏ i∈ F.erase p,X i else 0
lemma crowns_has {i:Type*} [DecidableEq i] {X:i→ℝ} (v : ℝ) (p:i) (he : Summable X) (hp : ∀ i,0≤X i) : Summable (crowns X v p):=by
  have hh : Summable (fun k:{a:Finset i|p∈a} => crowns X v p k.val) := ?_
  · have hz : Function.support (crowns X v p) ⊆ {a|p∈a} := fun i hi=> by by_contra ht; exact hi (by simp only [crowns,if_neg (show p∉i from ht)])
    exact ((hasSum_subtype_iff_of_support_subset hz).mp hh.hasSum).summable
  let A:= fun k:{i:Finset i|p∈i}=> k.val.erase p
  have h : Summable (fun i=>∏ j∈ A i,X j) := (summable_finsetProd_of_summable_nonneg hp he).comp_injective
    (fun a b hg=> Subtype.ext (delete_has a.property b.property hg))
  apply Summable.congr (h.mul_left v); intro s; exact (if_pos s.property).symm

-- Sum over lists where mark erased and reconstruct regular.Return.at.K
variable (H:Cash W X.x μ L Q o C T R) (hk:X.width=o.K) (ht:X.manifest)
include H hk ht
lemma tons (Y : Finset (Stores S)) (hy : Layout X.seeds Q.halo X.B Y) (z : Air f G):
    HasSum (fun t : ListsAt c f=> M.premium X W o.a Q.table k Q.halo z (issue Y k t)) (M.salary X k W o.a Q.table Y z):=by
  let i t:= issue Y k t; let a:= M.turn.badge S; let F t:= M.premium X W o.a Q.table k Q.halo z (i t)
  let U:= X.liftA R.beta z; let w:=M.paidU X o.a U; change HasSum F _
  cases hx:M.turn with
  | logKey p=>
    have hA : a= .inr (.inr (.inl (.inl (.inl p)))):=by unfold a; rw [hx]; rfl
    have he p' : R.activities.regularOccurrence R.p p p'=0:=by
      by_cases h:Healthy R.p.threshold (R.activities.reg p).support p' <;> simp [Activities.regularOccurrence,h, show R.activities.E p=0 from (by simpa only [hx,Wing.blank] using M.blank)]
    have hc : X.vertex R Q.table W o.a k Q.halo z a=0:=by
      rw [hA]; change Real.exp (-R.activities.regularOccurrence R.p p _ * _)-1=0
      rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
    let Q₁:= (Sum.inl (Sum.inl p):LogIndex c f)
    let g(t:ListsAt c f):= X.term R Q.table W o.a k Q.halo z (i t)
    have hG (s): a∈i s↔Q₁ ∈ s.2:= by rw [hA]; simp [i,issue,Q₁]
    have hM t (ht:Q₁ ∈ (t:ListsAt c f).2) : w*g t=0 :=by rw [show g t=0 from prod_eq_zero ((hG t).2 ht) hc,mul_zero]
    let T0:= {s: ListsAt c f | Q₁ ∉ s.2}
    let j(x : T0):ListsAt c f:=(x.val.1,insert Q₁ x.val.2)
    have hZ (x:T0) : i (j x)=insert a (i x.val):=by rw [hA]; ext t; rcases t with t|t|t|t <;> simp [i,j,Q₁,issue]
    have hz (x:T0): (i (j x)).erase a=i x.val:=by rw [hZ, erase_insert ((hG x.val).not.mpr x.prop)]
    have hp: Injective (i):=by
      rintro ⟨x,y⟩ ⟨z,w⟩ hh; have he: _ := congr_arg (fun x:Molecule S => (x.toRight.toRight.toRight,x.toRight.toRight.toLeft)) hh; simpa only [i,issue,toRight_disjSum,toLeft_disjSum] using he
    have hu: Injective j:=fun x y (h:j x=j y)=> Subtype.ext (hp ((hz x).symm.trans (h.symm ▸ hz y)))
    have ht : M.salary X k W o.a Q.table Y z=w*X.summedUp R Q.table W o.a z k Y :=by unfold salary comfortP summedUp; simp only [hx,Wing.Occupied,Wing.remaining,if_true,w,U]; ring
    rw [ht]; apply (hu.hasSum_iff (f:=F) ?_).1
    · have hg (x:T0): F (j x)=w*g x.val:=by
        unfold F premium; rw [if_pos (show M.turn.badge S∈i _ from (hG _).2 (mem_insert_self ..)), show (i (j x)).erase _= _ from hz x]
      convert! (hasSum_subtype_iff_of_support_subset (s:=T0) (fun i (hi:w*g i≠0)=> show i∈T0 from fun h=>hi (hM _ h))).2 ((luxury X k H hk ‹_› hy z).mul_left w) using 1; exact funext hg
    intro x hx; unfold F premium; apply if_neg; intro H
    have ht := (hG _).1 H; let z: T0:=⟨(x.1,x.2.erase Q₁),show Q₁ ∉ x.2.erase Q₁ from Finset.notMem_erase _ _⟩; exact hx ⟨z,Prod.ext rfl (insert_erase ht)⟩
  | gasKey p=>
    have hA : a= .inr (.inl p):=by unfold a; rw [hx]; rfl
    have hg t : a∈i t↔p∈k:=by rw [hA]; simp [i,issue]
    unfold salary comfortP; simp only [hx,Wing.Occupied,Wing.remaining]; split_ifs with hf
    swap; · rw [show F=0 from funext (fun t=> if_neg (show M.turn.badge S∉i t from (hg _).not.mpr hf)),mul_zero,zero_mul,zero_mul]; exact hasSum_zero
    let A := ∏ B∈Y, X.Pack R Q.table k W o.a B U
    let B := ∏ i∈k.erase p,X.bag R o.a U i
    let f' (t : Finset (WarningAt c f)) := ∏ i∈t,X.detect U W o.a R k i
    let C' := Real.exp (∑' j,X.farLog R o.a Q.table z j)
    have h := (expense_series H X rfl hk ht z).2.2
    have hZ(t : ListsAt c f) : F t = f' t.1*(w*A*B)*(∏ i∈t.2,X.raiseAir R o.a Q.table z i) :=by
      have he : (i t).erase a=issue Y (k.erase p) t :=by
        rw [hA]; ext z; rcases z with z|z|z|z <;> simp [issue,i]
      have ht l (hl : l∈Y) : X.vertex R Q.table W o.a k Q.halo z (.inl l) = X.Pack R Q.table k W o.a l U := if_pos (hy.checkpoints _ hl)
      unfold F premium; rw [if_pos (show M.turn.badge S∈i _ from (hg t).2 hf),he]; unfold Coat.term issue; simp only [prod_disjSum]; rw [show (∏ i∈Y,X.vertex R Q.table W o.a k Q.halo z (.inl i))=A from prod_congr rfl ht]
      unfold f' B w U; simp only [vertex,Sum.elim]; ring
    have hp : (∏ i : WarningAt c f,(1+X.detect U W o.a R k i))=∑ t,f' t:= _root_.Finset.prod_one_add _
    convert Raw.finite_start F (fun i=> f' i*(w*A*B)*C') (fun i => (h.mul_left (f' i*(w*A*B))).congr_fun (fun j=> (hZ (i,j)))) using 1
    rw [hp,← Finset.sum_mul,← Finset.sum_mul]; unfold f' w A B C' U; ring

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
  let b:= crowns H.text M.weight (M.turn.badge S)
  have he: Summable b := crowns_has M.weight _ hp H.positive
  have hh t : Integrable (u t) D:= (hm t).2.1
  have hz:= Summable.of_nonneg_of_le (fun t=> integral_nonneg (μ:=D) (show 0 ≤ fun v=> ‖u t v‖ from fun _=>norm_nonneg _)) (fun t=> (hm t).2.2) (he.comp_injective (issue_injective Y k))
  have hl g : ∑' j,u j g=f' g := (M.tons (X.wrapY g.1) k H hk ht Y hy g.2).tsum_eq
  have hA : Summable (fun t=> crowns H.fair M.weight (M.turn.badge S) (issue Y k t)):= (crowns_has M.weight _ H.fair_summable H.fair_price).comp_injective (issue_injective Y k)
  have hD: Dominated u := by
    refine ⟨_,hA,fun t i=>?_⟩
    unfold crowns; split
    next ha=>
      let A':= issue Y k t; unfold u into premium; rw [if_pos ha, norm_mul]; exact mul_le_mul ((M.coin (X.wrapY i.1) o.a _ )) (H.every X rfl hk ht k _ i.1 i.2) (norm_nonneg _) M.profit
    next ha=> unfold u into premium; rw [if_neg ha,norm_zero]
  rw [← funext hl]; exact ⟨(show Envelope _ from (⟨Measurable.tsum (f:=u) (fun i=> (hm i).1.meas),hD.bound⟩:Envelope (fun i=>∑' t, u t i))).integrable _,hasSum_integral_of_summable_integral_norm hh hz⟩
end Leaf
end YM.PhysicalNext.Repeat.Lotus
