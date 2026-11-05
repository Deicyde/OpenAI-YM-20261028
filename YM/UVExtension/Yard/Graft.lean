import YM.UVExtension.Yard.Branch
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Yard
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Finset
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration WilsonStartup Residual Averaging Geo
open Lamppost Concert
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint} {P : Listing G n} {X:Support n} {D Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y} {σ C Λ b c : ℝ}
    (a:D→ Collection.Source G n)
    (K : PathData G)(v:Clip)
variable (hG : G.Simple) (F:Atlas (fork p G P.reg (preExponent p)) M (fun d=>trill p G P.reg (preExponent p) (a d).logRead) (fun _=>b))
    (H:∀ d,smoothP p P.reg (a d).logRead)

variable {A:Collection.Source G n}
    (hv:Decent v p)(hK: K.Bounds v σ C Λ)(he: Geo.Width p v σ)
include hv hK he hG
variable (x:ℝ) (hb:0≤b)
omit hv hK he hG
def vacant (G:Gauge)(n:Side): Collection.Source G n := ⟨fun _=>0,fun _=>0⟩
lemma vacant_cost : (fork p G P.reg (preExponent p)).MeasureP (trill p G P.reg (preExponent p) (vacant G n).logRead) 0 := by
  apply (fork_earns (G:=G) P.reg _).2; exact ⟨fun _=>0,fun i=> sup_le (sup_const _) abs_zero.le,fun i=> by simp [SumBudget]⟩
lemma vacant_norm:smoothP p P.reg (vacant G n).logRead := fun _=>CouplingShape.reg_const _
lemma vac_proj {d : RegularAddress n} (i j : PlaqAxes): projection d (fun _:Config G n=> (0:ℝ)) i j=0:=by
  unfold projection; split; next h=> exact hessian_zero 0 _ _
  exact rfl
lemma vac_delta : delta (P.read (vacant G n))=0:= by
  unfold Averaging.delta Averaging.total censusAt; simp_rw [show ∀ i, projection ((P.read (vacant G n)).reg i) ((P.read (vacant G n)).E i) axes01 axes01=0 from fun _=> vac_proj axes01 axes01,ite_self,tsum_zero]
lemma proud (a:Collection.Source G n) :
    let Y:= branch P K v p (vacant G n) x
    let Z:= branch P K v p a 0
    let X:= branch P K v p a x
    (∀ i,X.regular i=Y.regular i+Z.regular i)∧∀ i U,X.logarithm i U=Y.logarithm i U+Z.logarithm i U:=by
  intro Y Z X
  let t:= delta (P.read a); let g:= (vacant G n); have he: delta (P.read g)=0:= vac_delta
  constructor
  · intro i; funext U
    suffices h:∀ i, archive P K v a x t i U= archive P K v g x (delta (P.read g)) i U+archive P K v a 0 t i U from h (numbering (EKey n) i)
    rw [he]; rintro (i|i|i)
    · have hz(g':Pot G n)(h:g'=0):rebate (P.reg i) g' =0:=by rw [h]; ext V; unfold rebate payout counter quad; simp_rw [show ∀ j k, projection (P.reg i) (0:Config G n→ℝ) j k = 0 from fun _ _=> vac_proj ..]; simp
      simp_rw [archive,Sum.elim,hz _ (show g.logRead i=0 from rfl)]; simp
    · simp [archive,Low.fresh]
    simp [archive,High.fresh]; ring
  intro i U
  suffices h: ∀ i, loses P K v p a x t i U=loses P K v p g x (delta (P.read g)) i U+loses P K v p a 0 t i U from h _
  rw [he]; rintro (i|i); swap; · simp_rw [loses, Sum.elim,comp_apply,Low.loan]; split_ifs <;> ring
  have hz(g':Pot G n)(h:g'=0):fault (P.reg i) g' p.threshold=0:=by rw [h]; ext V; unfold fault payout counter quad; simp_rw [show ∀ j k, projection (P.reg i) (0:Config G n→ℝ) j k = 0 from fun _ _=> vac_proj ..]; split_ifs <;> simp
  simp [loses,hz _ (show g.logRead i=0 from rfl)]
variable (P)
include hv hK he hG
lemma roughL {A:Collection.Source G n} (h:smoothP p P.reg A.logRead)(hp:(fork p G P.reg (preExponent p)).MeasureP (trill p G P.reg (preExponent p) A.logRead) b): let t:= branch P K v p A 0; let Y:=shelves P K p
    (fork p G Y.reg p.supportExponent).MeasureP (trill p G Y.reg p.supportExponent t.regular) (regularNeed G p v σ C 0 1*b)∧
    (softer Y p.B (p.supportExponent+1)).MeasureP (fun i u=> t.logarithm i u) (softNeed G p v σ C 0 1*b):=by
  intro t Y
  rw [show regularNeed G p v σ C 0 1*b= regularNeed G p v σ C 0 b from (by unfold regularNeed; rw [abs_zero]; ring), show softNeed G p v σ C 0 1*b= softNeed G p v σ C 0 b by unfold softNeed hitNeed softReset Push.AbsoluteSums.Footprint.payment Footprint.degreeIncome; rw [abs_zero]; ring]
  exact (switch K v hG hv hK he 0 h hp).2

include P
lemma priceL:0≤regularNeed G p v σ C 0 1∧0 ≤ softNeed G p v σ C 0 1:=by
  let f:=vacant G n
  have hz := vacant_cost (P:=P) (p:=p); obtain ⟨a,ha,hb⟩:= hz.afloat
  have hx : Meter.MeasureP (fork p G P.reg (preExponent p)) (trill p G P.reg (preExponent p) f.logRead) 1:= ⟨_, ha,fun i=> budget_loosen (hb i) (zero_le_one: (0:ℝ)≤1)⟩
  have H:= switch K v hG hv hK he 0 (vacant_norm (P:=P)) hx
  obtain ⟨_,_,h⟩:=(H.2.1).afloat; obtain ⟨_,_,h'⟩:= H.2.2.afloat; exact ⟨budget_nonneg (h 0),budget_nonneg (h' 0)⟩

include H F hb
lemma evens : let X:= shelves P K p; let Y d:= branch P K v p (a d) 0
    Nonempty (ticketR M p X.reg p.supportExponent (fun i=> (Y i).regular) (fun _=>4*regularNeed G p v σ C 0 1*b)) ∧ Nonempty (Atlas (softer X p.B (p.supportExponent+1)) M (fun d i u=> (Y d).logarithm i u) (fun _=>4*softNeed G p v σ C 0 1*b)):=by
  intro X Y
  let f := fork p G P.reg (preExponent p); let g:= fork p G X.reg p.supportExponent; let K':=softer X p.B (p.supportExponent+1)
  have hs i: smoothP p X.reg (Y i).regular:= (switch K v hG hv hK he 0 (H i) (truth a F i)).1
  have ht:= priceL P K v hG hv hK he
  have hΨ z (_:z∈M.span): 0≤b ∧ b≤ b:=⟨hb,le_rfl⟩
  constructor
  · apply Atlas.apply_to _ F hΨ hb ht.1; intro S w m hm h
    obtain ⟨f,hf,hV⟩:= (Concert.raises _ _ S w _ H).1 h
    have hu := (fork_earns (p:=p) P.reg (terms a S w).logRead).2 ⟨f,hf,hV⟩; let t:= terms a S w; have hL:= blasts P.reg _ S w H
    have he' := linear a K v hG F H S w (projects_ledger (a:=terms a S w) hL hu)
    have hp0:(branch P K v p t 0).regular=plaits S w (fun i=> (Y i).regular):= funext (he'.1)
    have hT : g.MeasureP _ _:= (roughL P K v hG hv hK he hL hu).1
    rw [hp0] at hT; exact (Concert.raises _ _ S w _ hs).2 ((fork_earns ..).1 hT)
  apply Atlas.apply_to _ F hΨ hb ht.2; intro S w m hm h
  obtain ⟨f,hf,hV⟩:= (Concert.raises _ _ S w _ H).1 h
  have hu := (fork_earns (p:=p) P.reg (terms a S w).logRead).2 ⟨f,hf,hV⟩; let t:= terms a S w; have hL:= blasts P.reg _ S w H
  have hp := linear a K v hG F H S w (projects_ledger (a:=terms a S w) hL hu)
  obtain ⟨a,ha,hh⟩:= (roughL P K v hG hv hK he hL hu).2.afloat
  exact ⟨_,fun i=> ⟨(ha _).1,fun V=> by simpa only [hp.2 i V] using! (ha i).2 V⟩,hh⟩
end YM.UVExtension.Yard
