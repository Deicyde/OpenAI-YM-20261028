import YM.FullVolume.Rank.Wind
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Rank
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune Finset
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι:Type}
-- transport audition and reproject onto common seats.stage after Keep.H price.H.T.
local notation "R"=> S.orient
namespace Hue
variable {P Q:ℕ→ Coefficient F n}(h:Hue P Q A S)
variable {D E: Rep G n}(m:Motion) (x:D.activities.Moves m.1 0)
abbrev burn (P:Coefficient F n): (ℕ→Support n)×(ℕ→ Config G n→ℂ) := (P.support,P.regular)
lemma audits (p:Coefficient F n)(y: E.activities.Moves m.1 0) : burn (audition x p)=burn (audition y p)∧ (audition x p).x=(audition y p).x:=by unfold audition; split<;>exact ⟨rfl,rfl⟩
private lemma stall (m:Motion): Tendsto (Motion.patch F m) (𝓝 (0:F.Coeff)) (𝓝 0):=by
    unfold Motion.patch; split;next h=>
       have hv : Continuous (fun i=> star (F.act m.1.ortho i)):= continuous_star.comp (F.act m.1.ortho).continuous_of_finiteDimensional
       simpa using hv.tendsto 0
    next h=> simpa using ((F.act m.1.ortho).continuous_of_finiteDimensional.tendsto (0:F.Coeff))
lemma priceU (m:Motion)(x:S.orient.activities.Moves m.1 0){P:Coefficient F n} (T:SectionData F)(hS:T.Sound A)(hx:n.val≥2)(h:P.Format 0 A R){v:ℝ}(hp:P.remBound 0 R S.k v): let Q:= audition x P
    Q.Format 0 A R∧ Q.remBound 0 R S.k (turnCost (R).p.order (R).p.power *v)∧ Q.x=Motion.patch F m P.x:=by
    intro Y; obtain ⟨a,b,hT,hq⟩:= rem_tabs.mp hp; obtain ⟨hw,hv,hB,-⟩:= audition_receipt _ x hx hS h hT
    let w:= turnCost (R).p.order (R).p.power; have hh:1 ≤ w:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ one_le_two)); refine ⟨hv,hB.bound ?_,hw⟩; change w*a+b ≤ _; exact (add_le_add_right (le_mul_of_one_le_left hT.second hh) _).trans ((mul_add w a b).symm.trans_le (mul_le_mul_of_nonneg_left hq (zero_le_one.trans hh)))
include h
lemma rhythm (m:Motion)(x:S.orient.activities.Moves m.1 0)(T:SectionData F)(hS:T.Sound A)(hx:n.val≥2): Hue (fun i=> audition x (P i)) (fun i=>audition x (Q i)) A S:=by
    let z i:=breakP (P i) (Q i)
    have hv(i): (audition x (z i)).x=Motion.patch F m (z i).x:=by unfold audition Motion.patch;split<;> rfl
    have he i: audition x (z i)=breakP (audition x (P i)) (audition x (Q i)) := turn_br ..
    let w:=turnCost (R).p.order (R).p.power; have hp:0 < w:=pow_pos (by positivity) _
    refine ⟨fun i=> turn_same _ _ _ x (h.same i),?_,fun i=>?_, fun v hv=> (h.sent (v/w) (div_pos hv hp)).mono fun i hi=>?_⟩
    · exact ((stall m).comp h.reads).congr' (Eventually.of_forall fun i=> (hv i).symm.trans (congr_arg Coefficient.x (he i)))
    · let y:= h.turns i; have hx:=format_reorient x y hx; rw [show affine m.1 (0:Site n) 0=0 from (by simp [affine])] at hx; rw [← he]; unfold audition; split; exact format_barAll hx;exact hx
    rw [← he]; exact rem_mono ((priceU m x T hS hx (h.turns i) hi).2.1) (le_of_eq (by change w* (v/w)=v; field_simp))
-- finite-pencil on Hue
omit h
lemma multiple {P Q:ℕ→ι→ Coefficient F n}[Fintype ι][Nonempty ι](q:F.Coeff →ₗ[ℂ] ι→ℂ)(v:F.Coeff)(hp:∀ i,Hue (fun n=>P n i) (fun n=> Q n i) A S) :Hue (fun n=> pencil (code _) (P n) q v) (fun n=>pencil (code _) (Q n) q v) A S:=by
    let f n j:= breakP (P n j) (Q n j); let U n:= pencil (code _) (f n) q v; have he n : U n= breakP (pencil (code _) (P n) q v) (pencil (code _) (Q n) q v):= pencil_br ..
    refine ⟨fun n=> funext (fun i=>congr_fun ((hp ((code _) i|>.1)).same n) ((code _) i|>.2)),?_ ,fun i=> he i ▸ merge_format _ _ (fun j=> stretch_format _ ((hp j).turns i)),fun b hb=>?_⟩
    · simp_rw [pencil_x,← Finset.sum_sub_distrib,← smul_sub]; simpa only [Finset.sum_const_zero] using tendsto_finsetSum (a:=fun _=> (0:F.Coeff)) Finset.univ (fun i _=> by simpa only [smul_zero] using! ((hp i).reads.const_smul (q v i)))
    let R':= ∑ i, ‖q v i‖; have hh:0 ≤ R':= Finset.sum_nonneg fun i _=> norm_nonneg _; let c:=b/(R'+1); have hv:0<c:=div_pos hb (by linarith)
    filter_upwards [eventually_all.mpr fun i=>(hp i).sent _ hv] with t ht
    rw [← he]; refine rem_mono (pencil_cost (code _) (f t) q S.sane (X:=fun _=>c) (fun i=> ⟨(hp i).turns t,ht i⟩) v).2 ?_
    rw [← sum_mul]; change R'*c≤_; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hv.le).trans_eq (by unfold c; field_simp)
-- Board with fixed Keeper equivalent.Shifting presentations.O.Develop output.L step.S. can use Gauge.E renormal.Tore. needAlong
lemma projector {R' R'':Rep G n}(h: Along R' R'')(P:Coefficient F n){s t:ℝ}(p:P.remBound 0 R' s t): profile R'.activities P.forced= profile R''.activities P.forced:=by unfold profile barcode; rw [h.force]
lemma drones {R' R'':Rep G n}(h:Along R' R'')(P:Coefficient F n)(m:Motion)(x:R'.activities.Moves m.1 0)(y:R''.activities.Moves m.1 0){s t:ℝ}(p:P.remBound 0 R' s t):
    profile R'.activities (audition x P|>.forced)= profile R''.activities (audition y P|>.forced):=by
    rw [foyer _ _ _ _,foyer _ _ _ _]; exact congr_arg (floatUp m 0) (projector h _ p) -- χ helper
-- compare acted+true Pencil
section visible
variable {p q:ι→ Coefficient F n} [Fintype ι] [Nonempty ι] (x:F.Coeff →ₗ[ℂ] ι→ℂ)(v:F.Coeff){D E:Rep G n}
local notation "P'"=> pencil (code _) p x v
local notation "Q'"=> pencil (code _) q x v
lemma matching (_h:Along D E) (hb:Keeper D.p D.activities)(ha:Keeper E.p E.activities)(hx:cart hb=cart ha)(hp:∀ i,burn (p i)= burn (q i))(he:∀ i,profile D.activities (p i).forced= profile E.activities (q i).forced)(hA:∀ i,∃ v,(p i).remBound 0 D S.k v)(hy:∀ i,∃ v,(q i).remBound 0 E S.k v):capture P' hb=capture Q' ha:=by
    have hr: burn P'=burn Q':=by
       have hK(p:ι→ Coefficient F n)(i): (pencil (code _) p x v).regular i = x v ((code _) i).1 • (p ((code _) i).1).regular ((code _) i).2:=rfl
       refine Prod.ext (funext (fun i=> congr_fun (Prod.mk.inj (hp ((code _) i|>.1))|>.1) ((code _) i|>.2))) (funext fun i=>?_)
       change (P').regular i=(Q').regular i; rw [hK,hK,congr_fun (show (p ((code _) i).1).regular=(q ((code _) i).1).regular from (Prod.mk.inj (hp _)).2)]
    let U i j:= profile D.activities (p i).forced j; let V i j:= profile E.activities (q i).forced j; have hU i: U i=V i:= he _
    have hv : profile D.activities ((P').forced)=profile E.activities (Q'|>.forced):=by
       funext i Y
       have hc{D:Rep G n}{p:ι→ Coefficient F n}(hA:∀ i,∃ v,(p i).remBound 0 D S.k v): profile D.activities (pencil (code _) p x v|>.forced) i Y=∑ i',x v i' *profile D.activities (p i').forced i Y:=by
           choose c hc using hA; have h:= profile_merge (code _) (fun i' => Extra.Histories.stretch (x v i') (p i')) S.sane (fun i=> stretch_rem _ (hc i)) Summable.of_finite i Y; exact ((h.congr_fun fun j=>by unfold Extra.Histories.stretch; rw [profile_scale]; rfl).unique (hasSum_fintype _))
       rw [hc hA,hc hy];simp_rw [he] -- coe
    have h : liveE P'=liveE Q':= by unfold liveE; rw [(Prod.mk.inj hr).1,(Prod.mk.inj hr).2]
    refine Prod.ext h (show stowK hb P'=stowK ha Q' from ?_); unfold stowK; rw [hx,hv]
end visible
open Motion
lemma clovenD {H: History G}{N p m:ℕ}(D:Desk G (H.S.side m p))(E:Desk G (H.S.side (m+1) p))(P:Tool F H N p m) (ha:Well (H.rep N p (m+1)) E (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) (hW:Well (H.rep N p m) D (Real.sqrt (H.levels.clock.forcedAllowance m))){Z: Worth}{u ξ v T K R_ κx} (hA:Tool.Cap P (B:=κx) (Y:=A) (W:=Z) (D:=T) (T:=K) (u:=u) (ζ:=ξ) (v:=v) (X:=R_))(U: Keeper D.orient.p D.orient.activities)(hf:cart («R»:=H.rep N p m) P.down=cart U)(O:∀ m:Motion,D.orient.activities.Moves m.1 0)(T':Gram F A E ((H.levels.params (m+1)).columns)) (y:F.Coeff): let X':=fun i:Tally F=> audition (O i.1) (P.shot i.2 (Coin.uses (T'.scythe i.2))); let G':=Gram.point P T' y; let W:= pencil (code _) X' (chips F) y
    W.x=G'.x ∧ (∃ v,W.remBound 0 D.orient D.k v) ∧ capture G' P.down=capture W U:=by
    intro X_ p₁ P₁; let pU(i:Tally F):=P.shot i.2 (Coin.uses (T'.scythe i.2)); let q:= X_; let F_:= P.portfolio T'.scythe; have hp k:= Hue.audits k.1 (P.whirl k.1) (pU k) (O k.1) -- order check h
    have he(i:Tally F):= (P.recoil hA ha i.2 (T'.scythe i.2)).earns
    have hv(i:Tally F):∃ v,(q i).Format 0 A D.orient∧ (q i).remBound 0 D.orient D.k v:=by
        have hh:= Hue.priceU i.1 (O i.1) κx hA.good ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p)) ((along_format (pU i) hW.alongside.sym (he i|>.format))) (show (pU i).remBound 0 D.orient D.k _ from ((show kappa H m = D.k from hW.paid.symm) ▸ (along_bound _ hW.alongside.sym (he i|>.bound))))
        exact ⟨_,hh.1,hh.2.1⟩
    choose v hv hX using hv
    refine ⟨?_ ,⟨_,(pencil_cost (code _) q (chips F) D.sane (fun i=>⟨hv i,hX i⟩) y).2⟩,?_⟩
    · rw [show P₁.x= _ from pencil_x (code _) q (chips F) y,show p₁.x= _ from pencil_x (code _) F_ (chips F) y]; exact sum_congr rfl fun i _=> congr_arg ((chips F y i) • ·) (hp i).2.symm
    have hP k:= P.scout hA ha T'.scythe (fun i=> T'.toll _) k
    exact matching (chips F) y (hW.alongside.sym) _ _ hf (fun i=> (hp i).1) (fun i=> Hue.drones (hW.alongside.sym) (pU i) i.1 (P.whirl i.1) (O i.1) ((he i|>.bound))) (S:=D) (fun i=> ⟨_,show (F_ i).remBound 0 (H.rep N p m) D.k _ from ((show kappa H m = D.k from hW.paid.symm) ▸ (hP i|>.2.2))⟩) (fun i=>⟨_,hX i⟩)
end Hue
end YM.FullVolume.Paint.Rank
