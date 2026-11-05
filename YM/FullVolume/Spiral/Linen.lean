import YM.FullVolume.Spiral.Balm
import YM.FullVolume.Dusk.Grove
/- split EPICS. preserve pencil encoding in audition & per stripes. ranks covers pre-s. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn
local notation "I" => Extra.Histories.InputColumn.Listing
section
variable (Z:Plate F m n){Q:Desk G m}
variable (K:Keeper Q.orient.p Q.orient.activities)
-- exact fields
abbrev dots (v:F.Index)(x:Coin F Y Q): I→ Pin F n:=consist 0 (fun j=> Z.tint j ((Coin.uses x).1 j)) (fun j=>Z.ink j (stowK K (book (Size.axis F v) (Coin.uses x)) j))
abbrev stems (v:F.Index): I→ Pin F n:=consist (Z.main v) 0 0
def poseF (v:F.Index): Coefficient F n:= Extra.Histories.merge (code I) (fun i=> Matric.tell (stems Z v i))
def palmF (v:F.Index)(x:Coin F Y Q): Coefficient F n:= Extra.Histories.merge (code I) (fun i=> Matric.tell (dots Z K v x i))
variable (A:∀ m:Motion,P.orient.activities.Moves m.1 0)
-- full pencil
abbrev fullF (x:F.Index→ Coin F Y Q): F.Coeff→ Coefficient F n:= pencil (code (Tally F)) (fun i=> audition (A i.1) (gather Z K (Matric.book (Size.axis F i.2) (Coin.uses (x i.2))) i.2)) (chips F)
def pagesP : F.Coeff→ Coefficient F n:= pencil (code (Tally F)) (fun i=> audition (A i.1) (poseF Z i.2)) (chips F)
def pagesS (x:F.Index→ Coin F Y Q): F.Coeff→ Coefficient F n:= pencil (code (Tally F)) (fun i=> audition (A i.1) (palmF Z K i.2 (x i.2))) (chips F)
end
lemma togetherP (R:I→sun→ Coefficient F n)(Y:Hol G)(P:Desk G n)(y:I→F.Coeff)(x:F.Coeff)(a b:I→ℝ)(v t:ℝ)(hq: HasSum y x)(hv:Summable (fun i=> F.coeffSize (y i)))(hA:SumBudget a v)(hB:SumBudget b t) (h:∀ i,Forum (R i) q (y i) Y P (a i) (b i)) : Forum (fun s=>Extra.Histories.merge (code I) fun i=>R i s) q x Y P v t:=hq.tsum_eq ▸ (enlarge (multi R (code I) Y P _ _ _ hB.2.1 hA.2.1 hv h) hA.2.2 hB.2.2)
-- numerical
variable {Z:sun→Plate F m n}
variable {U:sun→Rep G n}{K:sun→Rep G m}{Q: Desk G m}
variable {T:Tableau q 300} {E:Heading F}{L:Side}
variable {Y':sun→F.Index→ Response G n}{Yr Yk:sun→ℕ→ (Config G m→ℂ)→ Response G n}
variable {η χ :ℝ}
variable (hU:∀ s,Along P.orient (U s))(hK:∀ s,Along Q.orient (K s))(h:Epics Z U K E L Y T P.k Q.k η χ Y' Yr Yk) (hQ:4≤q) (hF :∀ s,Scan (Z s) Y (U s) (K s))
local notation "eA"=> T.price+1
local notation "e"=> ((T.price+1)+(3+2*T.price))
local notation "F!"=> orbitCost F
include h hQ hF hU
variable (hα:0≤η)(hχ:0≤χ)
include hα hχ
lemma sprout (j:F.Index): let x:= Size.axis F j; let b':=(T.price+1)*(η * F.coeffSize (F.core x)); let v':=e*(χ*F.coeffSize (vowel F L (F.core x)))
   Forum (fun s:sun=> poseF (Z s) j) (q/2) (E.leads L x) Y P b' v':=by
   intro x b v'; let Y':I→F.Coeff:= consist (E.leads L x) 0 0; let a:=consist b 0 0; let r:=consist v' 0 0
   have hY : HasSum Y' (E.leads L x):=by simpa only [Y',consist, Sum.elim_inl,add_zero] using added (f:=Y') hasSum_zero hasSum_zero
   have hh : HasSum a b:= by simpa only [a,consist, Sum.elim_inl,add_zero] using added (f:=a) hasSum_zero hasSum_zero
   have hZ : HasSum r v':=by simpa only [r,consist, Sum.elim_inl,add_zero] using added (f:=r) hasSum_zero hasSum_zero
   refine togetherP (q:=q/2) (fun k s=> Matric.tell (stems (Z s) j k)) _ _ Y' _ a r _ _ hY ?_ ⟨?_,hh.summable,hh.tsum_eq.le⟩ ⟨?_,hZ.summable,hZ.tsum_eq.le⟩ ?_
   · apply summable_of_ne_finset_zero (s:={Sum.inl ()}); rintro (_|_|_) hx; simp at hx; all_goals simp [Y',Frame.coeffSize,consist]
   · rintro (i|_|_); exact mul_nonneg (by linarith [T.sane]) (mul_nonneg hα (Work.G08.size_nonneg F _)); all_goals exact le_rfl
   · rintro (i|_|_); exact mul_nonneg (by linarith [T.sane]) (mul_nonneg hχ (Work.G08.size_nonneg F _)); all_goals exact le_rfl
   rintro (k|k|k); exact herbs Z T E L hU h hQ hF j; all_goals exact field0 P F _ (by linarith only [hQ]) Y
omit hχ
include hK
variable (hx:Keeper Q.orient.p Q.orient.activities)
lemma balms (j:F.Index)(z:Coin F Y Q):∃ a b:I→ℝ,SumBudget a ((T.price+1)*(η*‖z‖))∧ SumBudget b (e*(η*‖z‖))∧∀ k, Forum (fun s:sun=> Matric.tell (dots (Z s) hx j z k)) (q/2) 0 Y P (a k) (b k):=by
   let V:=book (Size.axis F j) (Coin.uses z); let X:= rack hx V; let Q0:= Q.orient
   have he:Well Q0 Q Q.k:=⟨⟨rfl,rfl⟩,rfl⟩
   obtain ⟨hs,hv⟩:= granted he Y (Size.axis F j) z; have hp:X.Format 0 Y Q0:= rack_format hx V hs
   obtain ⟨a,b,h₁,h₂,hv,hμ,⟨v,hA,hM⟩,q₀,hq,h0⟩:= keeps hx V hv -- hA etc
   let u(i:ℕ):=Q.orient.p.mass (X.support i) (v i); let k(i:ℕ):= Q.orient.p.mass (Local.patch Q.orient.activities i) (q₀ i)/Q.k
   have hk:SumBudget k b:=by
      refine ⟨fun i=>div_nonneg (hq.1 _) Q.sane.le,hq.2.1.div_const _,?_⟩; unfold k; rw [tsum_div_const]; exact (div_le_iff₀ Q.sane).mpr (hq.2.2.trans_eq (mul_comm ..))
   let X'(i:ℝ):I→ℝ:= consist 0 (fun j=> i*(η*u j)) (fun j=> i*(η*k j)); let Y(z):= z*η
   have hh(i:ℝ)(h:0≤ i):SumBudget (X' i) (i*(η* ‖z‖)):=by
      have hz':HasSum (X' i) (0+i*(η*((∑' i,u i)+∑' i,k i))):=by rw [mul_add,mul_add]; exact added ((hA.2.1.hasSum.mul_left η).mul_left i) ((hk.2.1.hasSum.mul_left η).mul_left i)
      refine ⟨?_,hz'.summable,(hz'.tsum_eq.trans_le ?_)⟩
      · rintro (i'|k|k); exact le_rfl; exact mul_nonneg h (mul_nonneg hα (hA.1 k)); exact mul_nonneg h (mul_nonneg hα (hk.1 k))
      rw [zero_add]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((add_le_add hA.2.2 hk.2.2).trans (by assumption)) hα) h
   refine ⟨_,_,hh (T.price+1) (by linarith [T.sane]),hh _ (by linarith [T.sane]),?_⟩
   rintro (i|i|i); exact field0 P F (q/2) (by linarith only [hQ]) ‹Hol G›; exact regs Z T E L hU hK h hQ hF X i hp _ (hM i) rfl; exact prints Z T E L hU hK h hQ hF X i hp _ (h0 i|>.1) (h0 i|>.2)
lemma pores (j:F.Index)(z:Coin F Y Q):Forum (fun s:sun=> palmF (Z s) hx j z) (q/2) 0 Y P ((T.price+1)*(η*‖z‖)) (e*(η*‖z‖)):=by
   obtain ⟨a,b,hb,hY,ht⟩:= balms hU hK h hQ hF hα hx j z; refine togetherP _ Y P 0 0 a b _ _ hasSum_zero ?_ hb hY ht
   apply summable_of_ne_finset_zero (s:=∅); intros; simp only [Pi.zero_apply, Frame.coeffSize,norm_zero,sum_const_zero]
omit hK
include hχ
variable (V:∀ m:Motion,P.orient.activities.Moves m.1 0) (R: SectionData F)(hR:R.Sound Y)(hn:2 ≤ n.val)(w:F.Coeff)
local notation "c_"=> turnCost P.orient.p.order P.orient.p.power
include hR hn
lemma archwork : Forum (fun s:sun=> pagesP (Z s) V w) (q/2) (E.leads L w) Y P (F!*F!*(T.price+1)*η*F.coeffSize (F.core w)) (c_* F!*e*χ*F.coeffSize (vowel F L (F.core w))):=by
   let H(i:Tally F):=Size.axis F i.2; let k:= F!* ((T.price+1)*η); let p:=turnCost P.orient.p.order P.orient.p.power; let l:=p*e*χ
   have hk:0≤k:=mul_nonneg (zero_le_one.trans (orbitCost_one_le F)) (mul_nonneg (by linarith only [T.sane]) hα); have hL:0 ≤ l:=by have h: 0≤ p:=pow_nonneg (by positivity) _;exact mul_nonneg (mul_nonneg h (by linarith only [T.sane])) hχ
   let u(i:Tally F):=(chips F w i) • Motion.patch F i.1 (E.leads L (H i)); let a(i:Tally F):= ‖chips F w i‖* (k* F.coeffSize (F.core (H i))); let b(i:Tally F):= ‖chips F w i‖*(l *F.coeffSize (vowel F L (F.core (H i))))
   have hy: ∑' i, u i= E.leads L w:=by rw [tsum_fintype]; exact repaint_same F (E.leads L) (fun x m=> (E.coheres L m x).symm) w
   let P0 (i:Tally F) (s:sun):= Extra.Histories.stretch (chips F w i) (audition (V i.1) (poseF (Z s) i.2))
   have hz(i:Tally F): Forum (P0 i) (q/2) (u i) Y P (a i) (b i):=by
       have h':= (whorls (sprout hU h hQ hF hα hχ i.2) i.1 (V i.1) R hR hn).paidStretch (chips F w i); apply h'.enlarge <;> exact le_of_eq (by first | (unfold a H k; ring) | (unfold b H l p; ring))
   rw [←hy]; refine enlarge (multi P0 (code _) Y P _ _ _ Summable.of_finite Summable.of_finite Summable.of_finite hz) ?_ ?_
   · rw [tsum_fintype,show ∑ i:Tally F,a i= k*∑ i:Tally F, ‖chips F w i‖* F.coeffSize (F.core (Size.axis F i.2)) from ?_]; swap; · rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>mul_left_comm ..)
     exact (mul_le_mul_of_nonneg_left (core_tab F w) hk).trans_eq (by unfold k; ring)
   rw [tsum_fintype]; exact (residual_bill F L l hL w).trans_eq (by unfold l p; ring)
include hK
omit hχ
def chipPay (F:Labels.Frame G i)(w:F.Coeff):=∑ i:Tally F, ‖chips F w i‖
lemma moonts (f:F.Index→ Coin F Y Q):Forum (fun s:sun=> pagesS (Z s) hx V f w) (q/2) 0 Y P (F!*(T.price+1)*η*chipPay F w *‖f‖) (c_*e*η*chipPay F w*‖f‖):=by
   let r:= F!* (T.price+1)*η; let v:= c_*e*η
   let a(i:Tally F):= ‖chips F w i‖* (r*‖f i.2‖); let b(i:Tally F):= ‖chips F w i‖*(v*‖f i.2‖)
   let P0(i:Tally F)(s:sun):= Extra.Histories.stretch (chips F w i) (audition (V i.1) (palmF (Z s) hx i.2 (f i.2)))
   have he(i:Tally F):Forum (P0 i) (q/2) 0 Y P (a i) (b i):=by
       have ht: Motion.patch F i.1 0=0:=by unfold Motion.patch; split<;> simp; -- at tactic
       have h':= (whorls (pores hU hK h hQ hF hα hx i.2 (f i.2)) i.1 (V i.1) R hR hn).paidStretch (chips F w i); rw [ht,smul_zero] at h'; unfold a b r v; exact enlarge h' (le_of_eq (by ring)) (le_of_eq (by ring))
   have hh (s:ℝ)(hs:0≤ s) : ∑' i:Tally F, ‖chips F w i‖*(s*‖f i.2‖) ≤ s*chipPay F w* ‖f‖:=by
       rw [tsum_fintype,chipPay,Finset.mul_sum,Finset.sum_mul]; apply sum_le_sum; intro i _; rw [mul_left_comm,← mul_assoc]; apply mul_le_mul_of_nonneg_left (norm_le_pi_norm f i.2) (mul_nonneg hs (norm_nonneg _))
   have hY:= enlarge (multi P0 (code _) Y P 0 a b Summable.of_finite Summable.of_finite Summable.of_finite he) (hh r (mul_nonneg (mul_nonneg (zero_le_one.trans (orbitCost_one_le F)) (by linarith only [T.sane])) hα)) (hh v (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (by linarith only [T.sane])) hα))
   simp only [Pi.zero_apply,tsum_zero] at hY; exact hY
end YM.FullVolume.Paint.Tower
