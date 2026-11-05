import YM.Next.RANK.Flux.Coin
import YM.Next.RANK.Flux.Grain
import YM.Next.RANK.LedgerGate


/-!
# Viability tests BEFORE any marked log

Kin and survey must hold on C&P already. Uses marker counts not geometry shortcuts.
Partner estimates in this receipt refer ALWAYS to source atoms (vacuum additions
separate), including even (1,site) unit changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e a b y : ℝ}
variable [Fintype ι] [Fintype κ] [Fintype α]

private def wake (a : ℝ) := Real.exp a-1


-- estimate obligations here (once on each step) may also be used by producers before Epoch. Strength `ucap`
def ucap (e : ℝ):= ((e+1)+1+1)+1+1

structure Tickets (Q : BudgetPoint) (y : ℝ) : Prop where
  day : Risible Q.B y
  total : Risible Q.B (Real.exp y-1)
  merger : Risible Q.B ((Real.exp y-1)+(Real.exp y-1))
  revenue : Risible Q.B (Real.exp ((Real.exp y-1)+(Real.exp y-1))-1+y)
  final : Real.exp (Real.exp ((Real.exp y-1)+(Real.exp y-1))-1+y)-1 ≤ 1

variable {Q : BudgetPoint} (S : ι→ Plug G ζ Q.threshold) (P : κ → Lining G ζ Q.threshold) (F : α → CoverReads G ζ Q.threshold)
variable (f : ι⊕κ→ ℝ) (g : α→ℝ)
section
variable (u : ι→Prop) {r : V→ℝ} (hr : ∀ i,0 < r i) {M L z : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L)

-- input statement still on all first-system/uncolored tag mixtures, no LOG.
structure Authorship (u : ι→Prop) (r : V→ℝ) (e M L y z : ℝ) : Prop where
  earned i : 0 ≤ f i
  reserved i : 0 ≤ g i
  regular i U : if (S i).landed then M* Poly.price r ((S i).tolls U) ≤ f (.inl i) else
      factor (¬ u i) L * Poly.price r ((S i).tolls U) ≤ f (.inl i)
  late i U : L* Poly.price r ((raised (P i)).covets U) ≤ f (.inr i)
  fees i U : Poly.price r ((F i).covets U) ≤ g i
  cost : Hits (dish S P) f Q (ucap e) y
  boundary : Hits (fun i=>(F i).extent) g Q (ucap e) y
  roots j : strike (dish S P) f Q (fun i=> ∃ p : ι,i=.inl p∧ ¬ (S p).landed ∧ j∈(S p).fires.val) (ucap e) ≤ z

variable (T : Tickets Q y) (hv : 0≤ e) (h : Authorship S P F f g u r e M L y z)

lemma columnK (A : ι→Lifted G ζ Q.threshold) (v : ι→ℝ) (_ : ∀ i,0 ≤ v i) (hb : Hits (fun i=>(A i).extent) v Q (e+1) 1)
    (H : ∀ i U,M*Poly.price r ((A i).amount U) ≤ v i) (hM : 1 ≤ M) :
    Stripes Q A r (e+1) (1/M):= by
  let X i:=(A i).extent;let p:=alarm X v Q.B (e+1); have ht : 0<M:= zero_lt_one.trans_le hM
  have hp i:0≤p i:=alarm_pos X v _ _ (by assumption) i
  refine ⟨fun i=>p i/M,fun i=>⟨div_nonneg (hp _) ht.le,fun U=> ?_⟩,fun i=>?_⟩
  · apply (le_div_iff₀ ht).2; unfold p alarm; apply le_trans _ (mul_le_mul_of_nonneg_right (H i U) (Real.exp_pos _).le)
    rw [Lifted.amount,Poly.solo];unfold charge X; exact le_of_eq (by ring)
  rw [← show ((∑ j, if i∈X j then p j else 0)/M) = ∑ j, if i∈ (A j).extent then p j/M else 0 from ?_]
  · refine div_le_div_of_nonneg_right ?_ ht.le;have he:=hb i; unfold strike at he; rw [sum_filter] at he; apply le_trans _ he; apply sum_le_sum;intro i _; split_ifs<;> exact le_rfl
  rw [Finset.sum_div]; apply sum_congr rfl; intro j _; split_ifs; exact rfl; exact zero_div _

abbrev Pay1 := panda S P f
abbrev Pay₂ := Sum.elim (fun i : Dimmed (panel S P)=> Pay1 S P f i.val) (hlog (sunny (panel S P)) (fun i=> Pay1 S P f i.val))
-- annotate le proofs; order arr
include hr hM hL hv h T
lemma cloud : Stripes Q (after S P F) r (e+1) (1/M):= by
  let B:=panel S P;let D:=evening B;let X:= sunny B;let A₀:= Dimmed B; let Y:= Pay1 S P f;let E:=e+1;let m:=wake y
  let v:=Pay₂ S P f;let R:=Dusty S P;let P':=negXs (t:=Q.threshold) X
  have hX i:0≤Y i:=panda_pos _ _ _ _ h.earned
  let m₀ (i:Bright B):= Y i.val; let Z:=hlog X m₀
  have hp i:0 ≤ v i:= by rcases i with i|i; exact hX _; exact (hlog_pos X m₀ (fun _=> hX _) i)
  have hr': Hits (dish (Plug.raid ∘ D) P') v Q (E+1+1) (m+m):= by
    obtain ⟨hv₀,hv₁⟩:= reaches S P Q f h.earned (show Hits (dish S P) f Q (E+1+1+1+1) y from h.cost) T.day (by linarith only [hv,(show E=e+1 from rfl)])
    have Hx:= touches_here X m₀ (fun i=>hX _) hv₀ (show 0 ≤ E+1+1 by unfold E;linarith only [hv]) T.total
    have ht:= (marches (fun i:A₀=>Plug.extent (Plug.raid (D i))) (fun i:A₀=> Y i.val) (fun i=>hX _) hv₁ (show E+1+1≤E+1+1+1 by linarith only))
    exact plus_hits P' _ _ _ (Plug.raid ∘ D) ht Hx (show m+m≤m+m from le_rfl)
  let C:= panda (Plug.raid ∘ D) P' v
  have hC c:0 ≤ C c:= panda_pos _ _ _ _ hp
  let A:=Sum.elim C g
  have ha i:0 ≤ A i:= by rcases i with i|i; exact hC i; exact h.reserved i
  let N:= wake (m+m)
  have hu: Hits (fun i=> (R i).extent) C Q (E+1) N:= by
    exact pad (Plug.raid ∘ D) P' v Q hp hr' T.merger.grain (by unfold E;linarith) T.merger.day
  have hF: Hits (dish (Plug.raid ∘ R) (witness F)) A Q (E+1) (N+y):= by
    exact plus_hits (witness F) Q C g (Plug.raid ∘ R) hu (marches (fun i=>(F i).extent) g h.reserved h.boundary (show E+1 ≤ ucap e by unfold ucap E;linarith only)) (show N+y≤_ from le_rfl)
  let W:=after S P F
  let f:=panda (Plug.raid ∘ R) (witness F) A
  have ht: Hits (fun i=>(W i).extent) f Q E (wake (N+y)):= by
    exact pad (Plug.raid ∘ R) (witness F) A Q ha hF T.revenue.grain (by unfold E;linarith) T.revenue.day
  have he:=budget_squeeze S P u _ _ hL hM hr h.regular h.late
  have hh i V : M*Poly.price r ((R i).amount V) ≤ C i := by
    apply dest D P' i V r hr v hM (fun i=> he.2 i V);intro j; unfold P'; rw [negs]
    have hz (X : veil _):Poly.price r (-X)=Poly.price r X:= by unfold Poly.price; simp
    rw [hz];apply le_trans _ (bond_factor (fun i:Bright B=>clean S P u i.val) X Q.threshold m₀ r hr hL j V (fun i=> he.1 i V))
    exact le_mul_of_one_le_left (Poly.nonnegative hr _) (raised_one hL _)
  refine columnK W f (fun _=> panda_pos _ _ _ _ ha) (fun i=> (ht i).trans T.final) (fun i V=> ?_) hM
  exact dest R (witness F) i V _ hr A hM (fun i=>hh i V) (fun i=> h.fees i V)
end
end YM.Next.Rank.Flux
