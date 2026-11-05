import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Odometer

/-!
# Multiplicity at all purchase points. Banking from budgets at face.

Future consumer applying API using true budgets and support gains. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch Edition Filter Thirst
open scoped BigOperators Classical Topology

variable {V ι κ : Type} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {Q : Rep G n} {x : V→Site n} {C : Family G} {N m v k p : ℕ} {s t u y z r e b : ℝ}

def Pertains (x : V→Site n) (m : ℕ) := ∀ i,(univ.filter (fun j:V=>x j=i)).card≤m

lemma ancestor_P (Y : Points v) (h : k≤N) (hk : Station.width C.path.levels b k ≤ m) (hu : m ≤ N) (H : Fit C.path.levels b k Y) : Pertains (Peak.readers (C:=C) (b:=b) (p:=p) Y h hu) v:= by
  intro i; let A : (Ship.yard C b h p).Cell × Fin v → Site (C.side m p):=readers (C:=C) (p:=p) Y h hu (b:=b)
  let F:= C.path.levels; let W:= F.S.toDepth hk p;let B:= F.S.toDepth hu p;let s:= univ.filter fun j=> A j=i
  have hx j: W.parent (A j)=j.1:= by
    let X:= stampSite C b Y h p j
    let v: Station.width F b k ≤ N:= hk.trans hu
    let t:middle F b k ≤ N:= (Station.before F b k).trans h
    let T:= F.S.toDepth (Station.wider F b k) p
    have ht := Station.parent_nested T (F.S.toDepth t p) (F.S.toDepth v p) (F.S.toDepth_odd _ _) (F.S.toDepth_odd t _) X
    have hP :(F.S.toDepth t p).parent X=T.embed j.1:= H.stop ..
    change W.parent (B.parent X)=_
    rw [← parent_nested W B (F.S.toDepth v p) (F.S.toDepth_odd _ _) (F.S.toDepth_odd _ _), ht,hP,T.embed_parent]
  change s.card ≤ _; apply (card_le_card (show s ⊆ {W.parent i} ×ˢ (univ (α:=Fin v)) from ?_)).trans
  · rw [card_product,card_univ,Fintype.card_fin]; exact (le_of_eq (congr_arg (· * v) (card_singleton (show (Ship.yard C b h p).Cell from W.parent i)) |>.trans (one_mul _)))
  intro j hj; exact mem_product.mpr ⟨mem_singleton.mpr ((mem_filter.mp hj).2 ▸ (hx j).symm),mem_univ _⟩

section
variable [Fintype ι]
lemma valve (X : ι→ SourceAt G x) (P : BudgetPoint) (a : ι→ℝ) (h : ∀ i,0 ≤ a i) (ht : Pertains x m) (hv : 0≤y) (hp : ∀ i,strike (feet X) a P (fun j=>i∈ (X j).fires.val) (e+1) ≤ y) : Hits (feet X) a P e (wilt P.B*(m*y)):= by
  choose Vh hb using fun i=> (X i).chosen
  let Z i:= x (Vh i); let f i:= a i*debt P.B (e+1) (feet X i)
  have hh : Incur (feet X) P.B a e (wilt P.B*(m*y)):= by
    refine Thirst.circle _ _ Z (fun i=>(X i).remembers _ (hb i)) _ _ P.B_pos h _ ?_
    intro i; let F:= univ.filter fun j=>Z j=i; let D:=univ.filter fun j:V=>x j=i; let g k:=pay f (fun j=> Z j=i) k
    have he k: 0 ≤ g k:= by unfold g pay; split;exact mul_nonneg (h _) (Real.exp_pos _).le; exact le_rfl
    refine ⟨he,(hasSum_fintype _).summable,(tsum_fintype ..).trans_le ?_⟩
    have hx : (∑ j:ι,g j) = ∑ j∈ F,f j:= by rw [Finset.sum_filter]; apply sum_congr rfl; intro _ _; unfold g pay; split_ifs<;>rfl
    apply le_trans hx.le
    apply (promote f (fun i:V=>y) F D (fun i U=> Vh i=U) (fun i _=> alarm_pos (feet X) a _ _ h i) (fun j hj=> ⟨Vh j,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩,rfl⟩) ?_).trans
    · rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hv;exact_mod_cast (show D.card≤m from ht i)
    intro j _ S hs hh; apply le_trans _ (hp j); refine sum_le_sum_of_subset_of_nonneg ?_ fun i _ _=> alarm_pos (feet X) a _ _ h i
    intro i hi; have ht:j∈(X i).fires.val:=hh i hi ▸ hb i; simpa using ht
  intro i; have h:=hh i; unfold strike; rw [sum_filter]
  apply le_trans _ ((tsum_fintype ..).symm.trans_le h.2.2); apply Finset.sum_le_sum; intro j _; unfold Thirst.pay; split_ifs <;> exact le_rfl
end
end YM.Next.Rank.Flux
