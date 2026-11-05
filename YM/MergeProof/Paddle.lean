import YM.MergeProof.Wicket
/-! recover multi via DECORRELATED modes (possibly coincident in different modes)
& embeddings.Fraction stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{f c:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable (A:History G)(r:ℕ→ℕ)(k p N:ℕ)(δ φ:ℕ→ℝ)(o:∀ m:ℕ,V →Site (A.S.side m p))(w:V→ℝ)(hw:∀ i,0 < w i)
def march {V:Type*}(w:V→ℝ)(φ:ℕ→ℝ)(k:ℕ) : ℕ→V→ℝ
   | 0=> w
   | m+1=> if k ≤ m then fun i=>φ m*march w φ k m i else w
include hw
lemma marines : march w φ k k = w:=by cases k with
 | zero=> rfl
 | succ i=> rw [march,if_neg (by omega)]
omit hw
structure Migrating : Prop where
   mare m:k ≤ m→m < N→ (A.levels.clock.op m p).ratio.embed ∘ o m=o (m+1)
structure Drake (B:Census V)(M:ℕ)(o:V→Site f) : Prop where
   spread : ∀ s:B.Mode, 2 ≤ s.val.card→ ∀ i∈s.val,∀ j∈s.val,i≠j → M^2 ≤ separation (o i) (o j)
def mintK (x:ℕ):= Real.exp ((x:ℝ)/128)
lemma Drake.palms {a v:V→ℝ}{K:ℕ}{o:V→Site f}(hh:Drake B K o)(hv:∀ i,a i≤v i*mintK K)(hw:∀ i,0<a i)(he:∀ i,0<v i)(hx:8≤K): Repegs o K v a (1/2) 1 B:=by
   intro i hi X hX; have ht := Work.I01.answer f V o K hx i.val (hh.spread i hi) hi X hX
   rw [one_mul]; unfold Poly.toll
   refine (Finset.prod_le_prod (fun i _=>hw i|>.le) (fun i _=>hv i)).trans ?_
   rw [Finset.prod_mul_distrib,prod_const]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> he i|>.le); unfold mintK; rw [← Real.exp_nat_mul]
   have ht':(K:ℝ)*i.val.card ≤ 64*(coverNumber K X :ℝ):= by exact_mod_cast ht
   apply Real.exp_monotone; linarith only [ht']
local notation "P"=>A.levels.budget
structure Brine : Prop where
    water m : k ≤ m→ 0 < φ m ∧ 0<δ m
    mint m : k ≤ m→ 1 ≤ δ m*φ m*mintK (P m).B
    split m : k ≤ m → (P (m+1)).B^2 ≤ (A.S.block m).val*(P m).B^2
    support m : k ≤ m → 8 ≤ (P m).B
include hw
set_option quotPrecheck false
local notation "W" => march w φ k
variable (h:Brine A k δ φ)(B:Census V)
include h
lemma march_pos m (hk:k ≤ m) (j:V): 0<W m j:=by
   induction hk with
   | refl=> rw [marines k φ w hw]; exact hw _
   | step hi ih=>rename_i m; simp only [march,if_pos (show k ≤ m from hi)]; exact mul_pos (h.water m hi).1 ih
lemma desal (hn:Migrating A k p N o)(hS:Drake B (P k).B (o k))(hx:Monotone r)(hO:Occupancy (o k) (r k)): Matchup A r δ p N k o W B:=by
   have hM m (hi:k ≤ m) (hp:m<N): (A.levels.clock.op m p).ratio.parent ∘ o (m+1)=o m:=by rw [← hn.mare m hi hp]; exact funext fun i=> Ratio.embed_parent ..
   have hε:∀ m:ℕ,k ≤ m→m≤N → Occupancy (o m) (r k):=by
      intro m he hp; induction he with
      | refl =>exact hO
      | step hi ih=>rename_i m; intro x; let f:=(A.levels.clock.op m p).ratio
                    have hρ:= ih (show m ≤ N by omega) (f.parent x); apply le_trans (Finset.card_le_card _) hρ
                    intro j hj; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩; rw [← hM _ hi hp];simp only [Function.comp_apply]; exact congr_arg f.parent (Finset.mem_filter.mp hj).2
   have hΔ:∀ m:ℕ,k ≤ m → m≤N→Drake B (P m).B (o m):=by
      intro m he hp; induction he with
      | refl=> exact hS
      | step hi ih=>rename_i m; let f:=(A.levels.clock.op m p).ratio
                    rw [← hn.mare m hi hp]; refine ⟨fun s ht i hi' j hj hij=> ?_⟩; exact (h.split _ hi).trans ((Nat.mul_le_mul_left f.count.val ((ih (show m≤N by omega)).spread s ht i hi' j hj hij)).trans (Corona.below f ..))
   refine ⟨fun i he hp j=> march_pos A k δ φ w hw h i he _,fun m hi hp x=> (hε m hi hp x).trans (hx hi),fun i hi hp x=> (hε (i+1) (hi.trans i.le_succ) hp x).trans (hx hi), hM, fun i hi hm=>?_⟩
   have hw':=march_pos A k δ φ w hw h i hi; have hv:=hΔ _ hi hm.le
   apply hv.palms (v:=fun j=>δ i*W (i+1) j) _ hw' (fun j=>mul_pos (h.water i hi).2 (march_pos _ _ _ _ w hw h _ (hi.trans i.le_succ) j)) (h.support _ hi); intro j
   simp only [march,if_pos hi]; exact ((mul_one (W i j)).symm.trans_le (mul_le_mul_of_nonneg_left (h.mint _ hi) (hw' j|>.le))).trans_eq (by ring)
end YM.MergeProof.Accent
