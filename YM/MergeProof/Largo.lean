import YM.MergeProof.Renaissance

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p : ℕ)(A:Hol G) (W : Worth)
local notation "DO"=> fun i=> GaugeDoor (H.rep N p (i+1)) (H.rep N p i)
set_option quotPrecheck false
/-- fixed ports not tag motion selected later. Affine at all admissible periods. -/
def Carol (m:ℕ) (D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(V : Voice F H p (m+1))(Q: Voice F H p m) (t:ℝ):Prop:=∃ Y:Set Wing,Y.Finite∧∀ v,let I:= V.plays v; let R:=H.rep N p (m+1); let Z:=V.index v
       Tale Y 0 0 (((H.S.block m).val:ℂ)^d) (I.exponentialEntry 0 B R) (profile R.activities I.forced) (profile (H.rep N p m).activities (Q.plays v).forced) (Z 0) ((orbitCost F*F.coeffSize Z)*(t+2*(H.levels.params (m+1)).columns)) (Q.charge v) D
structure Tune (m:ℕ) (P:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(t:ℝ):Prop where
   price : ∃ (W':Set Wing), W'.Finite ∧ ∃ (K:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities), (∀ i:(StockTag (H.S.side (m+1) p)), W' (.gasKey (cart (R:=H.rep N p (m+1)) K i))) ∧
      ∃ (T : Heading F) (a b:ℝ),Stampede B H N p m A P a b t T W' ∧ Buys H F W m a b
   honest:SoundDoor (H.levels.clock.op m p) P
   toll:0 ≤ t
   kappa:Real.sqrt (H.levels.clock.forcedAllowance (m+1)) ≤ 1

lemma compose {u: ℕ→ℝ} {D:∀ m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (h : H.Selected)(hB:B.Sound A) (hw : roomCost H.levels W) (hb : Bank W H.levels) (r : ℕ) (hr : r≤N)
    (V : Voice F H p N) (hu : OnTop B H N p A V) (hv: Chorus H N p N V)
    (calls : ∀ m:ℕ, r ≤ m → ∀ hm:m<N,Tune B H N p A W m (D m hm) (u m)):
    ∃ M : Extra.Histories.Music F H N p,M.tone N=V ∧ Sung B H N p A W r M ∧ ∀ m:ℕ,r ≤ m → ∀ hm:m<N, Carol B H N p m (D m hm) (M.tone (m+1)) (M.tone m) (u m) ∧ Chorus H N p m (M.tone m):=by
   classical
   induction hr using Nat.decreasingInduction with
   | self=>
     let a (m : ℕ) : Voice F H p m := ⟨fun _ => Extra.Histories.primary 0 0, fun _ => 0,LinearEquiv.refl ℂ _⟩
     let M : Extra.Histories.Music F H N p := ⟨update a N V⟩
     have he : M.tone N=V := update_self N V a
     refine ⟨M,he,⟨he.symm ▸ hu, le_rfl, fun i hi ht => ?_, fun i hi ht => by omega⟩,fun i hi ht=> by omega⟩
     obtain rfl : i=N := le_antisymm ht hi
     rw [he]; exact hu.heard
   | of_succ k hk ih=>
     obtain ⟨M,hM,hS,hD⟩:=ih fun i hi=> calls i (by omega)
     obtain ⟨⟨W',hW,K,hx,T,t,b,h₀,h₁⟩,hK,hP,hQ⟩:= calls k le_rfl hk
     have hSq: Chorus H N p (k+1) (M.tone _):=by
        by_cases h:k+1=N
        · change Chorus H N p (k+1) (M.tone (k+1)); rw [h,hM]; exact hv
        exact (hD (k+1) le_rfl (by omega)).2
     obtain ⟨v,hV,hT,hX,hY⟩:= repriseQ B H N p A W k (M.tone _) h hk (hS.earned _ le_rfl hk) hw hb T (D k hk) hK W' hP h₀ hW hQ h₁ K hx hSq hB (fun U=> (Tour.bright H h N p _ hk U).ne')
     let t : Extra.Histories.Music F H N p := ⟨update M.tone k v⟩
     have hh : t.tone k=v := update_self k v M.tone
     have htr (i : ℕ) (hi : k < i) : t.tone i=M.tone i := update_of_ne hi.ne' v M.tone
     refine ⟨t,(htr N hk).trans hM,⟨?_,hk.le, fun i hi he => ?_,fun i hi he => ?_⟩,fun i hi he=>?_⟩
     · rw [htr _ hk]; exact hS.head
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr _ h]; exact hS.earned i h he
       subst i; rw [hh]; exact hV
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr i h,htr (i+1) (by omega)]; exact hS.step i h he
       subst i; rw [htr (k+1) k.lt_succ_self,hh]; exact hT
     obtain hl|hl:= lt_or_eq_of_le hi
     · rw [htr i hl,htr (i+1) (by omega)]; exact hD i hl he
     subst i; rw [hh,htr (k+1) k.lt_succ_self]; exact ⟨hY,hX⟩
end YM.MergeProof
