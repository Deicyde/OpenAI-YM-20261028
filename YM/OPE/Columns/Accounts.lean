import YM.MergeProof.Largo
import YM.OPE.Columns.HeadingStep

/-!
# Keep quantitative triangular transfer on actual Music charges

Strengthening of YM/MergeProof/Largo.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p : ℕ)(A:Hol G) (W : Worth)
local notation "DO"=> fun i=> GaugeDoor (H.rep N p (i+1)) (H.rep N p i)
set_option quotPrecheck false
/-- fixed ports used on the *same* Stampede as the primary construction -/
structure Triangle (m : ℕ) (x y : F.Coeff → F.Coeff) : Prop where
  leads : ∃ T : Heading F, (∃ c : ℝ, Push.Local.Leading T.map.toLinearMap c) ∧
    (∀ v, F.coeffSize (T.map v) ≤ W.K (H.levels.clock.J (m+1))*F.coeffSize v ∧
          F.coeffSize (T.map.symm v) ≤ W.K (H.levels.clock.J (m+1))*F.coeffSize v) ∧
    ∀ v, F.coeffSize (y v - T.leads (H.S.block m) (x v)) ≤
      barunit (H.S.block m) * F.coeffSize (F.core (x v))
structure TuneColumns (m:ℕ) (P:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(t:ℝ):Prop where
   price : ∃ (W':Set Wing), W'.Finite ∧ ∃ (K:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities), (∀ i:(StockTag (H.S.side (m+1) p)), W' (.gasKey (cart (R:=H.rep N p (m+1)) K i))) ∧
      ∃ (T : Heading F) (a b:ℝ),Stampede B H N p m A P a b t T W' ∧ Buys H F W m a b ∧ ∃ c, Leading (T.map.toLinearMap) c
   honest:SoundDoor (H.levels.clock.op m p) P
   toll:0 ≤ t
   kappa:Real.sqrt (H.levels.clock.forcedAllowance (m+1)) ≤ 1

lemma compose_columns {u: ℕ→ℝ} {D:∀ m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (h : H.Selected)(hB:B.Sound A) (hw : roomCost H.levels W) (hb : Bank W H.levels) (r : ℕ) (hr : r≤N)
    (V : Voice F H p N) (hu : OnTop B H N p A V) (hv: Chorus H N p N V)
    (calls : ∀ m:ℕ, r ≤ m → ∀ hm:m<N,TuneColumns B H N p A W m (D m hm) (u m)):
    ∃ M : Extra.Histories.Music F H N p,M.tone N=V ∧ Sung B H N p A W r M ∧ ∀ m:ℕ,r ≤ m → ∀ hm:m<N, Carol B H N p m (D m hm) (M.tone (m+1)) (M.tone m) (u m) ∧ Chorus H N p m (M.tone m) ∧ Triangle H W m (M.tone (m+1)).index (M.tone m).index :=by
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
     obtain ⟨⟨W',hW,K,hx,T,cost,b,h₀,h₁,hL⟩,hK,hP,hQ⟩:= calls k le_rfl hk
     have hSq: Chorus H N p (k+1) (M.tone _):=by
        by_cases h:k+1=N
        · rw [h,hM]; exact hv
        exact (hD (k+1) le_rfl (by omega)).2.1
     obtain ⟨v,hV,hT,hX,hA,hY⟩:= repriseQ_columns B H N p A W k (M.tone _) h hk (hS.earned _ le_rfl hk) hw hb T (D k hk) hK W' hP h₀ hW hQ h₁ K hx hSq hB (fun U=> (Tour.bright H h N p _ hk U).ne')
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
     subst i; rw [hh,htr (k+1) k.lt_succ_self]; refine ⟨hY, hX, ⟨T, hL, ?_, hA⟩⟩
     intro x
     have hx₁ := h₀.map_norm x
     -- `cost` was charged before the block
     have ht' : cost ≤ W.K (H.levels.clock.J (k+1)) := by
       have ha : 0 ≤ b := h₁.epsilon
       let s := (H.levels.params (k+1)).columns
       have he : cost ≤ cost+b*s := le_add_of_nonneg_right
         (mul_nonneg ha (zero_le_one.trans (H.levels.params _).columns_ge))
       exact ((he.trans (le_mul_of_one_le_right ((zero_le_one.trans h₁.cost).trans he)
         (orbitCost_one_le _)))).trans h₁.funds
     have h := mul_le_mul_of_nonneg_right ht' (Work.G08.size_nonneg F x)
     exact ⟨hx₁.1.trans h,hx₁.2.trans h⟩
end YM.MergeProof
