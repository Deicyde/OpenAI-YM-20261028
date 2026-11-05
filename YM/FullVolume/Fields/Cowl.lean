import YM.FullVolume.Fields.Basin
import YM.FullVolume.Mark.Sages
/-! EOF for exponent and profiles of marks: at origin and ANY fixed translated anchor.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Ac Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations MergeProof MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{n:Side}{S:Desk G n}{P:BudgetPoint}
local notation "D"=> S.orient
section cost
variable (x y: Coin F A S)
def logrem:= fun U:Config G n => ∑' i,(book (0:F.Coeff) (Coin.uses x)).maskedTerm D i U
def clore (i:Box n):= profile (D).activities (Coin.uses x|>.2) i
lemma lprop (U): Summable (fun i=>(book (0:F.Coeff) (Coin.uses x)).maskedTerm D i U)∧ ‖logrem x U‖≤ ‖x‖:=by
    let P:= book (0:F.Coeff) (Coin.uses x); obtain ⟨a,b,ha,hb,h,hc,⟨c,hC,hQ⟩,hP⟩:= (Coin.wealth x).2
    let f(i:ℕ):= P.maskedTerm D i U; have hg : SumBudget (fun i=> ‖f i‖) a:= by
       apply Extra.Multi.Budget.mono hC (fun i=>norm_nonneg _) _ le_rfl; intro i; apply le_trans _ ((D).p.loMass _ _ (hQ i).1); by_cases hv:Healthy (D).p.threshold (P.support i) U
       · unfold f Coefficient.maskedTerm; rw [masked_eq _ _ _ _ hv]; exact (hQ i).2 U hv [] (Nat.zero_le _) (by simp)
       unfold f Coefficient.maskedTerm; rw [masked_ne _ _ _ _ hv, norm_zero]; exact (hQ i).1
    exact ⟨hg.2.1.of_norm,(norm_tsum_le_tsum_norm hg.2.1).trans (hg.2.2.trans ((le_add_of_nonneg_right hb).trans h))⟩
lemma lports (U):logrem (x-y) U=logrem x U-logrem y U:=by
    unfold logrem; rw [← Summable.tsum_sub (lprop .. |>.1) (lprop ..|>.1), map_sub]; refine tsum_congr fun i=> ?_; change masked _ _ ((Coin.uses x).1 i-(Coin.uses y).1 i) _= _; exact congr_fun (map_sub (maskLinear _ _) ((Coin.uses x).1 i) ((Coin.uses y).1 i)) U
lemma heel (i:Box n)(U):Summable (fun k:{k//barcode (D).activities k=i}=> (Coin.uses x).2 k.val U) ∧ ‖clore x i U‖≤ S.k*‖x‖:=by
   let Q:=barcode (D).activities; let f j:= (Coin.uses x).2 j U; obtain ⟨a,b,hp,hb,hq,hk,hV,c,hc,hC⟩:= (Coin.wealth x).2; let g(j:{j//Q j=i}):= f j.val
   have hg: SumBudget (fun i=> ‖g i‖) (S.k* b):= Extra.Multi.Budget.mono (Local.sumBudget_subtype (fun i'=>Q i'=i) hc) (fun i=>norm_nonneg (g i)) (fun j=> ((hC j.val).2 U).trans ((D).p.loMass _ _ (hC j.val).1)) le_rfl -- syntax
   exact ⟨hg.2.1.of_norm,(norm_tsum_le_tsum_norm hg.2.1).trans (hg.2.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hp).trans hq) hk.le))⟩
lemma hedge (i:Box n)(U):clore (x-y) i U=clore x i U- clore y i U:=by unfold clore profile cram; rw [← Summable.tsum_sub (heel .. |>.1) (heel .. |>.1), map_sub];rfl -- issues
end cost
variable (F)
section
variable (T:SectionData F)
-- part(T) linear.L.Reg. measurable.
local notation "Λ"=> (0:Site n)
abbrev rotor (x:F.Coeff) (U: Config G n):= part T Λ D U x
lemma morsel {s:ℕ→ F.Coeff}(h:CauchySeq s): Confluence (fun i (U:Config G n)=>part T (0:Site n) D U (s i)):=by
    let f (x:F.Coeff) (U:Config G n):=part T (0:Site n) D U x
    have hx(v:F.Coeff): ∃ a:ℝ,∀ x, ‖f v x‖≤ a:=by
        let R:=(D); let B:=T.footprint Λ; let V:= T.places (F.scaled R.p.threshold⁻¹ (F.core v)) Λ
        have hb:IsCompact (Set.range (fun x=> ‖V x‖)):= isCompact_range (continuous_norm.comp (T.continuous_places ..))
        obtain ⟨b,hX⟩:= hb.bddAbove; refine ⟨‖v 0‖+max b 0,fun x=> (norm_add_le (v 0) (masked R.p.threshold B V x)).trans (add_le_add le_rfl ?_)⟩; by_cases h:Healthy R.p.threshold B x; rw [masked_eq _ _ _ _ h]; exact (hX ⟨x,rfl⟩).trans (le_max_left ..)
        rw [masked_ne _ _ _ _ h,norm_zero]; exact le_max_right ..
    choose d' hd' using hx
    let p(i:F.Index):= d' (Size.axis F i); let v:= ∑ i,p i; have hp i:0≤ p i:=(norm_nonneg (f _ (1:Config G n))).trans (hd' _ _); refine sheers f v s (fun k=> ⟨_,hd' _⟩) (fun x y U=>?_) h
    let V:= x-y; let q:= part T Λ D U; change dist (q x) (q y)≤ _; rw [dist_eq_norm,dist_eq_norm,← map_sub]; change ‖q V‖ ≤ v * ‖V‖
    nth_rw 1 [← Size.sum_axes F V]; rw [map_sum]; apply (norm_sum_le ..).trans; unfold v; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; rw [map_smul,norm_smul,mul_comm (p i)]; exact mul_le_mul (norm_le_pi_norm ..) (hd' ..) (norm_nonneg _) (norm_nonneg _)
end
variable {F} (T:SectionData F)
section sail
variable {p:ℕ→ Coefficient F n} (R:ℕ→ Rep G n) {x:ℕ→ Coin F A S}
variable (ht : ∀ᶠ n in atTop, ∃ K: Keeper (R n).p (R n).activities, Along (R n) S.orient ∧ (p n).Format 0 A (R n) ∧ Coin.uses (x n)=capture (p n) K) (hc: CauchySeq x)
include ht hc
lemma recto (he:CauchySeq (fun n=> (p n).x)): Confluence (fun n=> (p n).exponentialEntry 0 T (R n)):=by
    have hp:= sheers (logrem (F:=F) (A:=A) (S:=S)) 1 x (fun i=> ⟨_,fun U=> (lprop (x i) U).2⟩) (fun i j U=>by rw [dist_eq_norm,dist_eq_norm,← lports,one_mul]; exact (lprop ..).2) hc
    let f k U:= part T (0:Site n) D U (p k).x; refine Confluence.persist (f:=fun n U=>f n U+logrem (x n) U) (Confluence.bats (morsel F T he) hp) (ht.mono fun i hi=> ?_)
    obtain ⟨K,hq,hA,hV⟩:=hi; dsimp only; rw [← expo (p i) K T hA]; funext U
    unfold f logrem part Coefficient.exponentialEntry Coefficient.maskedTerm ; simp_rw [bookE,bookS,Matric.book_x]
    rw [hq.price,hV];rfl
lemma towers (i:Box n): Confluence fun n=> profile (R n).activities (p n).forced i:=by
    have h:= sheers (fun (f:Coin F A S)=>clore f i) S.k x (fun n=> ⟨_,fun U=> (heel (x n) i U).2⟩) (fun v w U=>by rw [dist_eq_norm,dist_eq_norm, ←hedge]; exact (heel ..).2) hc
    refine h.persist (ht.mono fun j hj=>?_) ; obtain ⟨K,hp,h,hV⟩:=hj; let Q:= capture (p j) K
    dsimp only; change clore (x j) i= _; unfold clore; rw [hV,← profited (p j) K]
    unfold profile barcode; rw [hp.force]
end sail
-- rotate scalars stepUp; closed representation
variable (m:Motion)(x:Site n)
lemma revive {f:ℕ→ Config G n→ℂ} (h:Confluence f) (t:ℂ): Confluence fun n=> radiant t m x (f n):=by
   unfold radiant stepUp Motion.scalar; split
   · exact ((h.alongside (pull m.1 x)).ahead star continuous_star).ahead (fun z=>t • z) (by fun_prop)
   exact (h.alongside (pull m.1 x)).ahead (fun z=> t • z) (by fun_prop)
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.towers
#print axioms YM.FullVolume.Retreat.revive
#print axioms YM.FullVolume.Retreat.recto
