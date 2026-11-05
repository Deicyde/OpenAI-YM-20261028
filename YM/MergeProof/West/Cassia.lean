import YM.MergeProof.West.Chasm
import YM.MergeProof.West.Fix
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middle C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNow (d:=d) c R x b hk h q T τ U ε)
lemma cellular {V:Type} (X:Clump V) (a b:V→ℂ) (r ε : ℝ) (hr:1≤r) (he:0≤ε) (ha:∀ i,‖a i‖≤r) (hb:∀ i,‖b i‖≤ r) (hd:∀ i,‖a i-b i‖≤ ε): ‖honors X a-honors X b‖ ≤ West.cents X r * ε := by
  let M:ℂ →ₐ[ℂ] poly (Fin 1):= Algebra.ofId ..
  have ht (p:ℂ) : coin (M p)=‖p‖:=by change coin (_root_.MvPolynomial.C _) = _; simp [coin]
  rw [← ht, map_sub, g_honors,g_honors]; exact pursesC X _ _ _ _ hr he (fun i=> ht _ ▸ ha i) (fun i=> ht _ ▸ hb i) (fun i=> le_trans (le_of_eq (show coin (M _-M _) = ‖a i-b i‖ by rw [← map_sub M,ht])) (hd i))

def grater (n:ℕ)(j t:ℝ):=(∑ v:modes (Fin n), West.cents (yolk (Fin n) v) j)*t
lemma crumbling {Z A:veil (Fin n)}{u:modes (Fin n)} (j t:ℝ) (h:1≤j) (ht:0≤ t) (hp:A.part (quiet _)=1) (hx:Z.part (quiet _)=1) (H:∀ i:modes (Fin n),i.val ⊆ u.val → ‖A.part i‖≤j ∧ ‖Z.part i‖≤j ∧ ‖A.part i-Z.part i‖≤ t): ‖(connected A hp).part u-(connected Z hx).part u‖≤ grater n j t:=by
  let Y:=Flux.bed u.val A; let X:=Flux.bed u.val Z
  have hh (A : veil (Fin n)) (H:A.part (quiet _)=1): (connected A H).part u=(medicine (yolk (Fin n)) (Flux.bed u.val A)).part u:= by
    have he:= Flux.bedrock u.val (connected_spec A H)
    rw [← Expands.uniq he (belly _ (by rw [Flux.shelve,if_pos]; exact H; exact Finset.empty_subset _)),Flux.shelve,if_pos (Finset.Subset.refl _)]
  have hp'(i:modes (Fin n)): ‖X.part i‖≤j ∧ ‖Y.part i‖≤j ∧ ‖Y.part i-X.part i‖ ≤ t:=by
    unfold X Y; rw [Flux.shelve,Flux.shelve]; split
    · next hi=> exact ⟨(H i hi).2.1,(H i hi).1,(H i hi).2.2⟩
    simp [zero_le_one.trans h,ht]
  rw [hh A hp,hh Z hx]; exact (cellular (yolk (Fin n) u) Y.part X.part j t h ht (fun i=> (hp' i).2.1) (fun i=>(hp' i).1) (fun i=>(hp' i).2.2)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> penny _ _ (zero_le_one.trans h)) (Finset.mem_univ u)) ht)

variable (W: Fin n → poly (Chamber G C.S k p))
variable (hP : ∀ u,vista R W hk u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)
variable (hx:roomTest C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε) (he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ u, Poetic (vista R W hk u)) (hs:∀ u,totalDegree (vista R W hk u)≤ D) (hu:∀ u,coin (vista R W hk u)≤ r) (hp:∀ u : Manner n,∀ i'∈(vista R W hk u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))

local notation "O"=> offerNow E (vista R W hk)
set_option quotPrecheck false
local notation "F"=> Array.reorient (Ship.yard C b c.allow p) T.1 (spunW R W hk.le (vantage E))

include hP hx t Hv he he' hr H hs hu hp
lemma f_inale (M:ℝ) (hM : 1≤ M)(m:ℝ) (hD:gentility B ε r D n ≤ m) (hm:0≤m) (hz:∀ v:modes (Fin n),v.val⊆ T.2.val.val.val → ‖text (vantage E) (heads R W hk.le v)‖ + m ≤ M):
    let j:= T.2; let V:= gloryFt x b p c.allow hk.le h T.1 j.val (anneals C c i) (vista R W hk.le j.val.val); ‖(leadFt E (offerNow E (vista R W hk))).part j.val.val-V U‖ ≤ grater n M m:=by
   intro j V'; let L:=leadFt E (offerNow E (vista R W hk)); let O':=planterFt E (offerNow E (vista R W hk)); let K:=Ship.yard C b c.allow p
   let L':= Array.reorient K T.1 (t_cum R W hk.le (vantage E)); let W':= (F)
   have hh:= expanders R W hk.le (vantage E); have hp : Expands L' W':= by
     refine ⟨?_,?_⟩
     · dsimp only [L',Array.reorient]; split; · exact (congr_arg star hh.1).trans (star_zero _)
       exact hh.1
     rw [show Poly.pass L'= _ from (Array.turns_pass K T.1 _).symm,hh.2]
   have hX : V' U=L'.part j.val.val:= by unfold L' Array.reorient V' gloryFt Edition.dot; dsimp only [K]; split <;> rfl
   have ht:W'.part (quiet _)=1:=by rw [← hp.2]; exact Poly.pass_part _ hp.1
   rw [hX, hp.uniq (connected_spec W' ht)]; apply crumbling M m hM hm
   intro i hi; have hu:= (flight_pay E W hP hx t Hv he he' hr H hs hu ‹∀ u : Manner n,_› i hi).trans hD
   have hs:=hz i hi; let D:= ‖text (vantage E) (heads R W hk.le i)‖; have hD : ‖W'.part i‖=D:= by dsimp only [W',Array.reorient];split; exact norm_star _; rfl
   refine ⟨?_,hD.trans_le (by linarith only [hs,hm]),hu⟩
   let u:=W'.part i;exact ((norm_sub_norm_le (O'.part i) u).trans hu)|> (fun hx=> by change ‖O'.part i‖≤M; unfold u at hx;rw [hD] at hx; unfold D at hx;linarith only [hx,hs])
end YM.Next.Rank.Tapes.West
