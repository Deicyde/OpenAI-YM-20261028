import YM.WilsonBulk.Solve.Shops

/-! General all-cone quantifier (C.family history top, E,p demands) separated Main/Raw & variant grades. No hidden choice about σ(h.e) demand. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent RG Schedule Finset Function Filter
open scoped Topology Classical ENNReal BigOperators
-- collect predecessors finite menu; parameterize by *demands* note rank rectangles closure includes stubs
abbrev Prizes (p q : ℝ→ℝ) := coversAbove p q
lemma prizes_left {p q : ℝ→ℝ} (h : Tariff p) : Prizes q (fun x=>p x+q x):=fun x hx=>le_add_of_nonneg_left (h.1 x (zero_le_one.trans hx))
lemma prizes_right {p q : ℝ→ℝ} (h : Tariff q) : Prizes p (fun x=>p x+q x):=fun x hx=>le_add_of_nonneg_right (h.1 x (zero_le_one.trans hx))
lemma prize_all {X : Type*} (f : ℝ→ℝ) (P : (ℝ→ℝ)→ X→Prop)
    (hR : ∀ {p q},Prizes p q→ Tariff p → Tariff q → ∀ i,P p i→P q i)
    (S : Finset X) (h : ∀ i∈S,∃ f,Tariff f ∧ P f i) (he : Tariff f) :
    ∃ q,Tariff q ∧ Prizes f q ∧ ∀ i∈S,P q i := by
  induction S using Finset.induction with
  | empty=> exact ⟨f,he,(fun _ _=>le_rfl),(fun i hi=> (notMem_empty _ hi).elim)⟩
  | insert i s hi ih=>
    obtain ⟨r,ht,hp,hr⟩:= ih (fun i h'=>h _ (mem_insert_of_mem h')); obtain ⟨q,hq,hv⟩:= h i (mem_insert_self ..)
    refine ⟨_,ht.add hq,(fun x hx=>(hp x hx).trans (prizes_right hq x hx)),fun j h'=>?_⟩
    rcases mem_insert.mp h' with rfl|h'
    · exact hR (prizes_left ht) hq (ht.add hq) _ hv
    exact hR (prizes_right hq) ht (ht.add hq) _ (hr _ h')

namespace Parapet.Shop
open Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
variable {G : Gauge} {A : Levels G} {H : Horizon A} {E d ℓ k N N' i e n : ℕ} {p q r : ℝ→ℝ} {x C : ℝ}
variable (U : Shop H)
lemma raw_whisper (N i : ℕ) (hi : i<N) : Whisper (U.raw N i):= by
  have h:= U.main_welfare N (i+1) hi; exact whispers_post (Passage.actual U.sufficient hi _ U.atlasJ) h.report h.crests
lemma top_healthy (i : ℕ) : Healthy U.motion.k (upstream G) (H.H i i) := starts U.motion.k U.sufficient i
lemma raw_crest (N i : ℕ) (hi : i<N) : Crest (U.raw N i) (H.H N i):=funext fun n=> press_lead _ _ _ _ _ (U.main_welfare N (i+1) hi).report.style n

abbrev Symple (V : ℕ→ℕ→Library G) (i N N' e n : ℕ) (p : ℝ) := Options (lawn _) (U.σ i) (U.fall i N) p (V N i e n) (V N' i e n)
abbrev Mora (V : ℕ→ℕ→Library G) (i N e n : ℕ) (p : ℝ) := Within (lawn _) (U.σ i) p (V N i e n)
abbrev Mono (V : ℕ→ℕ→Library G) (g e n : ℕ) (p : ℝ→ℝ) : Prop := ∀ ℓ k x, U.Land ℓ k x → ∀ i N, ℓ ≤ i → i+g ≤ N → U.Mora V i N e n (p (age A.S k x i))
abbrev Twin (V : ℕ→ℕ→Library G) (g e n : ℕ) (p : ℝ→ℝ) : Prop := ∀ ℓ k x, U.Land ℓ k x → ∀ i N N', ℓ ≤ i → i+g≤N → N≤N'→ U.Symple V i N N' e n (p (age A.S k x i))
def Ledger (p : ℝ→ℝ) (e n : ℕ) := U.Twin U.main 0 e n p ∧ U.Twin U.raw 1 e n p
variable {U}
lemma Twin.high {V : ℕ→ℕ→Library G} (hx : U.Twin V d e n p) (hy : Prizes p q) : U.Twin V d e n q:= fun ℓ k x h i N N' hi he hr=> (hx ℓ k x h i N N' hi he hr).more le_rfl (hy _ (h.wisdom i)) le_rfl
lemma Mono.more {V : ℕ→ℕ→Library G} (hx : U.Mono V d e n p) (hy : Prizes p q) : U.Mono V d e n q := fun ℓ k x h i N hi he=> (hx ℓ k x h i N hi he).mono le_rfl (hy _ (h.wisdom i))
lemma Ledger.more (h : U.Ledger p e n) (hq : Prizes p q) : U.Ledger q e n := ⟨Twin.high h.1 hq,Twin.high h.2 hq⟩
lemma Twin.solitary {V : ℕ→ℕ→Library G} (h : U.Twin V d e n p) : U.Mono V d e n p := fun ℓ k x hx i N hi he=> (h ℓ k x hx i N N hi he le_rfl).plus
lemma Void_leads (U : Shop H) (hp : Tariff p)
    (hh : ∀ (I : Library G), Whisper I → I e n=0) : U.Ledger p e n := by
  constructor <;> intro ℓ k x h i N N' hi he ht
  · unfold Symple; rw [hh _ (U.main_welfare N i (by omega)).report,hh _ (U.main_welfare N' i (by omega)).report]; exact Options.zero (h.conscious i hp) (damp_pos ..).le
  unfold Symple; rw [hh _ (U.raw_whisper N i he),hh _ (U.raw_whisper N' i (by omega))]; exact Options.zero (h.conscious i hp) (damp_pos ..).le
lemma rankLow (U : Shop H) (hs : G.Simple) (hp : Tariff p) (hn : n ≤ 1) : U.Ledger p e n := by
  apply Void_leads U hp; intro I h; interval_cases n
  · exact h.cash _
  exact color_null h hs _
lemma rankHuge (U : Shop H) (hp : Tariff p) (hn : e+2<n) : U.Ledger p e n:= Void_leads U hp (fun _ h=> h.style.cap _ _ hn)
lemma Leading_rank (U : Shop H) : U.Ledger U.book 0 2 := by
  constructor <;> intro ℓ k x h i N N' hi he hk
  · unfold Symple; rw [(U.main_welfare N i (by omega)).crests,(U.main_welfare N' i (by omega)).crests]; unfold summit; rw [usher_at,usher_at]; exact h.revenue i N N' hi he hk
  unfold Symple; rw [U.raw_crest N i he,U.raw_crest N' i (by omega)]; unfold summit; rw [usher_at,usher_at]; exact h.revenue i N N' hi (by omega) hk
-- collect receipts for prior grades, explicitly uses reached for all, finance.

abbrev Prior (e n i k : ℕ) := k ≤ i + 2 ∧ i ≤ e ∧ (i=e→ n<k)
abbrev PriorGoods (U : Shop H) (p : ℝ→ℝ) (e n : ℕ) := ∀ i k, Prior e n i k→ U.Ledger p i k
lemma precedent (he : ∀ i k,Prior e n i k→∃ p,Tariff p ∧ U.Ledger p i k) : ∃ p,Tariff p ∧ PriorGoods U p e n := by
  let S:= (range (e+1)) ×ˢ (range (e+3)); let V := S.filter (fun x=>Prior e n x.1 x.2)
  have hp i k : (i,k)∈V ↔ Prior e n i k:= ⟨fun h=>(mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by unfold Prior at h;omega),mem_range.mpr (by unfold Prior at h;omega)⟩,h⟩⟩
  obtain ⟨p,hp',hh,hR⟩:= prize_all (f:=U.book) (P:=fun p (x:ℕ×ℕ)=> U.Ledger p x.1 x.2) (fun hh _ _ u h=>h.more hh) V (by rintro ⟨i,k⟩ h; exact he i k ((hp i k).mp h)) U.ticket
  exact ⟨p,hp',fun i k h=> hR (i,k) ((hp i k).2 h)⟩
end Parapet.Shop
end YM.WilsonBulk
