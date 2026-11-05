import YM.OPE.Log.Moderate
import YM.OPE.Sweep.Net
import YM.OPE.Log.PaidMove
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Extra.Multi Push GridApprox.Nil Ac Pressure Corona Next.Rank Station Source Local Menu Extra.Histories PhysicalNext.Repeat
open scoped Topology BigOperators Classical
variable {G:Gauge}{n n':Side} {S:Schedule} {V I J : Type}[Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{A:History G}{E:V→Site n}{P:V→Motion}
  {v:V}{o:V×I→Site n} {b w ℓ : ℕ}
variable (i:I)(hb:0<b)

include hb in
/-- Net with a distinguished representative. The surjection centers
are repeated, so all copies agree on the group overlap simultaneously. -/
lemma cozy (f:I→Site n)(hw:0<w)(hg: ¬ OPE.Log.Moderate f b w) :
    ∃ (J:Type) (_:Fintype J) (_:DecidableEq J) (L:Fibers I J),
      L.twig (L.bunch i)=i ∧ Fintype.card J<Fintype.card I ∧ OPE.Log.Moderate (f ∘ L.twig) b w ∧ ∀ x:I,separation (f x) (f (L.twig (L.bunch x)))<b*w:=by
    classical
    let p(a : Finset I):= i∈a∧(a:Set I).Pairwise (fun x y=>b*w≤ separation (f x) (f y)); let S:= univ.filter p; have ht x:x∈S↔ p x:=mem_filter.trans (and_iff_right (mem_univ _))
    have hξ:p {i}:= ⟨mem_singleton_self _,by simp⟩
    obtain ⟨s,hp,hh⟩:= Finset.exists_max_image S Finset.card ⟨{i}, (ht _).2 hξ⟩; have hs: i∈s:=(ht s|>.1 hp).1; have he :=(ht s|>.1 hp).2
    have hX (x:I) (hx:x∉s) : ∃ a∈s,separation (f x) (f a) < b*w:=by
       by_contra! h; have hy:p (insert x s):=by
         refine ⟨mem_insert_of_mem hs,fun i hi j hj hij=>?_⟩; rcases mem_insert.mp hi with hi|ht'; subst i
         · exact h j ((mem_insert.mp hj).resolve_left hij.symm)
         rcases mem_insert.mp hj with rfl|hh'; · rw [separation_comm]; exact h i ht'
         exact he ht' hh' hij
       have hu:=hh (insert x s) ((ht _).2 hy); rw [card_insert_of_notMem hx] at hu; omega
    have h₀:∀ x, ∃ j : (↑s:Type), separation (f x) (f j.val)< b*w ∧ (x∈s→j.val=x):=by
       intro x; by_cases ht:x∈s
       · exact ⟨⟨x,ht⟩, by simpa only [separation_self] using (mul_pos hb hw), fun _=>rfl⟩
       obtain ⟨j,hj,H⟩:=hX x ht; exact ⟨⟨j,hj⟩,H,fun h=> (ht h).elim⟩
    choose K hK hJ using h₀; let F:Fibers I (↑s:Type):= ⟨K,Subtype.val,fun x=> Subtype.ext (hJ x x.property)⟩
    refine ⟨_,inferInstance,inferInstance,F,hJ i hs,?_ ,⟨fun i j hij=> he i.property j.property (mt Subtype.ext hij)⟩,hK⟩
    rw [Fintype.card_coe]; refine lt_of_le_of_ne (Finset.card_le_univ _) ?_; intro H; rw [Finset.eq_univ_of_card s H] at he; exact hg ⟨fun i j hij=> he (mem_univ i) (mem_univ j) hij⟩

open OPE.Log
lemma Cross.earns (h:Cross b o)(hT:Collar o v E P)(hs:Moderate (fun i:I=>o (v,i)) b w)(hw:w≤b): Moderate o b w:=by
    refine ⟨?_⟩; rintro ⟨i,b'⟩ ⟨j,c⟩ hp; by_cases ht:i=j; · subst j; rw [hT.widths i]; exact hs.wide b' c (by rintro rfl; exact hp rfl)
    exact ((show b*w ≤ b^2 from by rw [pow_two]; gcongr)).trans (h _ _ ht)
-- Wakes
include hb in
lemma Collar.cozy (h:Collar o v E P)(hv:Cross b o)(hw:0<w)(he:w≤b)(hd:¬ Moderate o b w):
    ∃ (J:Type)(_ : Fintype J)(_ : DecidableEq J)(F:Fibers I J), F.twig (F.bunch i)=i ∧ Fintype.card J<Fintype.card I∧ Moderate (o ∘ (partialGroup V F).twig) b w ∧ ∀ j:V×I, coverNumber b ({o (j.1,F.twig (F.bunch j.2)),o j}:Support _) ≤ w+2:=by
    obtain ⟨J,hJ,hI,F,hF,h',hc,hK⟩:= ManyCopies.cozy i hb (fun i:I=> o (v,i)) hw (fun hδ=> hd (hv.earns h hδ he)); refine ⟨_,hJ,hI,F,hF,h', (hv.shrunk F).earns (h.shrunk F) hc he,?_ ⟩; rintro ⟨j,x⟩; apply moderateRadius; rw [separation_comm,h.widths]; exact (hK x).le
variable [DecidableEq V][Fintype V]
lemma Cross.counts (h:Cross b o) (hz:Fintype.card I≤ℓ) : 0<b → Occupancy o ℓ:=by
    intro hb y; let s:=univ.filter (fun i:V×I=>o i=y); have hf i (h:i∈s):= (mem_filter.mp h).2; have hi:=card_image_of_injOn (f:=Prod.snd) (s:=s) (by
       intro i hx j hj he; apply Prod.ext _ he; by_contra ht; have h:=h i j ht; rw [hf i hx,hf j hj,separation_self] at h; exact (pow_pos hb 2|>.not_ge) h)
    exact le_trans hi.ge ((card_le_univ _).trans hz) -- hi relation?
end YM.MergeProof.Ribbons.ManyCopies
