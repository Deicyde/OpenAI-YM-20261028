import YM.FullVolume.Reel.Treasure
import YM.FullVolume.Nectar.Vau
import YM.MergeProof.Close
/-!
 # Pact calculus on source payloads

 Weighted ℓ¹ over supports and modes SIMULTANEOUSLY in the real analytic
 series; values in all-configuration sup norm (not a.e.).

 `Repegs` works at exactly the same analytic width. We trim absent modes, all
 real `s` at once; crucial for no dimension/volume factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson
variable {V I:Type}[DecidableEq V] [Fintype V] [Fintype I]{B:Marker.Census V}{G:Gauge}{n:Side}
variable {F:sun→I→ Config G n→Poly B}{S:I→Support n}{p q v t c:ℝ}{a:ℕ}{w w':V→ℝ}
    {k k':Finset B.Mode}{x: V→ Site n}(hw:∀ i,0<w i)(hC:0≤c)
-- k normally positive or hot. quiet allowed in some helpers.
abbrev Pact (w:V→ℝ) (S:I→Support n) (F:sun→ I→ Config G n→ Poly B) (k:Finset B.Mode) (a:ℕ)(p v:ℝ):Prop:= Treasure (fun i:I × ↑k=> Real.exp (p*coverNumber a (S i.1))* Poly.toll w i.2.val) (fun s (i:I × ↑k) U=> (F s i.1 U).part i.2.val) v
/-- All positive modes; excludes vacuum `quiet`. -/
def lively (B:Marker.Census V):Finset B.Mode:=univ.erase B.quiet
/-- Modes of at least two marked sites, stove budget. -/
def multiple (B:Marker.Census V):Finset B.Mode:= univ.filter (fun i=>2 ≤ i.val.card)
lemma multiplicity (i:B.Mode) : i∈multiple B ↔ 2 ≤ i.val.card:=by simp [multiple]
lemma lively_ne (i:B.Mode): i∈ lively B ↔ i≠B.quiet:=by simp [lively]
lemma multiple_lively : multiple B ⊆ lively B:=by
  intro i hi; apply (lively_ne _).2; intro h
  subst i; simp [multiple,Marker.Census.quiet] at hi
abbrev G1 (K:sun→ I→ Config G n→ Poly B)(s:sun)(i:I)(y:Config G n):Poly B:=Accent.octave (K s i y)
namespace Pact
variable (h:Pact w S F k a p v)
include hw h
lemma price : 0≤v:= h.positive (fun _=>mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le)
lemma subtype (hs:k'⊆k): Pact w S F k' a p v:=by
    obtain ⟨b,hb,hB⟩:=h.coins
    let f : I × ↑k' → I × ↑k:= fun j=> ⟨j.1, ⟨j.2.val,hs j.2.property⟩⟩
    have hf: Injective f:=fun i j h=> Prod.ext (congr_arg (fun j=> j.1) h) (Subtype.ext (congr_arg (fun j=> j.2.val) h))
    let C i:=b (f i)
    refine ⟨C,?_,fun i=>hB (f i)⟩
    let g (j:I× ↑k):=Real.exp (p*coverNumber a (S j.1))*Poly.toll w j.2.val*b j
    change ∑ j:I× ↑k', g (f j) ≤ v
    rw [← Finset.sum_image hf.injOn]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le) (hB i).positives)).trans hb
lemma lower (hp:q≤p): Pact w S F k a q v:=by
    obtain ⟨b,hb,hB⟩:= h.coins
    refine ⟨_, (sum_le_sum (fun i hi=>?_)).trans hb, hB⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (Poly.worth hw _).le) (hB i).positives
omit h
lemma alter (h:Pact w S F k a (p+q) v) (hv:∀ s i,Borne x (S i) (F s i) t)(hh: k⊆multiple B)(ht: Repegs x a w w' q c B)(hz:0≤c): Pact w' S F k a p (c*v):=by
    obtain ⟨b,hb,hB⟩:= h.coins
    let N(i:I × ↑k):Prop:= i.2.val.val.image x ⊆ S i.1
    let f(i:I × ↑k):= if N i then b i else 0
    refine ⟨f,?_,fun i=>?_⟩
    · apply le_trans _ (mul_le_mul_of_nonneg_left hb hz)
      rw [Finset.mul_sum]; apply sum_le_sum; intro i _; unfold f
      split
      next h=>
         let T:= coverNumber a (S i.fst)
         refine le_trans (b:=Real.exp (p*T) * (c * Poly.toll w i.snd.val* Real.exp (q*T)) * b i) ?_ (le_of_eq ?_)
         · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht _ ((multiplicity _).1 (hh i.2.property)) _ h) (Real.exp_pos _).le) (hB _|>.positives)
         unfold T; rw [add_mul,Real.exp_add]; ring
      rw [mul_zero]
      exact mul_nonneg hz (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le) ((hB i).positives))
    unfold f; split; exact hB _
    next hn=>
         have ht(s U): (F s i.1 U).part i.snd.val=0:= of_not_not (fun h=> hn ((hv s _).place _ _ h))
         simp_rw [ht]
         exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
omit hw
lemma eighth_part (h:Pact w S F k a p v) (hh:k⊆multiple B):Pact w S (G1 F) k a p v:=by
   obtain ⟨b,hb,hB⟩:= h.coins; refine ⟨b,hb,fun i=>?_⟩
   simp_rw [G1,Accent.crest _ _ ((multiplicity _).1 (hh i.2.property))]
   exact hB i
end Pact
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.Pact.alter
