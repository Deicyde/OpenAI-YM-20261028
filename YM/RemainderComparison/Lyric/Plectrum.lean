import YM.RemainderComparison.Lyric.Beat
import YM.MergeProof.Dreams

/-!
# Explicit disjoint score and syllables over all layouts

Thin: actual. Disconnected vs connected correction is in `Song` later.
Outputs on these exact addresses; prove equating the choice when plugging
any local real vacuum / mask on the AUX; for formal analogy register later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell
open Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ} {O:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)
-- ALL arrays, for sigma budgets. Option.Fin_p length(u).
abbrev Syllable (z:H.fragrances):= Option (Fin z.1) → Drums M S
variable (z:H.fragrances) (w:Syllable M H z)

def cadence := ((coefficient H.seam z.2)/↑(z.1+1).factorial : ℝ)

def page : Finset ι := univ.biUnion fun i=> (w i).val
def notes := ∑ i,(w i).val.card
def after := notes M H z w-(page M H z w).card
def invests (r:ι→ℝ) := ∏ i, ∏ j∈(w i).val,r j
def string (V:Config G c):= cadence H z * ∏ i,toe M H χ (z.2 i) (w i) V
def cut (V:Config G c):= RG.masked (Pressure.temp x) (reachability (H:=H) z) (string M H χ z w) V

def Turns := (↑(univ:Finset (Option (Fin z.1))): Set _).PairwiseDisjoint (fun i=> (w i).val)
omit [Fintype ι] in
lemma octave : after M H z w=0 ↔ Turns M H z w := by
   let f (i):= (w i).val
   have hl : (page M H z w).card ≤ notes M H z w:= Finset.card_biUnion_le
   unfold after Turns; rw [Nat.sub_eq_zero_iff_le]; constructor
   · intro hp i hi j hj hn
     by_contra he
     obtain ⟨x,hx,hx'⟩:= Finset.not_disjoint_iff.mp he
     let g k:= if k=i then (f k).erase x else f k
     have h:(univ.biUnion g)=page M H z w:=by
       ext k; constructor
       · intro h; obtain ⟨j,hv,hs⟩:= mem_biUnion.mp h; apply mem_biUnion.mpr; refine ⟨j,hv,?_⟩; unfold g at hs; split at hs; next=> exact mem_of_mem_erase hs
         next=> exact hs
       intro h; obtain ⟨j',hj',hk⟩:= mem_biUnion.mp h
       by_cases h:j'=i
       · subst j'; by_cases h:k=x
         · subst k; exact mem_biUnion.mpr ⟨j,Finset.mem_univ _,show x∈g j from by unfold g; rw [if_neg hn.symm]; exact hx'⟩
         exact mem_biUnion.mpr ⟨i,hj',show k∈ g i from by simp only [g, ↓reduceIte]; exact mem_erase.mpr ⟨h,hk⟩⟩
       exact mem_biUnion.mpr ⟨j',hj',show k∈g j' from by unfold g; rw [if_neg h]; exact hk⟩
     have ht : ∑ i, (g i).card < notes M H z w := by
       refine Finset.sum_lt_sum (fun k _=>Finset.card_le_card (show g k⊆ f k from ?_)) ⟨i,mem_univ _,?_⟩
       · unfold g; split
         · exact erase_subset ..
         rfl
       unfold g; rw [if_pos rfl]; exact Finset.card_lt_card (erase_ssubset hx)
     rw [← h] at hp; exact (not_lt_of_ge (le_trans hp Finset.card_biUnion_le)) ht
   intro he; exact (Finset.card_biUnion he).ge
omit [Fintype ι] in
lemma opus (h:Turns M H z w) (r:ι→ℝ): invests M H z w r=∏ i∈page M H z w,r i:= (Finset.prod_biUnion h).symm

variable (N : Captain H j q d v u A b r B e n χ)
include N
omit [Fintype ι] in
lemma scripted (V:Config G c) : cadence H z * (∏ i, Palette.act M H χ V (z.2 i).val (w i))=cut M H χ z w V:=by
   let f i V:=toe M H χ (z.2 i) (w i) V
   let Z:= reachability (H:=H) z; let t:= Pressure.temp x
   simp_rw [flagged_step M H χ N]; unfold cut; by_cases h: Healthy t Z V
   · rw [masked_eq _ _ _ _ h]; apply congr_arg; exact prod_congr rfl (fun i _=> masked_eq t (H.smallAt (z.2 i)) _ _
       (Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ _)) h))
   unfold t Z at h; rw [masked_ne _ _ _ _ h]; obtain ⟨x,hx,hf⟩:= Finset.not_disjoint_iff.mp h; obtain ⟨i,hi,hv⟩:= mem_biUnion.mp hx; exact mul_eq_zero_of_right _ (Finset.prod_eq_zero hi
       (masked_ne _ (H.smallAt (z.2 i)) _ V (Finset.not_disjoint_iff.mpr ⟨x,hv,hf⟩)))
lemma chorus (r:ι→ℝ)(U): H.trainedMill (Palette.color M H χ U r) z=
       ∑ w:Syllable M H z, invests M H z w r*cut M H χ z w U:=by
   let f i j:=(∏ k∈(j:Drums M S).val,r k)*act M H χ U (z.2 i).val j
   rw [show H.trainedMill (Palette.color M H χ U r) z= cadence H z*∏ i,∑ j,f i j from ?_]
   swap; · change coefficient H.seam z.2*(∏ i,∑ j,f i j)/↑(z.1+1).factorial =_ ; unfold cadence; ring
   rw [Fintype.prod_sum f, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _=>?_)
   rw [← scripted M H χ z j N]; unfold f; rw [prod_mul_distrib]; exact (mul_left_comm ..)

omit N
omit [Fintype ι] in
lemma homily (r:ι→ℝ) (y:ℝ) (p': Finset ι) : invests M H z w (ways r y p')= (y^after M H z w) * Merge.Switch.click (page M H z w) (invests M H z w r) y p':=by -- p'? declare
   by_cases he : page M H z w ⊆ p'
   · have ht i : (w i).val ⊆ p':= Finset.Subset.trans (subset_biUnion_of_mem (fun i=> (w i).val) (Finset.mem_univ i)) he
     unfold invests; rw [Switch.click,if_pos he]; simp_rw [amplitudes,Switch.click,if_pos (ht _),prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← mul_assoc (y^_), ← pow_add]
     rw [show after M H z w+(page M H z w).card=∑ i,#(w i).val from Nat.sub_add_cancel (show #(page M H z w) ≤ notes M H z w from Finset.card_biUnion_le)]
   rw [Switch.click,if_neg he,mul_zero]
   obtain ⟨k,hk,hM⟩:=Finset.not_subset.mp he
   obtain ⟨i,hi,hv⟩:=mem_biUnion.mp hk
   exact Finset.prod_eq_zero hi (Finset.prod_eq_zero hv (if_neg hM))

open Switch
include N
lemma scripts (r:ι→ℝ)(V)(v):
    jet (Palette.song M H χ r z V) v = ∑ w:Syllable M H z, if Turns M H z w ∧ v=page M H z w then invests M H z w r*cut M H χ z w V else 0 := by
    let U w:= invests M H z w r*cut M H χ z w V
    let g (t:ℝ) a := ∑ w:Syllable M H z,t^after M H z w*bench (page M H z w) (U w) a
    have hp : Models (Palette.song M H χ r z V) g := by
      constructor
      · intro x _; ext p; rw [song, Lyric.chorus M H χ z N]
        unfold Switch.value g; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _=> ?_)
        have hh:= congr_fun ((modelClick (page M H z i) (U i)).current x ‹_›) p
        unfold Switch.value at hh; rw [homily M H z i r]
        calc
          _= (x^after M H z i)*∑ y∈p.powerset,x^y.card*bench (page M H z i) (U i) y:= by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>mul_left_comm ..
          _=_:=by rw [hh]; unfold click U; split_ifs <;> ring
      intro a; refine tendsto_finsetSum _ fun i _=> ?_; exact ((tendsto_id.mono_left nhdsWithin_le_nhds).pow (after M H z i)).mul tendsto_const_nhds
    rw [hp.exact]; exact Finset.sum_congr rfl fun i _=> by
       unfold bench
       by_cases he:Turns M H z i; · simp [he,(octave M H z i).2 he,U]
       simp [he,mt (octave M H z i).1 he]
end YM.RemainderComparison.Lyric
