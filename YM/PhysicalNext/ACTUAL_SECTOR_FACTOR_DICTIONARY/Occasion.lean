import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Courtesy

/-!
# Rolling up the review bills

Use literal covered packet/schedule normalizations. All identities
still pointwise in the physical variables, not requiring any putative
output/local coefficient envelopes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.PhysicalNext.Dictionary.Formal
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Lobbies SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D) (F : Forest S.ratio) (A : Stores S) (k₀ k : S.Choices) (V : Config G c) (Z : Art I D) (s : ℝ) (m : Finset I)
    (i : Head I) (v : Versions i) (l : Tryouts S)
local notation "H₀"=>chosen D F k₀ A k
local notation "T"=>Voice.Check.Test
local notation "B"=>radiusB D.betaHat
local notation "P"=>submit i D A v l
local notation "Q"=>Fleet.packs S (hump B) (Fleet.manifest A)
local notation "X"=>construct (I:=I) D A

-- Prerequisites for Art not needed yet. Keep beam variants until later.
def lookup (j : ℕ) := Shipment.answer (fun l=>(j,l) ∈ torn i)
def lamps (p : Refs G f) : ℂ := (∏ j∈team i, job D Z j (lookup i j) F A (team i) k V p) * (∏ j∈coin i,Z.units j) *
    ∏ j : menu i, choices D Z s (bead j (v j)) F A (team i) k V p

lemma qualifies (j : ℕ) : qualifierAt (P) j = lookup i j := by
  unfold qualifierAt lookup
  apply congr_arg Shipment.answer
  funext x; rw [propext (storeworks D A i v l _), propext (bought i v l _)]

include h
lemma reserved_page (p : Refs G f) : ∏ j∈(Q), Booklet.vitalPage D j F A (team i) k V p = sealedBook D F A k V (team i) p := by
  have hp : Pieces (Fleet.spans S (hump B)) (Q) := Words.partition ..
  let Z := ({names:=fun _=>∅,sig:=fun _ _=>∅,score:=0,essay:=0,units:=0,plot:=fun _=>∅,origin:=id}: Art (Site f) D)
  have hk {u} (he : u∈(Q)) {v} (hi : v∈(Q)) (ht : u≠v) := Booklet.sheets D Z h.toApp ∅ (Finset.Subset.refl _) (Finset.Subset.refl _) hp.1 he hi ht F A
  unfold sealedBook invoked volumes Booklet.vitalPage; rw [Finset.prod_mul_distrib, ←Real.exp_sum]
  rw [Finset.prod_biUnion (fun _ hi _ hj he=> (hk hi hj he).1),Finset.sum_biUnion (fun _ hi _ hj he=>(hk hi hj he).2)]

omit h in
lemma offerings (ht : progress D A F i l) (p : Refs G f) :
    let q := shops i v l
    ∏ j∈q, choices D Z s j F A (team i) k V p =
      ((tickets D F A k V (team i) s p l : ℝ):ℂ) * ((∏ j∈coin i,Z.units j) *∏ j:menu i, choices D Z s (bead j (v j)) F A (team i) k V p) := by
  intro q; unfold q shops tickets Optional.subsetTerm; simp_rw [Finset.prod_disjSum]
  let Y := fun j=>choices D Z s j F A (team i) k V p
  have h₁ (j : T c f) (hj:j∈l.1) : Y (.inl j)= (↑(examFee D F A k V (team i) p j) : ℂ) := by unfold examFee; rw [if_pos (ht.2.1 j hj)]; rfl
  have h₂ (j) (hj:j∈l.2) : Y (.inr (.inl j))= (↑(volley D F A k V (team i) s p j) : ℂ) := by unfold volley; rw [if_pos (ht.2.2 j hj)]; rfl
  have he : ∏ j∈torn i, Y (.inr (.inr (.inr j)))=1 := Finset.prod_eq_one fun _ _=>rfl
  let R := ∏ j : menu i,Y (bead j (v j))
  have hf : (∏ j∈curtains i v,Y (.inr (.inr (.inl (.inr j)))))=R := by rw [curtains, Finset.prod_map]; rfl
  rw [if_pos ht.1]
  change (∏ j∈l.1,Y (.inl j)) * ((∏ j∈l.2,Y (.inr (.inl j)))*(((∏ j∈coin i,Z.units j) * _)*_))=_
  rw [Finset.prod_congr rfl h₁,Finset.prod_congr rfl h₂,he] -- hf
  change _*((_)*((_* (∏ j∈curtains i v,Y (.inr (.inr (.inl (.inr j)))))) *1))=_
  rw [hf]; change _=_*(_*R); push_cast; ring

lemma program (uPAGE : (H₀).Visual) : crude D Z s F V A m (P) k uPAGE =
    if welcomes D A Z i m then
      let p:=Print.backdrop D.betaHat A F uPAGE
      lamps D F A k V Z s i v p * (↑(sealedBook D F A k V (team i) p * tickets D F A k V (team i) s p l) : ℂ)
    else 0 := by
  unfold crude
  by_cases he : welcomes D A Z i m
  swap
  · rw [if_neg he,if_neg (fun hz=>he ((listed D A F Z i v l m).mp hz).1)]
  rw [if_pos he]; dsimp only
  let p:=Print.backdrop D.betaHat A F uPAGE
  by_cases ht : progress D A F i l
  swap
  · rw [if_neg (fun hz=>ht ((listed D A F Z i v l m).mp hz).2)]
    have hq : tickets D F A k V (team i) s p l=0 := by
      by_contra hz; have hi:=left_ne_zero_of_mul hz; have hj:=right_ne_zero_of_mul hz
      apply ht
      have hp : Fleet.pure Prod.fst l.2 := of_not_not (fun H=>hj (if_neg H))
      refine ⟨hp,fun j hu=>of_not_not (fun hh=>?_),?_⟩
      · have HB : (∏ u∈l.1,examFee D F A k V (team i) p u) ≠ 0 := hi
        exact Finset.prod_ne_zero_iff.mp HB j hu (if_neg hh)
      intro j hu; by_contra! hh
      apply Finset.prod_ne_zero_iff.mp (show (∏ u ∈ l.2, volley D F A k V (team i) s p u) ≠ 0 from ?_) j hu (if_neg hh)
      intro H; exact hj ((if_pos hp).trans H)
    rw [hq,mul_zero,Complex.ofReal_zero,mul_zero]
  rw [if_pos ((listed D A F Z i v l m).mpr ⟨he,ht⟩), submit,Fleet.draft_k]
  rw [show Fleet.draft (hump B) A (team i) (shops i v l) = (P) from rfl]
  let f := fun j=> shutter D Z s j (P) F A (team i) k V p
  change (∏ j ∈ ((Q).disjSum ((team i).disjSum (shops i v l))), f j)= lamps .. * _
  rw [Finset.prod_disjSum,Finset.prod_disjSum]
  have H (j : ℕ) : f (Sum.inr (Sum.inl j)) = job D Z j (lookup i j) F A (team i) k V p := by
    unfold f shutter; rw [← qualifies D A i v l j]
  unfold lamps
  let a:=sealedBook D F A k V (team i) p
  have ha : ∏ j∈(Q),f (.inl j)=(↑a:ℂ) := by
    unfold a; rw [← reserved_page D h F A k V i p]; push_cast; rfl
  let U:=∏ j∈coin i,Z.units j
  let R:=∏ j : menu i, choices D Z s (bead j (v j)) F A (team i) k V p
  let b:=tickets D F A k V (team i) s p l
  have hb : ∏ j∈shops i v l,f (.inr (.inr j))=(↑b:ℂ)*(U*R) := offerings D F A k V Z s i v l ht p
  change _= ((_*U)*R)*(↑(a*b):ℂ)
  rw [ha,hb,Complex.ofReal_mul]; simp_rw [H]; ring

lemma purchase (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V)
    (hs : Summable (fun l=> crude D Z s F V A m (submit i D A v l) k uPAGE)) :
    HasSum (fun l=> crude D Z s F V A m (submit i D A v l) k uPAGE)
      (if welcomes D A Z i m then
        lamps D F A k V Z s i v (Print.backdrop D.betaHat A F uPAGE) * (↑((∏ j,exam D F A k₀ k V (team i) uPAGE j)*Real.exp ((H₀).sumValue V uPAGE)):ℂ)
      else 0) := by
  simp_rw [program D h F A k₀ k V Z s m i v _ uPAGE] at hs ⊢
  by_cases he : welcomes D A Z i m
  · simp_rw [if_pos he] at hs ⊢; exact wing D h F A k₀ k V (team i) s uPAGE hc he.2.1.1 _ hs
  simp_rw [if_neg he]; exact hasSum_zero

-- Head reduction. Pay from Crude exactly; no generic algebra interface
-- remaining.
theorem headings (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) {z : ℂ}
    (hs : HasSum (fun i=> crude D Z s F V A m i k uPAGE) z) :
    HasSum (fun i=>if welcomes D A Z i m then
        (∑ v:Versions i, lamps D F A k V Z s i v (Print.backdrop D.betaHat A F uPAGE)) *
          (↑((∏ j,exam D F A k₀ k V (team i) uPAGE j)*Real.exp ((H₀).sumValue V uPAGE)):ℂ)
      else 0) z := by
  let v i:= crude D Z s F V A m i k uPAGE
  have hp : HasSum (v ∘ (X)) z := (build_inj D A).hasSum_iff (fun i he=> ?_) |>.mpr hs
  swap
  · unfold v crude; split
    next ht=>
      obtain ⟨ht,h0,h1⟩:=ht
      have hz : Words.permits (Fleet.required S D.labels _ question) i := fun i hi=>(h1 i hi).1
      apply False.elim (he (build_range D A i ?_ hz))
      unfold Shipment.station at ht; rw [←ht,Fleet.restored (parent:=question) hz]
    rfl
  let d (i : Head I): ℂ := ↑((∏ j,exam D F A k₀ k V (team i) uPAGE j)*Real.exp ((H₀).sumValue V uPAGE))
  let t (i : Hypothesis I) := if welcomes D A Z i.1 m then lamps D F A k V Z s i.1 i.2 (Print.backdrop D.betaHat A F uPAGE)*d i.1 else 0
  have hh : HasSum t z := hp.prod_fiberwise (by
    rintro ⟨i,q⟩
    exact purchase D h F A k₀ k V Z s m i q uPAGE hc (hp.summable.prod_factor (⟨i,q⟩:Hypothesis I)))
  refine hh.sigma ?_
  intro b
  convert! hasSum_fintype (fun x=> t (⟨b,x⟩:Hypothesis I)) using 1
  unfold t d; dsimp only; split <;> rename_i he
  · exact Finset.sum_mul ..
  simp [he]
end YM.PhysicalNext.Dictionary.Formal
