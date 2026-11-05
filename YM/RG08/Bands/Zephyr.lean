import YM.RG08.Bands.Gowns
/-!
# Contact forcing on all sectors even with arbitrarily small designated mass.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J :Type}{α:J→Type} [∀ i,Fintype (α i)]{p u: List I}{b r k n e ε E:ℕ}{i:I}
def accrues (q:I→ J→ℝ)(u:List I):J→ℝ:= u.foldr (fun i v=> q i*v) 1
variable {x y δ v p' w  z η ρ σ : J→ℝ}
def BillsP (k n E:ℕ)(y δ p:J→ℝ)(F V:∀ i, HeatS (α i))(η:J→ℝ): Prop:=∀ i≤n,∀ e ≤ E,∀ r,Drum k y δ p (fun j=> F j i e r) (fun j=> V j i e r) η
variable {F V P A : ∀ i, HeatS (α i)}{K W:∀ i, Row (α i) (α i)}
section layers
lemma bearing (h:BillsP k n E y δ v F V η)(he:BillsP k n E y δ w P A η)(hp:Audience y)(hx:0≤η): BillsP k n E y δ (v*w) (fun i=>borne (F i) (P i)) (fun i=>borne (V i) (A i)) η:= by
   intro i hi e he' r; unfold borne; simp_rw [Finset.sum_apply]; refine Drum.group (wheel i) hp hx (F:=fun b j=> gust (F j b.1) (P j b.2) e r) (H:=fun b j=> gust (V j b.1) (A j b.2) e r) fun b hb=> ?_
   unfold gust; simp_rw [Finset.sum_apply]; refine Drum.group (wheel e) hp hx (F:=fun a j=> spoolB (F j b.1 a.1) (P j b.2 a.2) r) (H:=fun a j=> spoolB (V j b.1 a.1) (A j b.2 a.2) r) fun a ha=>?_
   have ha:=mem_antidiagonal.mp ha; have hb:=mem_antidiagonal.mp hb
   unfold spoolB; refine Drum.group (wheel r) hp hx (F:=fun l j=> grant r (braidV ((F j) b.1 a.1 l.1) ((P j) b.2 a.2 l.2))) (H:=fun l j=>grant r (braidV (V j b.1 a.1 l.1) (A j b.2 a.2 l.2))) fun l hl=>?_ ; exact (knotted (h b.1 (by omega) a.1 (by omega) l.1) (he b.2 (by omega) a.2 (by omega) l.2) hx hp).grantor r
lemma bills_none : BillsP k n E y δ v (0:∀ i,HeatS (α i)) 0 η:= fun i hi e he r=> Drum.zero
lemma pair_bill (ht:BillsP k n E y δ v F P η)(he:BillsP k n E y δ v V A η)(hp:Audience y)(hx:0≤η): BillsP k n E y δ v (F+V) (P+A) η:= fun i hi e he' r=>(ht i hi e he' r).more (he i hi e he' r) hx hp
lemma sleeve (n k E)(δ y η:J→ℝ) (hy:0≤δ): BillsP k n E y δ 1 (fun i=> upstart (α i)) (fun i=> upstart (α i)) η := by
   intro i hi e he r; by_cases hj:i=0
   · by_cases h:e+r=0
     · simp only [upstart,hj,↓reduceIte,spine_one,h]
       rw [show r=0 by omega]; apply Drum.home (Card.mk ?_)
       refine ⟨1,Weighed.one,fun i=>?_⟩; unfold cis Quire.Ink; simp only [tailP,girth, sum_empty, Finset.univ_eq_empty, Nat.cast_zero,mul_zero,add_zero,one_pow,norm_one,Pi.one_apply,mul_one]
       exact ⟨fun _=> zero_le_one,(hasSum_fintype _).summable,by simp⟩
     simp only [upstart,hj,↓reduceIte,spine_one,h]; exact Drum.zero
   simp only [upstart,hj,↓reduceIte,spine_one]; exact Drum.zero
lemma layF {F V: ∀ i, Screed ℝ (α i) } {P A : ∀ i,Screed ℝ (α i) } (h:∀ i≤e,∀ r, Drum k y δ v (fun j=>F j i r) (fun j=> V j i r) η)(hh:∀ i≤e,∀ r, Drum k y δ w (fun j=>P j i r) (fun j=>A j i r) η)(hp:Audience y)(hx:0 ≤ η): Drum k y δ (v*w) (fun j=>gust (F j) (P j) e r) (fun j=>gust (V j) (A j) e r) η := by
   have ht:= bearing (P:=fun i _=>P i) (F:=fun i _=>F i) (A:=fun i _=>A i) (V:=fun i _=> V i) (n:=0) (fun i hi=> h) (fun i hi=>hh) hp hx 0 le_rfl e le_rfl r; simp_rw [borne_z] at ht; exact ht
lemma ledger (h:Audience y)(hp:0≤η)(ht:0≤δ){F V: I→ ∀ i:J, HeatS (α i)}{q:I→J→ℝ}(hF:∀ i∈p, BillsP k n E y δ (q i) (F i) (V i) η): BillsP k n E y δ (accrues q p) (fun i=>castM (fun t=>F t i) p) (fun i=> castM (fun t=>V t i) p) η := by
   induction p with
   | nil=> exact sleeve n k E δ y η ht
   | cons b u ih=> exact bearing (hF b List.mem_cons_self) (ih fun j hj=> hF j (List.mem_cons_of_mem _ hj)) h hp
lemma ledger_s (h:Audience y)(hp:0 ≤ η)(ht:0≤δ){F V:I→ ∀ i:J, Screed ℝ (α i)}{q:I→J→ℝ}(hV:∀ i∈p,∀ j ≤ E,∀ r, Drum k y δ (q i) (fun a=> F i a j r) (fun a=>V i a j r) η) : ∀ j≤E,∀ r, Drum k y δ (accrues q p) (fun i=> castF (fun t=> F t i) p j r) (fun i=>castF (fun t=> V t i) p j r) η:= by
   induction p with
   | nil => intro j hj r; exact sleeve (α:=α) 0 k E δ y η ht 0 le_rfl _ hj r
   | cons b u ih=>
     have hx:=hV b List.mem_cons_self; let hZ:=ih (fun i hi=> hV i (List.mem_cons_of_mem _ hi)); intro j hj r; exact layF (F:=F b) (V:=V b) (P:=fun i=>castF (fun u=> F u i) u) (A:=fun i=> castF (fun u=> V u i) u) (r:=r) (fun _ hi r=>hx _ (hi.trans hj) r) (fun i hi r=> hZ _ (hi.trans hj) r) h hp
end layers
section stars
variable {a:I→J→Cover}{q:I→J→ℝ}{U Q:I→∀ i,HeatS (α i)}
def shiftM (a: J→Cover) (F:∀ i,HeatS (α i))(i:J): HeatS (α i) := fun j=> season (a i) (F i j)
local notation "►" => shiftM
lemma hymns (hF:BillsP (k+b) n E y δ p' F V 1)(hp:Audience y)(h:0≤η)(hx:η≤1){z:J→Cover}(he:Weighed y (fun i=>η i*size (z i))): BillsP k n E y δ p' (► z F) (► z V) η:= fun i hi e he' r=> roam_enough (hF _ hi _ he' r) h hx he hp -- p'
-- x controls separation with steplet µ->0; even if both assembled roots presently coincide. Charge extra powers at joint intake only.
structure Leaves (b:ℕ)(p:List I) (a:I→J→Cover)(y η σ v δ x:J→ℝ)(K W:∀ i,Row (α i) (α i)):Prop where
   age : Audience y
   pos : 0≤η
   small : η ≤1
   nonneg : 0≤δ
   weight : ∀ i∈p, Weighed y (fun t=> η t*size (a i t))
   veto : Weighed y x
   shortL : ∀ (j:I),j∈p → ∀ (k:I), k∈p→ j≠k→∀ i, 1≤ x i*σ i*(1+size (a j i-a k i))
   reserve : 0≤σ
   wage : RowBoth y δ K W v
   scope : ∀ i,0<v i
   spaceT : Weighed y (fun i=>Run.utter b (v i))
lemma Leaves.road (h: Leaves b p a y η σ v δ x K W) (hp:u ⊆ p): Leaves b u a y η σ v δ x K W:= ⟨h.age,h.pos,h.small,h.nonneg,fun i hi=>h.weight i (hp hi),h.veto,fun i hi j hj=>h.shortL i (hp hi) j (hp hj),h.reserve,h.wage,h.scope,h.spaceT⟩
local notation "╲" => ► -- Std
lemma chapterL (he:Leaves b (i::p) a y η σ v δ x K W)(hF: BillsP (k+b) n E y δ (q i) (U i) (Q i) 1)(hh:∀ j∈p,BillsP (k+b) n E y δ (q j) (U j) (Q j) 1)(h:i ∉ p): BillsP k n E y δ (q i * accrues q p*σ^b)
    (fun j=> junction none (K j) (fun i=> ► (a i) (U i) j) (► (a i) (U i) j) p) (fun j=>junction none (W j) (fun i=> ► (a i) (Q i) j) (► (a i) (Q i) j) p) η:= by
   induction p with
   | nil=> simp_rw [junction]; exact bills_none
   | cons t u ih=>
     have hU i hi:= hh i (List.mem_cons_of_mem (l:=u) t hi)
     let a₀:= shiftM (a i) (U i); let b₀:=shiftM (a i) (Q i)
     have hV (j) (hj:j∈t::u) := hymns (k:=k) (z:=a j) (hh j hj) he.age he.pos he.small (he.weight j (List.mem_cons_of_mem _ hj))
     have hX:BillsP k n E y δ (q i*q t*σ^b) (fun j=> thunder none (K j) (a₀ j) (► (a t) (U t) j)) (fun j=> thunder none (W j) (b₀ j) (► (a t) (Q t) j)) η:= by
        intro n hn e he' r
        let F q m j:= grail none (K (j:J)) (a₀ j (q:ℕ×ℕ).1 (m:ℕ×ℕ).1) (shiftM (a t) (U t) j q.2 m.2) r; let H q m j:= grail none (W (j:J)) (b₀ j (q:ℕ×ℕ).1 (m:ℕ×ℕ).1) (shiftM (a t) (Q t) j q.2 m.2) r
        unfold thunder; simp only [Finset.sum_apply]; refine Drum.group (wheel n) he.age he.pos (F:=fun p j=> ∑ v ∈ wheel e,F p v j) (H:=fun p j=>∑ v∈wheel e,H p v j) fun p hp=>?_; have hp:=mem_antidiagonal.mp hp
        refine Drum.group (wheel e) he.age he.pos (F:= F p) (H:= H p) fun v hv=>?_; have hv:=mem_antidiagonal.mp hv
        unfold F H grail; refine Drum.group (wheel r) he.age he.pos (F:=fun s j=>grant r (countP none (K j) (a₀ j p.1 v.1 (s.1+1)) (shiftM (a t) (U t) j p.2 v.2 (s.2+1)))) (H:=fun s j=>grant r (countP none (W j) (b₀ j p.1 v.1 (s.1+1)) (shiftM (a t) (Q t) j p.2 v.2 (s.2+1)))) fun s hs=>?_
        exact (bonfire he.age he.pos he.small he.nonneg he.reserve (he.weight i List.mem_cons_self) (he.weight t (List.mem_cons_of_mem _ List.mem_cons_self)) (hF p.1 (by omega) v.1 (by omega) (s.1+1)) (hh t List.mem_cons_self p.2 (by omega) v.2 (by omega) (s.2+1)) he.wage he.scope he.spaceT he.veto (he.shortL i (by simp) t (by simp) (fun j=> h (by simp [j])))).grantor _
     simp_rw [junction]; refine pair_bill (F:=fun i=>_) (P:=fun i=>_) (A:=fun i=>_) (V:=fun i=>_) ?_ ?_ he.age he.pos
     · have hM:= ledger (F:=fun i=> ► (a i) (U i)) (V:=fun i=> ► (a i) (Q i)) he.age he.pos he.nonneg (p:=u) (fun i hi=>hV i (by simp [hi])); convert bearing hX hM he.age he.pos using 1; change q _ * (q t * accrues q u)*_= _; ring
     have hx':= ih (he.road (fun i hi=> by simp only [List.mem_cons] at hi ⊢; tauto)) hU (fun j=> h (by simp [j])); convert bearing (hV t List.mem_cons_self) hx' he.age he.pos using 1; change _*(q t * accrues q u)*_= _; ring
lemma chapter (he:Leaves b p a y η σ v δ x K W)(hF:∀ i∈p,BillsP (k+b) n E y δ (q i) (U i) (Q i) 1)(hp:p.Nodup) : BillsP k n E y δ (accrues q p*σ^b) (fun i=> pullG none (K i) (fun j=> ► (a j) (U j) i) p) (fun i=> pullG none (W i) (fun j=> ► (a j) (Q j) i) p) η:= by
   induction p with
   | nil=> simp_rw [pullG]; exact bills_none
   | cons i p ih=>
     have hx:= hF i List.mem_cons_self; have hv i hi:= hF i (List.mem_cons_of_mem (l:=p) _ hi); obtain ⟨hn,hP⟩:= List.nodup_cons.mp hp
     have hP:= ih (he.road (by simp)) hv hP
     simp_rw [pullG]; have ht:= chapterL (Q:=Q) (U:=U) he hx hv hn
     have H:=hymns (k:=k) hx he.age he.pos he.small (he.weight i List.mem_cons_self)
     refine pair_bill (F:=fun i=>_) (P:=fun i=>_) (A:=fun i=>_) (V:=fun i=>_) ht ?_ he.age he.pos
     rw [show accrues q (i::p)=q i*accrues q p from rfl,mul_assoc]; exact bearing H hP he.age he.pos
end stars
end YM.RG08.Bands
