import YM.Next.FLUCTUATIONS.Prediction

/-!
# Locality of the cut defects with a free input

Agreeing through `3R+4+predReach` is enough. Keep an input free
(and identical during comparison!) so we don't need to touch any
indicators. Numerical reads, not a support/cost receipt for doing a
subsequent integration in a polymer decomposition. Distances use
actual wraps, cutoff uses actual path lengths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
open Work.E03
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section read
variable (p : Site n → Site c) (hp : ∀ x (i : Axis), separation (p x) (p (x+step i)) ≤ 1)
include hp

lemma travel_near (U W : Config G n) (x : Site n) (w : Walk) (R : ℕ) (he : w.length ≤ R)
    (hU : AgreeNear p (p x) R U W) : travel U x w = travel W x w := by
  have hs (x : Site n) (d : Step) : separation (p x) (p (x+d.vec)) ≤ 1 := sep_walk p hp x [d]
  have hv : AgreeNear p (p x) w.length U W := hU.shrink (by rwa [separation_self,zero_add])
  clear hU he
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    have he : d.read U x = d.read W x := by
      unfold Step.read Step.used; split
      next h => rw [hv (x-step d.dir,d.dir) ?_]; apply le_trans (b:=1) _ (by simp)
                simpa only [Step.vec,h,↓reduceIte,sub_eq_add_neg] using hs x d
      next h => rw [hv (x,d.dir) (by simp)]
    have ht : separation (p x) (p (x+d.vec)) + w.length ≤ (d::w).length := by
      have hh := hs x d; simp; omega
    rw [travel,travel,he, ih _ (hv.shrink ht)]

lemma plotted_near (U W : Config G n) (A : Clip) (P : PathData G) (R d : ℕ)
    (i : Twin n) (hd : 1 ≤ d) (h : AgreeNear p (p i.1.1) (R+4) U W) :
    plotted P A R d U i = plotted P A R d W i := by
  have hb (x : Cell n) (hv : AgreeNear p (p x.1) 4 U W) : faceValue U x = faceValue W x :=
    travel_near p hp _ _ x.1 (square x.2.val.1 x.2.val.2) 4 le_rfl hv
  unfold plotted
  split
  next hi =>
    apply tsum_congr
    intro j
    dsimp only [shortenTerm]; split
    next ht =>
      let s := (P.row i.1.2 j).2
      let b := Work.F03.slotFace s i.1.1
      have hw : s.walk.length ≤ R := le_trans (show s.walk.length ≤ s.length from by
        unfold Slot.length; omega) ((le_mul_of_one_le_right (Nat.zero_le _) hd).trans ht)
      have hi : b.1 = stop i.1.1 s.walk := by
        unfold b Work.F03.slotFace Slot.offset; rw [wrap_stop_cover, map_zero,add_comm]
        nth_rw 2 [show i.1.1=i.1.1+0 by rw [add_zero]]
        rw [Work.E03.stop_add_left]
      have hj : separation (p i.1.1) (p b.1) + 4 ≤ R+4 := by
        rw [hi]; exact Nat.add_le_add_right ((sep_walk p hp _ _).trans hw) _
      have he := travel_near p hp U W i.1.1 s.walk (R+4) (hw.trans (by omega)) h
      have hf : s.atSite U i.1.1 = s.atSite W i.1.1 := by
        rw [Work.F03.atSite_path,Work.F03.atSite_path,he,hb b (h.shrink hj)]
      unfold PathData.ellTerms; rw [hf]
    next ht => rfl
  next hi => rw [shoot,shoot,hb i.1 (h.shrink (by simp))]
end read

-- All three factors Φ,Φ',N with within-row reads and band, from V.
section rows
variable {X Y α β : Type*} (F : Config G c → X → Y → Pay G) (p : X → Site c) (q : Y → Site c)

private structure RowNear (R : ℕ) : Prop where
  band (V : Config G c) (i : X) (j : Y) : R < separation (p i) (q j) → F V i j = 0
  seen (V W : Config G c) (i : X) (j : Y) : AgreeNear id (p i) R V W → F V i j = F W i j

variable [Fintype X] [Fintype Y]

omit [Fintype Y] in
private lemma RowNear.unzip_eq {p : X → Site c} {q : Y → Site c} {R : ℕ} {F : Config G c → X → Y → Pay G}
    (hr : RowNear F p q R) (V W : Config G c) (j : Y)
    (h : AgreeNear id (q j) (2*R) V W) (a b : X → G.Color)
    (he : ∀ i, separation (q j) (p i) ≤ R → a i = b i) : unzip (F V) a j = unzip (F W) b j := by
  unfold unzip
  refine sum_congr rfl fun i _ => ?_
  by_cases ht : separation (q j) (p i) ≤ R
  · rw [he _ ht, hr.seen V W i j (h.shrink (by omega))]
  · have hu : R < separation (p i) (q j) := lt_of_not_ge (separation_comm _ _ ▸ ht)
    rw [hr.band V i j hu, hr.band W i j hu,map_zero,zero_apply,zero_apply]

private lemma RowNear.unzip_zip_eq {p : X → Site c} {q : Y → Site c} {R : ℕ} {F : Config G c → X → Y → Pay G}
    (hr : RowNear F p q R) (V W : Config G c) (j : Y)
    (h : AgreeNear id (q j) (2*R) V W) (w : Y → G.Color) :
    unzip (F V) (zip (F V) w) j = unzip (F W) (zip (F W) w) j := by
  apply hr.unzip_eq _ _ _ h
  intro i hi
  unfold zip
  exact sum_congr rfl fun k _ => by rw [hr.seen V W i k (h.shrink (by omega))]

omit [Fintype X] [Fintype Y] in
private lemma lane_near (R d : ℕ) (hd : 1≤d) (K : Row α β) (e : X → Co c α) (b : Y → Co c β) :
    RowNear (fun V i j => lane R d (G:=G) V K (e i) (b j)) (Prod.fst ∘ e) (Prod.fst ∘ b) R := by
  have hl k (h : k*d ≤ R) : k≤R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) hd) h
  constructor
  · intro V i j h
    have hf (u : Cover) : priced R d V K (e i) (b j) u = 0 := by
      unfold priced; split
      next hv =>
        have hx : stop (e i).1 (route 0 u 1) = (b j).1 := by
          rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (e i).1 0 u
        have he : separation (e i).1 (b j).1 ≤ R := by
          rw [← hx]; exact (sep_walk (fun x : Site c => x) sep_step ..).trans (hl _ hv.1)
        exact (h.not_ge he).elim
      next hv => rfl
    simp [lane,hf]
  · intro V W i j h
    apply tsum_congr
    intro u; unfold priced; split
    next ht => rw [rated,rated, travel_near id (fun y i => sep_step y i) _ _ _ _ R (hl _ ht.1) h]
    next ht => rfl
end rows

private lemma f_near (T : Tube G S) (R : ℕ) :
    RowNear (T.Φ R) (S.ratio.parent ∘ fun i : Twin f => i.1.1) (fun j : Twin c => j.1.1) R := by
  constructor
  · intro V i j h
    have hf (u : Cover) : casted S T.R R V (mesh i) (mesh j) u = 0 := by
      dsimp only [casted]; split
      next hv =>
        let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
        have hp := sep_walk S.ratio.parent (parent_step S) (mesh i).1 w
        rw [show stop _ w = _ from casted_endpoint S (mesh i).1 u, S.ratio.embed_parent, ← hv.2] at hp
        exact (h.not_ge (hp.trans hv.1)).elim
      next hv => rfl
    simp only [Tube.Φ,leap,hf,tsum_zero]
  · intro V W i j h
    apply tsum_congr
    intro u
    dsimp only [casted]; split
    next ht =>
      have he : AgreeNear S.ratio.parent (S.ratio.parent (mesh i).1) R (replica S.ratio V) (replica S.ratio W) := by
        intro e he; unfold replica; split
        next hx => rfl
        next hx => exact h _ he
      rw [rated, rated, travel_near _ (parent_step S) _ _ _ _ R ht.1 he]
    next ht => rfl

/-- Anchored comparisons without changing the input `w` of D. -/
lemma local_gaps (T : Tube G S) (hb : S.patch.Branches S.kernel G) (R D : ℕ)
    (i : Twin c) (k : S.Choices) (U U' : Config G f) (V V' : Config G c)
    (hu : AgreeNear S.ratio.parent i.1.1 D U U') (hv : AgreeNear id i.1.1 D V V')
    (hR : 3*R+4+predReach S.patch ≤ D) :
    lGap T R U (S.prediction U k) V i = lGap T R U' (S.prediction U' k) V' i ∧
      ∀ w, dGap T R V w i = dGap T R V' w i := by
  let p (j : Twin c) := j.1.1
  let q (j : Twin f) := S.ratio.parent j.1.1
  have h1 : RowNear (T.Φ R) q p R := f_near T R
  have h2 : RowNear (T.Φ' R) Prod.fst p R := lane_near R S.patch.L.val S.patch.L.property T.R.mn pole mesh
  have h3 : RowNear (T.N R) Prod.fst p R := lane_near R S.patch.L.val S.patch.L.property T.R.o id mesh
  have he : AgreeNear id (p i) (2*R) V V' := hv.shrink (by unfold p; rw [separation_self]; omega)
  constructor
  · unfold lGap
    have hl (j : Twin f) (hh : separation (p i) (q j) ≤ R) : T.Xf R U j = T.Xf R U' j :=
      plotted_near _ (parent_step S) U U' T.high T.up R 1 j le_rfl (hu.shrink (by unfold p q at hh; omega))
    have hg (j : Bond c) (hh : separation (p i) j.1 ≤ R) : Z S (S.prediction U k) V j = Z S (S.prediction U' k) V' j := by
      have ht : V j = V' j := he j (by change separation (p i) j.1 ≤ _; omega)
      rw [Z,Z,ht,prediction_near_eq hb _ _ _ j (hu.shrink (by unfold p at hh; omega))]
    have hk : T.Xn R V i = T.Xn R V' i := plotted_near id (fun x i => sep_step x i) V V' T.low T.down R S.patch.L.val i
      S.patch.L.property (hv.shrink (by change separation i.1.1 i.1.1 + _ ≤ _; rw [separation_self]; omega))
    rw [h1.unzip_eq V V' i he _ _ hl,h2.unzip_eq V V' i he _ _ hg,hk]
  intro w
  unfold dGap; rw [h1.unzip_zip_eq V V' i he w,h2.unzip_zip_eq V V' i he w,h3.unzip_zip_eq V V' i he w]
end YM.Next.Fluctuations
