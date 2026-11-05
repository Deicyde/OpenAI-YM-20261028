import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sector
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.SECTOR_MEASURE.Gauges
import YM.Work.F05.Actions

/-!
# Reading the prices/extensions locally from V & U

Export range/locality and gauge rules also for **vectors** in the affine and
actual rows (compare `Next/FLUCTUATIONS/Covariance` and
`Locality` for the two defects; similar method but need also potentials).
No appeal to channel symmetries of single covariance entries. Numerical stencil
with all needed data to select actual cut operations. Q uses k; a comparison
requiring k varying local has to check its portions too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows.DataKernel
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior  Channel Next.Fluctuations Work.E03
open Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}

section conjugates
variable {o : Site n} {x : ℝ} {s : Clip} (U : Config G n) (z : Site n → G.El)

private lemma slot_gauge (o : Site n) (p : Slot) : p.atSite (gauge z U) o = G.adjoint (z o) (p.atSite U o) := by
  apply Work.F05.slot_gauge

lemma short_gauge {p : Clip} {A : PathData G} {σ C Λ : ℝ} (h : A.Bounds p σ C Λ) (R d : ℕ) (i : Cell n) :
    shorten A R d (gauge z U) i = G.adjoint (z i.1) (shorten A R d U i) := by
  let L := (G.adjoint (z i.1)).toContinuousLinearMap
  unfold shorten; change _ = L (∑' _, _)
  rw [L.map_tsum (shorten_summable A U h ..)]
  apply tsum_congr; intro j
  dsimp only [shortenTerm]; split
  next hx => rw [PathData.ellTerms,PathData.ellTerms,slot_gauge,map_smul]; rfl
  next hx => rw [map_zero]

lemma kept (s : Clip) (x : ℝ) (i : Site n) : PathData.kept s x i (gauge z U) ↔ PathData.kept s x i U := by
  simp [PathData.kept]

lemma plots {A : PathData G} {s : Clip} {σ C Λ : ℝ} (h : A.Bounds s σ C Λ) (R d : ℕ) (i : Twin n) :
    plotted A s R d (gauge z U) i = G.adjoint (z i.1.1) (plotted A s R d U i) := by
  unfold plotted; split
  · exact short_gauge U z h ..
  · rw [shoot, shoot, face_gauge,G.curvature_conjugate,map_smul]

lemma thins {A : PathData G} {s : Clip} {σ C Λ : ℝ} (h : A.Bounds s σ C Λ) (x : ℝ) (R d : ℕ) (i : Twin n) :
    thinned A s x d R (gauge z U) i=G.adjoint (z i.1.1) (thinned A s x d R U i) := by
  unfold thinned; rw [kept U z s x]
  split
  · split
    next hx => exact short_gauge U z h ..
    next hx => rw [map_zero]
  rw [SectorMeasure.toll_gauge z U,map_smul,shoot, shoot,face_gauge,G.curvature_conjugate,map_smul]
end conjugates

section entries
variable {α β γ Z Y : Type*}

private lemma rotated_pay (V : Config G c) (z : Site c → G.El) (x : Site c) (w : Walk) (a : ℝ) (i : G.Color) :
    rated (gauge z V) x w a (G.adjoint (z (stop x w)) i)=G.adjoint (z x) (rated V x w a i) := by
  rw [rated,rated,travel_gauge]
  change a • (G.adjoint (z x*travel V x w*(z (stop x w))⁻¹) (G.adjoint _ i))=G.adjoint (z x) (a • G.adjoint (travel V x w) i)
  rw [← G.adjoint_mul,inv_mul_cancel_right,G.adjoint_mul,map_smul]

/-- Work with sums over true label routes. -/
private lemma oriented_entries {ι : Type*} (D F : ι → Pay G) (h : Summable D) (l : Summable F) (a b : G.El)
    (hy : ∀ i k, D i (G.adjoint a k)=G.adjoint b (F i k)) (k : G.Color) :
    (∑' i, D i) (G.adjoint a k)=G.adjoint b ((∑' i,F i) k) := by
  let A := ContinuousLinearMap.apply ℝ G.Color (G.adjoint a k)
  let B := (G.adjoint b).toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ G.Color k)
  change A (∑' i, D i) = B (∑' i,F i); rw [A.map_tsum h,B.map_tsum l]
  exact tsum_congr fun i => hy i k

/-- Turn and spatial horizon facts bundled. -/
structure Rule (R : ℕ) (M : Config G c → Z → Y → Pay G) (a : Z → Site c) (b : Y → Site c) : Prop where
  reach V i j : M V i j≠0 → separation (a i) (b j) ≤ R
  stencil i (V W : Config G c) : AgreeNear id (a i) R V W → ∀ j, M V i j=M W i j
  move (z : Site c → G.El) (V : Config G c) i j k :
    M (gauge z V) i j (G.adjoint (z (b j)) k)=G.adjoint (z (a i)) (M V i j k)

lemma sameLevel (R d : ℕ) (hd : 0<d) (K : Row α β) (he : K.safe) (a : Z → Co c α) (b : Y → Co c β) :
    Rule (G:=G) R (fun V i j => lane R d V K (a i) (b j)) (Prod.fst ∘ a) (Prod.fst ∘ b) := by
  constructor
  · intro V i j h
    by_contra hm
    refine h ?_
    have hz u : priced R d V K (a i) (b j) u=0 := by
      unfold priced; split
      next hw =>
        have hs : stop (a i).1 (route 0 u 1)=(b j).1 := by
          rw [hw.2]; simpa only [map_zero,add_zero] using stop_route (a i).1 0 u
        exact (hm (show separation (a i).1 (b j).1 ≤ R from hs ▸ ((sep_walk id (sep_step (c:=c)) (a i).1 (route 0 u 1)).trans
          ((le_mul_of_one_le_right (Nat.zero_le _) hd).trans hw.1)))).elim
      next hw => rfl
    simp only [lane, hz,tsum_zero]
  · intro i V W h j; apply tsum_congr; intro u
    unfold priced; split
    next hw => rw [rated,rated,travel_near id (sep_step (c:=c)) V W _ _ R
                    ((le_mul_of_one_le_right (Nat.zero_le _) hd).trans hw.1) h]
    next hw => rfl
  intro z V i j k
  have hx (V : Config G c) : Summable (priced R d V K (a i) (b j)) := by
    apply Summable.of_norm_bounded (he (a i).2 (b j).2); intro u; unfold priced; split
    next hv => exact norm_rated_le ..
    next hv => simp
  apply oriented_entries _ _ (hx _) (hx _) _ _ _ k
  intro u x; unfold priced; split
  next hv =>
    have hs : stop (a i).1 (route 0 u 1)=(b j).1 := by
      rw [hv.2]; simpa only [map_zero,add_zero] using stop_route (a i).1 0 u
    dsimp only [Function.comp_apply]; rw [← hs]
    exact rotated_pay ..
  next hv => simp

lemma crosses (R : ℕ) (T : Tube G S) (P : Teller G) (hP : P.Funds S T) :
    Rule R (T.Φ R) (S.ratio.parent ∘ fun i : Twin f => i.1.1) (fun j : Twin c => j.1.1) := by
  let w (i : Twin f) u := route (lift (S.ratio.residue i.1.1)) (S.patch.L.val • u) 1
  have hz u (i : Twin f) : S.ratio.parent (stop i.1.1 (w i u))=S.ratio.parent i.1.1+wrap c u := by
    rw [show stop _ _=_ from casted_endpoint S i.1.1 u,S.ratio.embed_parent]
  constructor
  · intro V i j h; by_contra hv
    apply h; unfold Tube.Φ leap
    have hh u : casted S T.R R V (mesh i) (mesh j) u=0 := by
      dsimp only [casted]; split
      next he =>
        refine (hv ?_).elim
        change separation (S.ratio.parent i.1.1) j.1.1 ≤ R
        rw [show j.1.1 = _ from he.2]; change separation (S.ratio.parent i.1.1) (S.ratio.parent i.1.1+wrap c u)≤ R
        rw [← hz]; exact (sep_walk S.ratio.parent (parent_step S) ..).trans he.1
      next he => rfl
    simp only [hh,tsum_zero]
  · intro i V W h j; apply tsum_congr; intro u; dsimp only [casted]; split
    next hx =>
      have hh : travel (replica S.ratio V) i.1.1 (w i u)=travel (replica S.ratio W) i.1.1 (w i u) := by
        apply travel_near S.ratio.parent (parent_step S) _ _ _ _ R hx.1
        intro a ha; unfold replica; split
        next he => rfl
        next he => exact h _ ha
      exact congr_arg (fun g => T.R.mf (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2 u • (G.adjoint g).toContinuousLinearMap) hh
    next hx => rfl
  intro z V i j k
  have hs (V : Config G c) : Summable (casted S T.R R V (mesh i) (mesh j)) := by
    have he := Row.rights _ _ hP.crosses.2.2.1 P.width.le
    apply Summable.of_norm_bounded (he (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2)
    intro u; dsimp only [casted]; split
    next h => exact norm_rated_le ..
    next h => simp
  refine oriented_entries _ _ (hs _) (hs _) _ _ ?_ k
  intro u x; dsimp only [casted]; split
  next hv =>
    have hh : z (j.1.1)=constantGauge z S.ratio (stop i.1.1 (w i u)) := congr_arg z (hv.2.trans (hz u i).symm)
    dsimp only [Function.comp_apply]; rw [hh,← copied S.ratio S.patch.odd_side]
    exact rotated_pay ..
  next hv => simp
end entries

section vision
variable (h : P.Funds S T)
include h

lemma mvg (R : ℕ) (t : ℝ) (z : Site c → G.El) (V : Config G c) (i : Twin f) :
    T.Mv R t (gauge z V) i=G.adjoint (z (S.ratio.parent i.1.1)) (T.Mv R t V i) := by
  obtain ⟨_,_,_,hp⟩ := h.feeds; rw [← h.low] at hp
  unfold Tube.Mv Tube.vision Pressure.zip; rw [map_sum]; apply Finset.sum_congr rfl; intro j _
  simp_rw [thins _ _ hp]; exact (crosses R T P h).move _ _ i j _

lemma mwg (R : ℕ) (t : ℝ) (z : Site c → G.El) (V : Config G c) (i : Bond c) :
    T.Mw R t (gauge z V) i=G.adjoint (z i.1) (T.Mw R t V i) := by
  obtain ⟨_,_,_,hp⟩ := h.feeds; rw [← h.low] at hp
  unfold Tube.Mw Tube.vision Pressure.zip; rw [map_sum]; apply Finset.sum_congr rfl; intro j _
  rw [thins _ _ hp]; exact (sameLevel R S.patch.L.val S.patch.L.property T.R.mn (Row.rights _ _ h.crosses.1 P.width.le)
    pole mesh).move _ _ i j _

lemma ng (R : ℕ) (t : ℝ) (z : Site c → G.El) (V : Config G c) (i : Co c Gain) :
    zip (T.N R (gauge z V)) (T.vision R t (gauge z V)) i=G.adjoint (z i.1) (zip (T.N R V) (T.vision R t V) i) := by
  obtain ⟨_,_,_,hp⟩ := h.feeds; rw [← h.low] at hp
  unfold Tube.vision Pressure.zip; rw [map_sum]; apply Finset.sum_congr rfl; intro j _
  rw [thins _ _ hp]; exact (sameLevel R S.patch.L.val S.patch.L.property T.R.o (Row.rights _ _ h.crosses.2.1 P.width.le)
    id mesh).move _ _ i j _
end vision
end YM.ConnectedActivityE6.SliceRows.DataKernel
