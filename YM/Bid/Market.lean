import YM.Bid.Fetch
/-! Loom pin across ALL indices -/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction Retain
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} {C : Family G} {F : Order} {S : Table C.book}

lemma Looms (a : Seats) (b : B01) (c : B02) (d : B03) (e : B04) (f : B05) (g : B06) (h : B07)
    (i : B08) (j : B09) (k : B10) (l : B11) (m : B12) (n : B13) (o : B14)
    (p : B15) (q : B16) (r : B17) (x : B18) (Y : Grill C F) (s : Seed C F S) (X : Algebra S) : Phase.Loom s X Y := by
  constructor
  · intro H V
    obtain ⟨W,hW⟩ := b V s.kernel (a s)
    exact ⟨W,c S S X.derivatives V W s.kernel s.kernel (fun _ => le_rfl) s.kernel.laws.toSymmetric s.kernel.laws.toSymmetric H.derivatives hW⟩
  intro H V A ht
  have hv : Steady V := fun u z => OS.Ground.inert _ s.kernel _ H.motion z u
  have hd := d s.kernel X.derivatives V A hv ht
  have he := f e s Y X H V A hv hd
  refine ⟨he,fun d x' Q K => episode p q r x s A hd hv he Q K,m V A s.kernel hd hv,?_⟩
  intro R hR
  constructor
  · obtain ⟨y,hY⟩ := h g V A R X s.kernel H hd hv he hR
    have hh := i V A R X s.kernel H hv hR y hY
    have hm := j V A R X s.kernel H hv hd ht hR y hY
    have hl := l V A R X hv ht.cap hR y hY
    exact ⟨y,hY.threads,fun t => ⟨hY.basics t,hY.HOnly t,hY.translation t,(hh t).1,(hh t).2,hY.smooth t,
      k S (y t) X.derivatives (hY.rel t) (hY.smooth t) (hY.basics t) (hm t).1 (hm t).2.1 (hl t)⟩,
      hY.rel,hY.turns,fun t => (hm t).1,fun t => (hm t).2.1,fun t => (hm t).2.2⟩
  · intro q w i B
    obtain ⟨W,hW⟩ := n V A R X s.kernel H hv ht hd hR q w i B
    have hh := w.loci i
    exact ⟨W,c _ (q i) X.derivatives B W s.kernel hh (w.sees i) s.kernel.laws.toSymmetric hh.laws.toSymmetric (w.deriv i) hW⟩
  intro p w B
  exact o V A R X p s.kernel hv hd hR w B
end YM.Bid
