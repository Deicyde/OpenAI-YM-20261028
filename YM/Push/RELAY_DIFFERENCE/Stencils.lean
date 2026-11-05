import YM.Push.RELAY_DIFFERENCE.Placement

/-!
# Preparing comparison cylinders

Cover stencil in native units, Interior on its translate. Enlarging before
comparison to common stencil incl shifted read of Wdff. This isn't a
statement of any RG budgets on a good set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson Lattice Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : Side} {G : Gauge}

/-- Translate the full stencil in cutoff site units. -/
def stamp (X : Finset Cover) (x : Site n) : Set (Site n) := ↑(X.image fun z => wrap n z+x)

structure Local (X : Finset Cover) (F : Site n → Config G n → ℂ) : Prop where
  translates : literal F
  fits x : Interior (stamp X x) (F x)

variable {X Y : Finset Cover} {F P : Site n → Config G n → ℂ}

lemma Local.larger (h : Local X F) (H : X ⊆ Y) : Local Y F :=
  ⟨h.translates, fun x => (h.fits x).enlarges (show (_:Set (Site n)) ⊆ _ from Finset.coe_subset.mpr (Finset.image_subset_image H))⟩

lemma Local.smul (c : ℂ) (h : Local X F) : Local X fun x => c • F x := by
  refine ⟨fun o b => ?_,fun i => (h.fits i).scale c⟩
  rw [h.translates]; rfl

lemma Local.add (h : Local X F) (H : Local Y P) : Local (X∪Y) fun x => F x + P x := by
  refine ⟨fun o b => ?_,fun i => ((h.larger Finset.subset_union_left).fits i).plus ((H.larger Finset.subset_union_right).fits i)⟩
  rw [h.translates,H.translates]; rfl

lemma Local.neg (h : Local X F) : Local X fun x => -F x := by simpa using Local.smul (-1) h
lemma Local.sub (h : Local X F) (H : Local Y P) : Local (X∪Y) fun x => F x - P x := by
  simpa only [sub_eq_add_neg] using h.add H.neg

lemma Local.step (b : Axis) (h : Local X F) : Local (X.image (fun x => x+Lattice.step b)) fun x => F (x+Lattice.step b) := by
  refine ⟨fun o i => ?_, fun i => ?_⟩
  · rw [show o+i+Lattice.step b=o+Lattice.step b+i by abel]
    exact h.translates ..
  refine (h.fits _).enlarges ?_
  rintro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image_of_mem _ hy, by rw [map_add,wrap_step]; abel ⟩

variable {C : Family G} {N p d : ℕ} {f : Extraction.Order} {u w : Trial C}

/-- Fixed stencil eventual scope. Enough (not necessary) for center placements. -/
def Stencilled (f : Extraction.Order) (F : Trial C) := ∃ X : Finset Cover, ∀ᶠ i in f.fuse, Local X (F i.1 i.2)

lemma Stencilled.sub (hu : Stencilled f u) (hw : Stencilled f w) : Stencilled f (u-w) := by
  obtain ⟨X,hX⟩ := hu; obtain ⟨Y,hY⟩ := hw
  exact ⟨X∪Y, (hX.and hY).mono fun i hi => hi.1.sub hi.2⟩

lemma local_primary (h : C.Makes) (v : C.label d) : Local (C.localSection d).stencil (C.O N p v) := by
  refine ⟨fun o b => ?_,fun i => ?_⟩
  · funext U; exact (C.translation ..).symm
  have hc := C.continuousO N p _ v i
  exact ⟨C.invariant h _ _ _ _ _,hc.measurable,C.localO _ _ _ v _,hc.bounded_above_of_compact_support
    (HasCompactSupport.of_compactSpace _)⟩

lemma Stencilled.upper (h : C.Makes) (v : Bid.Rowe C d) : Stencilled f (Bid.upper C v) :=
  ⟨(C.localSection d).stencil, Eventually.of_forall fun _ => local_primary h _⟩

lemma Stencilled.visits (h : C.Makes) (v : C.label d) : Stencilled f (Bid.visits C d v) := upper h _

lemma Stencilled.heighten (h : C.Makes) (v : C.label d) (b : Axis) : Stencilled f (Bid.heighten C d v b) := by
  let X := (C.localSection d).stencil
  refine ⟨X.image (fun x => x+step b) ∪ X, Eventually.of_forall ?_⟩
  rintro ⟨N,p⟩
  have he := local_primary (N := N) (p := p) h v
  exact Local.smul _ ((Local.step b he).sub he)

lemma Stencilled.sober (h : Stencilled f u) : Bid.sober C u f := by
  obtain ⟨X,hX⟩ := h
  have hv : ∀ᶠ j in f.fuse, ∀ x, Measurable (u j.1 j.2 x) ∧ ∃ A : ℝ, ∀ v, ‖u j.1 j.2 x v‖ ≤ A :=
    hX.mono (fun i hi x => ⟨(hi.fits x).borel,(hi.fits x).cost⟩)
  exact (Order.fused f _).mp hv

lemma Stencilled.literal (h : Stencilled f u) : ∀ᶠ i in f.fuse, literal (u i.1 i.2) := by
  obtain ⟨X,hX⟩ := h
  exact hX.mono fun _ hi => hi.translates

/-- Period-independent fit of fixed microscopic stencil into any fixed
centered physical side. May use on fuse. -/
theorem stencil_fit (S : Schedule) (m : ℕ) (X : Finset Cover) : ∀ᶠ N in atTop, ∃ hn : m ≤ N,
    ∀ p : ℕ, ∀ o : Site (S.side N p), stamp X o ⊆ (center S p hn o).chamber 0 := by
  have he (z) (_ : z∈ X) (j : Axis) : ∀ᶠ N in atTop,
      S.a N*(2*((z j).natAbs+1):ℝ)<S.a m := (show Tendsto (fun N => S.a N*(2*((z j).natAbs+1):ℝ)) atTop (𝓝 0) from by
        simpa only [zero_mul] using S.shrinks.mul_const _).eventually (gt_mem_nhds (S.a_pos _))
  have hv := eventually_all_finset _ |>.mpr (fun z (hz:z∈X) => eventually_all.mpr (he z hz))
  filter_upwards [hv,eventually_ge_atTop m] with N HN hn
  refine ⟨hn,fun p x z hz => ?_⟩
  obtain ⟨y,hY,rfl⟩ := Finset.mem_image.mp hz
  refine Tiling.fits_stencil _ (Stock.centered_margin p hn x) fun j => ?_
  let t := S.toDepth hn p
  have hh := (HN y hY j).trans_eq (S.embeds_scale t).symm
  change S.a N*(2*((y j).natAbs+1):ℝ)< _ at hh
  have he := lt_of_mul_lt_mul_left hh (S.a_pos _).le
  have hx : 2*((y j).natAbs+1)<t.count.val := by exact_mod_cast he
  change (y j).natAbs < t.count.val/2; omega

lemma Stencilled.fits (m : ℕ) (h : Stencilled f u) : ∀ᶠ i in f.fuse, ∃ hm : m ≤ i.1,
    ∀ x, Interior ((center C.S i.2 hm x).chamber 0) (u i.1 i.2 x) := by
  obtain ⟨X,hX⟩ := h
  filter_upwards [hX, (cutoff_grows f).eventually (stencil_fit C.S m X)] with i hi ⟨hw,hf⟩ using
    ⟨hw,fun x => (hi.fits x).enlarges (hf _ x)⟩
end YM.Push.RelayDifference
