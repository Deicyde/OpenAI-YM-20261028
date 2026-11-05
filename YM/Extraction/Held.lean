import YM.Cells.Proximity
import YM.Extraction.Around
import YM.Extraction.Equicontinuity


/-!
# Local bounds on compact sets INCLUDING projection ties

Consume explicit centered estimates, both regulator tails. Then finish
producing the extraction surface. k-scale far offsets reached on same
smaller-grid centers. Budget `Fit` needed per stencil and PROVED.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter Lattice Cells MeasureTheory Wilson
open scoped Topology Matrix.Norms.Frobenius ComplexOrder BigOperators
variable {G : Gauge} {C : Family G} {f : Order} {N p k m n : ℕ}
namespace Around

lemma figure (H : C.Makes) (T : Tiling (C.side N p)) (v : C.book.Token) (K : ℕ)
    (x : Site (C.side N p)) (ht : x∈T.margin 0 K) (h : ∀ z∈(C.localSection v.1).stencil, ∀ a, (z a).natAbs < K) :
    Interior (T.chamber 0) (C.seen v x) := by
  have he : Continuous (C.seen v x) := C.continuousO _ _ v.1 v.2 _
  refine ⟨C.invariant H _ _ _ _ _,he.measurable, fun u y H => ?_,he.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  refine C.localO N _ _ _ _ _ _ (agrees_mono H ?_)
  intro z hz; obtain ⟨y,hY,rfl⟩ := Finset.mem_image.mp hz
  exact T.fits_stencil ht (h _ hY)

lemma inherits (hg : m≤k) (hk : k≤N) : Cells.span C.S hk p ∣ Cells.span C.S (hg.trans hk) p := by
  have hv d e (h : d ≤ e) := C.S.embeds_scale (C.S.toDepth h p)
  have hh : C.S.a N * (Cells.span C.S hk p * (↑(Cells.span C.S hg p):ℝ)) =
      C.S.a N * Cells.span C.S (hg.trans hk) p := by rw [hv,← mul_assoc,hv,hv]
  have hx := mul_left_cancel₀ (C.S.a_pos N).ne' hh
  exact ⟨Cells.span C.S hg p,by exact_mod_cast hx.symm⟩

def Fit (v : C.book.Token) (k N : ℕ) (p) := ∃ h : k≤N, ∀ z∈(C.localSection v.1).stencil,
    ∀ i, (z i).natAbs < Cells.span C.S h p

lemma fit (v : C.book.Token) (k : ℕ) : ∀ᶠ i : ℕ in atTop, ∀ p : ℕ, Fit v k (f.mesh i) p := by
  have he z (_ : z∈(C.localSection v.1).stencil) (b) : ∀ᶠ i : ℕ in atTop, ((z b).natAbs:ℝ)*C.S.a (f.mesh i) < C.S.a k := by
    have hv := (((C.S.shrinks.comp f.mesh.cofinal).const_mul ((z b).natAbs:ℝ)))
    rw [mul_zero] at hv
    exact hv.eventually (gt_mem_nhds (C.S.a_pos _))
  have ht := eventually_all_finset _ |>.mpr (fun z (hz:z∈(C.localSection v.1).stencil) => eventually_all.mpr (he z hz))
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop k),ht] with i h H p
  refine ⟨h,fun z hz a => ?_⟩
  apply (Nat.cast_lt (α := ℝ)).mp
  apply lt_of_mul_lt_mul_left _ (C.S.a_pos (f.mesh i)).le
  rw [show _ * (↑(Cells.span C.S h p):ℝ)=_ from C.S.embeds_scale (C.S.toDepth h p), mul_comm]
  exact H z hz a

open Spin in
def imageBudget (v : Fin n→C.book.Token) (A : ℝ) (k N p : ℕ) := k≤N ∧
    ∀ i j, centeredBudget C (token C.book (v i) j) A k N p ∧ Fit (token C.book (v i) j) k N p

lemma image_ (v : Fin n → C.book.Token) (h : CenteredBook C f) :
    (∀ p, ∀ᶠ k in atTop, ∃ A : ℝ, 0≤A ∧ ∀ᶠ j in atTop, imageBudget v A k (f.mesh j) p) ∧
    (∀ᶠ k in atTop, ∃ A : ℝ, 0≤A ∧ f.late (imageBudget v A k)) := by
  let T (i : Fin n × Spin.Frame) := Spin.token C.book (v i.1) i.2
  have he k : ∀ᶠ j : ℕ in atTop, ∀ i, ∀ p, Fit (T i) k (f.mesh j) p := eventually_all.mpr fun i => fit _ _
  have hm (p : ℕ) := lib C f Finset.univ h p T
  have hg k := f.mesh.cofinal.eventually (eventually_ge_atTop k)
  constructor
  · intro p; filter_upwards [(hm p).1] with k hk
    obtain ⟨A,hA,H⟩ := hk; refine ⟨A,hA,?_⟩
    filter_upwards [H,hg k,he k] with j hh hv hu; exact ⟨hv, fun i b => ⟨hh (i,b) (Finset.mem_univ _),hu (i,b) p⟩⟩
  filter_upwards [(hm 0).2] with k hk
  obtain ⟨A,hA,H⟩ := hk; refine ⟨A,hA,?_⟩
  refine H.mono fun i hi => ((hi.and (he k)).and (hg k)).mono ?_
  rintro j ⟨⟨hv,hh⟩,hy⟩; exact ⟨hy, fun x b => ⟨hv (x,b) (Finset.mem_univ _), hh (x,b) _⟩⟩

open Gaps Spin in
lemma fits_budget (H : C.Makes) (v : Fin n → C.book.Token) (W : Set (Points n)) (r : ℝ)
    (hK : ∀ x∈W, someFine C.S p r x) (A : ℝ) (hx : C.S.a m < r) (hg : m≤k)
    (hw : (n:ℝ)*(2*(3*C.S.a k)) < C.S.a m) (ht : imageBudget v A k N p) (u : Fin n→Cover)
    (hU : tag (C.S.a N) u ∈ W) : ‖lifted C N p v u‖ ≤ A^n := by
  obtain ⟨hN,hC⟩ := ht
  let t := Cells.span C.S hN p
  let x := wrap (C.side N p) ∘ u
  let T := center C.S p (hg.trans hN) 0
  have hs : C.S.a N * t=C.S.a k := C.S.embeds_scale (C.S.toDepth hN p)
  have he : C.S.a N * ↑T.side.val=C.S.a m := C.S.embeds_scale T.units
  have hp : (n:ℕ)*(2*(3*t)) < T.side.val := by
    apply (Nat.cast_lt (α := ℝ)).mp; apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le
    rw [he]; rw [← hs] at hw; push_cast; linarith
  obtain ⟨o,ho⟩ := T.fits_together x (3*t) (by exact Nat.mul_pos (by decide) ((C.S.toDepth hN p).count.property)) hp
  let X := T.newly o
  have hv : Cells.span C.S hN p ∣ X.side.val := inherits hg hN
  let D (i : Fin n) := X.which (x i)
  have HD (i) : x i ∈ X.margin (D i) (3*t) := ho i
  have hm : Injective D := by
    intro i j h; by_contra H
    have hh := gridSeparation C.S x rfl (hK _ hU) _ _ H
    have hl := X.extent (v := D i) (x := x j) (y := x i) (h.symm ▸ (HD j).1) (HD i).1
    have hi : r ≤ C.S.a m := hh.trans (le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (C.S.a_pos N).le) he.le)
    exact hx.not_ge hi
  choose a ha using fun i => X.pointed (D i) (x i)
  let V (i) := let s := way X (D i); token C.book (v i) (s.1⁻¹,s.2)
  have hQ (i) : a i∈X.margin 0 (3*t) := (X.reflected_margin (a i) ..).2 (ha i |>.symm ▸ HD i)
  have hT i := hC i ((way X (D i)).1⁻¹,(way X (D i)).2)
  have HH i : C.ref (V i).1≤N := (hT i).1.choose_spec.1
  let f (i) := C.seen (V i) (a i)
  have Hs i : ∀ z∈(C.localSection (V i).1).stencil, ∀ b, (z b).natAbs<t := (hT i).2.choose_spec
  have ha' i : Interior (X.chamber 0) (f i) := figure H _ (V i) (3*t) (a i) (hQ i) (fun z hz b => by have := Hs i z hz b; omega)
  have HD i : X.rootTest (C.beta N p) (f i) ≤ A := by
    apply interior_from X (V i) H hN hv A _ _ _ (hQ i)
    · intro b; simp_rw [V,orientation]; exact (hC _ _).1
    intro o ho; exact figure H _ (V i) (2*t) o ho (fun z hz b => by have := Hs i z hz b; omega)
  have hw i : X.copy (D i) (f i) = C.seen (v i) (x i) := by
    rw [show X.copy (D i) _=_ from Spin.uses H X (D i) _ (V i) (HH i),ha]; simp [V]
  have hu := X.planted (seamless H ..) D hm f ha'
  have hz := hu.trans (Finset.prod_le_prod (fun i _ => X.root_nonneg _ _) fun i _ => HD i)
  simp_rw [hw,Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hz; exact hz

private lemma room_scale (S : Schedule) (n : ℕ) (m) : ∀ᶠ k in atTop, (n:ℝ)*(2*(3*S.a k))<S.a m :=
    (show Tendsto (fun k => (n:ℝ)*(2*(3*S.a k))) atTop (𝓝 0) from by
      simpa only [mul_zero] using (((S.shrinks.const_mul (3:ℝ)).const_mul (2:ℝ)).const_mul (n:ℝ))).eventually (gt_mem_nhds (S.a_pos m))

lemma size_done (H : C.Makes) (he : CenteredBook C f) : Bound C f := by
  constructor
  · intro n v p W hW hp
    obtain ⟨r,hr,ht⟩ := Gaps.some _ p hW hp
    obtain ⟨m,hm⟩ := (C.S.shrinks.eventually (gt_mem_nhds hr)).exists
    obtain ⟨k,⟨A,hA,H'⟩,he,hw⟩ := (((image_ v he).1 p).and ((eventually_ge_atTop m).and (room_scale C.S n m))).exists
    exact ⟨_,pow_nonneg hA n,H'.mono fun i hi u hu => fits_budget H v W r ht A hm he hw hi u hu⟩
  intro n v K hK ht
  obtain ⟨r,hr,hp⟩ := Gaps.someGrows C.S hK ht
  obtain ⟨m,hm⟩ := (C.S.shrinks.eventually (gt_mem_nhds hr)).exists
  obtain ⟨k,⟨A,hA,H'⟩,he,hw⟩ := ((image_ v he).2.and ((eventually_ge_atTop m).and (room_scale C.S n m))).exists
  unfold Order.late at *
  exact ⟨_,pow_nonneg hA n, (H'.and (f.per.cofinal.eventually hp)).mono fun i h => h.1.mono fun j hJ u hu => fits_budget H v K r h.2 A hm he hw hJ u hu⟩
end Around

/-- First actual common extraction from the projected chessboard receipts. -/
theorem crops (H : C.Makes) (h : CenterPort C f) : ∃ g : Order, ∃ S P, RawLimits C (f.refine g) S P :=
    first_surface _ _ (Difference.completed H (h.book _ _)) (Around.size_done H (h.book _ _))
end YM.Extraction
