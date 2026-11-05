import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.PathPair
import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Awaken
import YM.MergeProof.Badlands
import YM.MergeProof.North.GraceN
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spinto
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Marginal
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
open Extraction.Gaps Extraction.Spin
variable {p k N m:ℕ}
lemma contour (H : C.Makes) (v : Fin n → C.book.Token) (W : Set (Points n)) (r : ℝ)
    (hK : ∀ x∈W, someFine C.S p r x) (A : Fin n→ ℝ) (hx : C.S.a m < r) (hg : m≤k)
    (hw : (n:ℝ)*(2*(3*C.S.a k)) < C.S.a m) (ht : k ≤ N ∧ ∀ i j, centeredBudget C (Extraction.Spin.token C.book (v i) j) (A i) k N p ∧ Fit (Extraction.Spin.token C.book (v i) j) k N p) (u : Fin n→ Lattice.Cover)
    (hU : tag (C.S.a N) u ∈ W) : ‖lifted C N p v u‖ ≤ ∏ i,A i := by
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
  have HD i : X.rootTest (C.beta N p) (f i) ≤ A i := by
    apply interior_from X (V i) H hN hv (A i) _ _ _ (hQ i)
    · intro b; simp_rw [V,orientation]; exact (hC _ _).1
    intro o ho; exact figure H _ (V i) (2*t) o ho (fun z hz b => by have := Hs i z hz b; omega)
  have hw i : X.copy (D i) (f i) = C.seen (v i) (x i) := by
    rw [show X.copy (D i) _=_ from Extraction.Spin.uses H X (D i) _ (V i) (HH i),ha]; simp [V]
  have hu := X.planted (seamless H ..) D hm f ha'
  have hz := hu.trans (Finset.prod_le_prod (fun i _ => X.root_nonneg _ _) fun i _ => HD i)
  simp_rw [hw] at hz; exact hz

lemma expanding (H : CellHyp C F) (x : C.book.Token) :
    ∀ᶠ m in atTop,F.late (centeredBudget C x (Real.exp (((x.1:ℝ)+2)*C.S.scale m)) m) := by
  rcases x with ⟨d,v⟩
  obtain ⟨m₀,hp,A,hA,η⟩ := H.centered d 1 (‖v‖+1) (by norm_num) (by positivity)
  let e:ℝ:= -(d:ℝ)-1; let w i:=C.S.a i^e
  have hh: Note C.S (fun i=>(A+1)*w i) (0+e*(-1)):= (Note.notes C.S _ (by linarith :0<A+1)).mills ((Note.note_a C.S).powr e)
  have he: e≤0:=by dsimp [e]; linarith [Nat.cast_nonneg (α:=ℝ) d]
  filter_upwards [eventually_ge_atTop m₀,hh.outweigh (Note.bell_exp C.S ((d:ℝ)+2)) (by unfold e; linarith),C.S.shrinks.eventually (ge_mem_nhds (α:=ℝ) (by norm_num : (0:ℝ) < 1))] with m hm hh hx
  apply (η _ hm 1 (by norm_num)).mono
  intro i hi; refine hi.mono fun j hj => ?_
  obtain ⟨h,hj⟩ := hj; refine ⟨h,hp.trans (hm.trans h),fun o => ⟨(hj v (by simp) o).1,(hj v (by simp) o).2.trans (?_)⟩ ⟩
  refine le_trans ?_ hh; rw [add_mul,one_mul]
  exact add_le_add_right (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (C.S.a_pos _) hx he) _

lemma spectra {v:Fin n→ C.book.Token} (H: CellHyp C F):∀ᶠ m in atTop, ∀ᶠ u:ℕ×ℕ in F.fuse, m≤u.1∧∀ i j, centeredBudget C (Extraction.Spin.token C.book (v i) j) (Real.exp ((((v i).1:ℝ)+2)*C.S.scale m)) m u.1 u.2 ∧ Fit (Extraction.Spin.token C.book (v i) j) m u.1 u.2:=by
  let T := fun i : Fin n × Extraction.Spin.Frame => Extraction.Spin.token C.book (v i.1) i.2
  filter_upwards [eventually_all.mpr (fun i => expanding H (T i))] with k hk
  have ht : ∀ᶠ u:ℕ×ℕ in F.fuse, ∀ i,centeredBudget C (T i) (Real.exp ((((T i).1:ℝ)+2)*C.S.scale k)) k u.1 u.2:= eventually_all.mpr fun i=> hk i
  have he : ∀ᶠ u in F.fuse, ∀ i, Around.Fit (T i) k u.1 u.2 := eventually_all.mpr fun i => by
    rw [Extraction.Order.fused]; exact Eventually.of_forall fun r => (Around.fit (f:=F) (T i) k).mono fun p hp => hp _
  filter_upwards [ht,he,large_mesh F k] with u h hp hv
  refine ⟨hv,fun i j=>⟨?_,hp (i,j)⟩⟩
  have hx : (T (i,j)).1=(v i).1:= by dsimp [T,Extraction.Spin.token]; split <;> rfl
  specialize h (i,j); rw [hx] at h;exact h
end YM.MergeProof.Ribbons
