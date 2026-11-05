import YM.Pert.Weak
import YM.Next.MAXWELL.Lit

/-!
Ward calibration and the order-zero insertions. Not taking conservation as a
field normalization: we use `StressLaws.translation`, on all inner fields,
which fixes the sign/scale in the comparator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert
open Function Filter Climb Org Next.UVStress Spec Table Ward
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

section Canonical
open UVNext.FreeStress Maxwell
variable (F : Labels.Frames G)

theorem initial_curl (a b : Axis) (c : G.ColorIndex) : curlProbe (initialPlace a b) c=Free.omegaLeg c a b :=
  congrArg (fun p : Fin 0 → E4=>Maxwell.constrain (Maxwell.fromF G p c a b)) (Subsingleton.elim ..)

theorem address_flat (a k b j : Axis) : Free.address F 4 (flat F a k b j)=Free.phi a b k j := by
  change ((Free.fields F 4) ((freeTable F).project 4 ((F.level _).coords (ff G 4 le_rfl a k b j)))).val=_
  rw [Free.fields_eval]
  change observable G 4 ((F.level 4).coords.symm ((F.level 4).coords _))=_
  rw [LinearEquiv.symm_apply_apply,ff,shell_bond]; simp_rw [initial_curl]; rfl

theorem address_panel (a b : Axis) : panel F a b = (Free.fields F 4).symm
    ⟨Free.sheetEnergy a b,by
      simp_rw [Free.sheetEnergy, ← address_flat F]
      exact Submodule.sum_mem _ fun _ _ => Free.address_in _ _ _⟩ := by
  apply Free.address_inj F
  trans Free.sheetEnergy a b
  · rw [panel,map_sum]; simp_rw [address_flat]; rfl
  exact Eq.symm (congrArg Subtype.val ((Free.fields F 4).apply_symm_apply _))

theorem common_stress : torch F 1 = Free.original F := by
  funext a b; apply Free.address_inj F
  rw [torch,one_smul,canonicalStress,map_sub,Free.inertia,Free.polStress]
  have h (x y : Axis) : Free.address F 4 (panel F x y) = Free.sheetEnergy x y := by
    rw [panel,map_sum]; simp_rw [address_flat]; rfl
  rw [h]
  split_ifs with ht
  · subst b; rw [total,map_smul,map_sum];
    simp_rw [show ∀ i : Axis, Free.address F 4 (∑ k, flat F i k i k) = Free.sheetEnergy i i from fun i=> h i i,
      Free.kr]
    simp
  rw [map_zero]; simp_rw [Free.kr]; simp [ht]
end Canonical
section Normalize
variable {C : Family G} {S : Table C.book} {F : Extraction.Order} {W : DiffPlan S}
    {M : MaxwellData C} {I : IR (C:=C) S} {X : Scaling S}

variable (p : Supplier F W M I X)

theorem same_translation {B0 : Register G} {S : Table B0} {d0 d1 : ℝ} {L : S.Stress} (h : S.Hierarchy) {D : DiffPlan S} {A B : SpinRows S}
    (hn : leaves D.deriv 4 ≠ 0) (hA : StressLaws S L (d0 • D.deriv) A) (hB : StressLaws S L (d1 • D.deriv) B) :
    d0=d1 := by
  suffices e : d0 • leaves D.deriv 4=d1 • leaves D.deriv 4 from smul_left_injective ℝ hn e
  funext b; apply ContinuousLinearMap.ext; intro v; apply S.field_ext h.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
  exact (hA.translation hx q hχ b 4 v).symm.trans (hB.translation hx q hχ b 4 v)

set_option maxHeartbeats 500000 in
theorem kappa_eq (hG : G.Simple) (hM : M.T.W=Maxwell.Free.scheme C.labels) (hJ : M.T.J=UVNext.FreeStress.torch C.book.grid 1) : M.T.κ=(-1:ℝ) := by
  have hM : M.T.W=Maxwell.Free.scheme C.book.grid := hM
  have hi := M.lit.delta
  have ht := (Maxwell.Free.shines C.book hG 1 one_ne_zero).delta
  have hh : StressLaws (Bel C.book) M.T.J (-(1:ℝ) • M.T.W.deriv) (-(1:ℝ) • (Maxwell.Free.gear C.book.grid).lie) := by
    rw [hM,hJ,common_stress]
    simpa only [Maxwell.Free.herald,one_smul] using ht
  let L := Bel C.book
  exact same_translation (S:=Bel C.book) M.hT M.lit.born hi hh

abbrev Slots (n : ℕ) := Fin n
def mixedTag {n : ℕ} (q : Slots n → (Bel C.book).Tag) (isJ : Slots n → Bool)
    (ab : Slots n → Axis × Axis) (T0 : (Bel C.book).Stress) (i : Slots n) : (Bel C.book).Tag :=
  if isJ i then ⟨4,T0 (ab i).1 (ab i).2⟩ else q i

def scaledPhysical (X : Scaling S) (J : S.Stress) (k : ℕ) {n : ℕ} (q : Slots n → (Bel C.book).Tag)
    (isJ : Slots n → Bool) (ab : Slots n → Axis × Axis) (i : Slots n) : S.Tag :=
  if isJ i then ⟨4,((X.r k^4 : ℝ):ℂ) • J (ab i).1 (ab i).2⟩ else ⟨_,X.U k _ (q i).2⟩

set_option maxHeartbeats 700000 in
include p in
lemma mixed_leading {c U J} (b : Tab S W M I p.uv c U J) {n : ℕ} (q : Slots n → (Bel C.book).Tag)
    (isJ : Slots n → Bool) (ab : Slots n → Axis × Axis) (j : ℕ) {K : Set (Points n)} (hK : IsCompact K)
    (hsep : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun z => disc (scaledPhysical X J k q isJ ab) (X.r k • z)) x-
      iteratedFDeriv ℝ j (disc (mixedTag q isJ ab ((M.T.κ)⁻¹ • M.T.J))) x‖ ≤ ε := by
  let d (i : Slots n) : ℕ := if isJ i then 4 else (q i).1
  let f (i : Slots n) := mixedTag (C:=C) q isJ ab ((M.T.κ)⁻¹ • M.T.J) i
  let g (k : ℕ) (i : Slots n) := scaledPhysical X J k q isJ ab i
  have hs i : (f i).1=d i := by cases hq : isJ i <;> simp [f,mixedTag,hq,d]
  have ht k i : (g k i).1=d i := by cases hq : isJ i <;> simp [g,scaledPhysical,hq,d]
  let u (i : Slots n) : (Bel C.book).Field (d i) := _root_.cast (congrArg _ (hs i)) (f i).2
  let v (k : ℕ) (i : Slots n) : (Bel C.book).Field (d i) := (X.U k (d i)).symm (_root_.cast (congrArg _ (ht k i)) ((g k i).2))
  have hu : hang d u=f := funext fun i => Sigma.ext (hs i).symm (show (_root_.cast _ _ ≍ _) from cast_heq ..)
  have hv k : panels (isoPanel X k) ∘ hang d (v k)=g k := by
    funext i; change (⟨d i,X.U k (d i) ((X.U k (d i)).symm _)⟩ : S.Tag)=_
    rw [LinearEquiv.apply_symm_apply]; exact Sigma.ext (ht k i).symm (show (_root_.cast _ _ ≍ _) from cast_heq ..)
  have hl (i : Slots n) : Tendsto (fun k => v k i) atTop (𝓝 (u i)) := by
    have hf (s : Bool) :
        let d : ℕ := if s then 4 else (q i).1
        let g (k : ℕ) := if s then (⟨4, (↑(X.r k^4:ℝ):ℂ) • J (ab i).1 (ab i).2⟩ : S.Tag) else ⟨(q i).1, X.U k _ (q i).2⟩
        let f := if s then (⟨4, (M.T.κ)⁻¹ • M.T.J (ab i).1 (ab i).2⟩ : (Bel C.book).Tag) else q i
        ∀ (h : f.1=d) (h' : ∀ k, (g k).1=d), Tendsto (fun k => (X.U k d).symm (_root_.cast (congrArg _ (h' k)) (g k).2)) atTop
          (𝓝 (_root_.cast (congrArg ((Bel C.book).Field) h) f.2)) := by
      cases s
      · change ∀ h h', Tendsto (fun k => (X.U k (q i).1).symm (X.U k _ _)) atTop (𝓝 _)
        simp
      change ∀ h h', Tendsto (fun k => (X.U k 4).symm ((↑(X.r k^4:ℝ):ℂ) • _)) atTop (𝓝 _)
      intro _ _
      apply meter_physical p b.locality.conserved (fun s i j => ?_) b.locality.charges
      rw [← b.locality.spots.signed]
      exact b.locality.spin ..
    change Tendsto (fun k => (X.U k _).symm (_root_.cast (congrArg _ (ht k i)) (g k i).2)) _
      (𝓝 (_root_.cast (congrArg ((Bel C.book).Field) (hs i)) (f i).2))
    exact hf (isJ i) (hs i) fun k=>ht k i
  have e := travels_jet p.uv.basis.kernel p.deriv M.hT M.lit.pales X p.limit_ v u hl j K hK hsep ε he
  filter_upwards [e] with k hk
  unfold Next.UVStress.tested at hk
  rw [hv, hu] at hk; exact hk
end Normalize
end YM.Pert
