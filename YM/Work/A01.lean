import YM.Bid.Angular
import YM.Work.A01.Conserve
import YM.Work.A01.Mirror


/-!
# A01: Recover the compatibility properties of *both* raw shell maps

For every point test in the all-spectator quotient, with its specified
center, take an actual smooth compact window. Use the supplied local
identities, kernel symmetries and equality of reads under inclusion. For
the unit use conservation and symmetry on the word with the unit deleted.
We never compare correlations at collisions, nor assume rotation/Lie
laws beyond the supplied H data.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A01
open Function Table Climb
open scoped BigOperators

section
variable {G : Gauge} {L : Register G} {S : Table L} (h : S.Hierarchy)
variable (W : DiffPlan S) {J : S.Stress} {p : Climb.Parts S} {Y : Ward.SpinRows S}

theorem translation_color (hr : W.Inclusions S) (hd : W.Derivatives S) (hp : Pre h W J p Y) :
    ColorLaw p W h.spin := by
  have hi (d e : ℕ) (w : d ≤ e) (i : Axis) (v) : p e i (W.rise w v)=W.rise (Nat.succ_le_succ w) (p d i v) := by
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    rw [hr.kernels _ _ hx, ← hp.raw.translation hx q hχ i e, ← hp.raw.translation hx q hχ i d,
      ← flux_translation, ← flux_translation, flux_inclusion h.laws.toSymmetric hx W hr J hχ]
  have hu (d i) : p d i (S.unit d) = 0 := by
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    rw [← front_eval q x _ 0, map_zero, ← hp.raw.translation hx q hχ i d, ← flux_translation]
    exact flux_unit h.laws h.smooth W hd J hp.tensor _ (fun _ => contDiff_const) (killing_const _) hx q χ hχ d
  refine ⟨fun d => ⟨fun i => ⟨hu d i, fun a w v => ⟨_, (hi a d w i v).symm⟩⟩, ?_, ?_⟩, hi⟩
  · intro i k v
    change S.mirror h.spin (d+1) k (p d i v) =
      ∑ j : Axis, (↑(k.matrix j i):ℂ) • p d j (S.mirror h.spin d k v)
    rw [eps_column]
    apply ext_against_mirror h.laws.toSymmetric h.spin k
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    have hb := mirror_eval h.laws.toSymmetric h.spin hx (Fin.cons ⟨_,p d i v⟩ q) k
    rw [comp_cons, show mirrorTag h.spin k ⟨_,p d i v⟩=⟨_,S.mirror h.spin (d+1) k (p d i v)⟩ from rfl] at hb
    rw [hb]
    let φ := shifted k.ortho χ
    let B := S.mirror h.spin d k v
    change _ = S.useAt S _ (Fin.cons ⟨d+1,(eps k i:ℂ) • p d (k.perm i) B⟩ _)
    have hw := hp.raw.translation (Points.move_in k.ortho hx) (mirrorTag h.spin k ∘ q)
      (window_move k.ortho hχ) (k.perm i) d B
    calc
      _ = flux J χ (fun _ => basis i) x q v := by
        rw [flux_translation, hp.raw.translation hx q hχ i d v]
      _ = flux J φ (fun _ => eps k i • basis (k.perm i)) (Points.move k.ortho x)
          (mirrorTag h.spin k ∘ q) B :=
        (flux_mirror h.laws.toSymmetric h.spin J hp.symmetric k hx hχ _ _
          (fun _ => (move_basis k i).symm) q v).symm
      _ = (eps k i:ℂ) * shellGrad S J φ (k.perm i) (Points.move k.ortho x)
            (mirrorTag h.spin k ∘ q) B := by
        rw [flux_scale J φ (fun _ => basis (k.perm i)), flux_translation]
      _ = _ := by rw [← front_eval _ _ _ ((eps k i:ℂ) • _), map_smul, front_eval, ← hw]; rfl
  · intro i v
    change S.conj h.spin (d+1) (p d i v) = p d i (S.conj h.spin d v)
    apply ext_against_real h.laws.toSymmetric h.spin
    intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    have ht := real_eval h.laws.toSymmetric h.spin hx (Fin.cons ⟨_,p d i v⟩ q)
    rw [comp_cons, show realTag h.spin ⟨_,p d i v⟩=⟨_,S.conj h.spin (d+1) (p d i v)⟩ from rfl] at ht
    rw [ht, ← hp.raw.translation hx q hχ i d, ← hp.raw.translation hx _ hχ i d,
      ← flux_translation, ← flux_translation, flux_real h.laws.toSymmetric h.spin J hp.tensor.real hx hχ]

theorem angular_hyper (hr : W.Inclusions S) (hd : W.Derivatives S) (hp : Pre h W J p Y) :
    Bid.Hyper h.spin W Y := by
  constructor
  · intro d u v
    apply ext_against_real h.laws.toSymmetric h.spin
    intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    have ht := real_eval h.laws.toSymmetric h.spin hx (Fin.cons ⟨_,Y d u v⟩ q)
    rw [comp_cons, show realTag h.spin ⟨_,Y d u v⟩=⟨_,S.conj h.spin d (Y d u v)⟩ from rfl] at ht
    rw [ht, ← hp.raw.rotation hx q hχ u, ← hp.raw.rotation hx _ hχ u,
      ← flux_spin, ← flux_spin, flux_real h.laws.toSymmetric h.spin J hp.tensor.real hx hχ]
  · intro d e w u v
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    rw [hr.kernels w _ hx, ← hp.raw.rotation hx q hχ u e, ← hp.raw.rotation hx q hχ u d,
      ← flux_spin, ← flux_spin, flux_inclusion h.laws.toSymmetric hx W hr J hχ]
  · intro d u
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    rw [← front_eval q x _ 0, map_zero, ← hp.raw.rotation hx q hχ u, ← flux_spin]
    exact flux_unit h.laws h.smooth W hd J hp.tensor (orbital u (x 0)) (smooth_orbital _ _)
      (killing_orbital _ _) hx q χ hχ d
  · intro d k u v
    apply ext_against_mirror h.laws.toSymmetric h.spin k
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window x hx
    have hb := mirror_eval h.laws.toSymmetric h.spin hx (Fin.cons ⟨_,Y d u v⟩ q) k
    rw [comp_cons, show mirrorTag h.spin k ⟨_,Y d u v⟩=⟨_,S.mirror h.spin d k (Y d u v)⟩ from rfl] at hb
    rw [hb, ← hp.raw.rotation hx q hχ u d,
      ← hp.raw.rotation (Points.move_in _ hx) _ (window_move _ hχ) (Org.orients k u),
      ← flux_spin, ← flux_spin]
    exact (flux_mirror h.laws.toSymmetric h.spin J hp.symmetric k hx hχ
      (orbital u (x 0)) (orbital (Org.orients k u) (Ortho.move k.ortho (x 0))) (move_rotation k u (x 0)) q v).symm
end

theorem answer : YM.Bid.A01 := by
  intro G L S h W hd hr _ J p Y hp
  exact ⟨translation_color h W hr hd hp, angular_hyper h W hr hd hp⟩

end YM.Work.A01
