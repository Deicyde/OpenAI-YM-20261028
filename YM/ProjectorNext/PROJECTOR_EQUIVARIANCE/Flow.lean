import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Cylinders

/-!
# Transport of equation densities

Through each step of `E : Packet C ...`. This part CAN use equality of
unnormalized densities. Even the unmarked `eval` itself has the transport,
by the actual kernel. Use `Levels.blocks`, with the shared choices (not
separate tags for pushes of different rows). At this interface only use
translations giving embedded coarse sites for a step, and the genuine
rotations of the lattice (signed permutations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source MeasureTheory Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

section Schedule
variable (L : Levels G) (m p : ℕ) (β : ℝ)

/-- If pulling an input by the embedded pull, the pushed function is pulled
by the given coarse map. This also proves just the origin orientation law by
`b = 0`. -/
lemma push_pull {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Config G (L.S.side (m+1) p) → Y) (hF : Integrable F (prior G _))
    (s : Signed) (b : Site (L.S.side m p)) :
    let T := L.clock.op m p
    T.push β (F ∘ pull s (T.ratio.embed b)) = T.push β F ∘ pull s b := by
  intro T
  let q := pull (K:=G.El) s (T.ratio.embed b)
  have hq : MeasurePreserving q (prior G _) (prior G _) := prior_pull ..
  funext U
  let u := pull s b U
  let V := fun x => T.density β x u • F x
  have hi : Integrable V (prior G _) := StepData.push_slice (L.transition_mass ..) u F hF
  have he := integral_map (φ:=q) (f:=V) hq.aemeasurable
    (by rw [hq.map_eq]; exact hi.aestronglyMeasurable)
  rw [hq.map_eq] at he
  change (∫ x, T.density β x U • F (q x) ∂prior G _) = ∫ x, V x ∂prior G _
  rw [he]
  unfold V
  simp_rw [show ∀ x, T.density β (q x) u = T.density β x U from fun x => (L.blocks m p).symmetric ..]

lemma push_star (F : Config G (L.S.side (m+1) p) → ℂ) :
    (L.clock.op m p).push β (star F) = star ((L.clock.op m p).push β F) := by
  let T := L.clock.op m p
  funext U
  have he (x : Config G (L.S.side (m+1) p)) : T.density β x U • star (F x) = star (T.density β x U • F x) := by
    simp only [star_smul,star_trivial]
  change (∫ x, T.density β x U • star (F x) ∂prior G _) = star _
  simp_rw [he]
  exact integral_conj
end Schedule

lemma eval_pull {H : RG.History G} (hc : H.Selected) (N p m : ℕ) (hm : m ≤ N) (s : Signed)
    (b : Site (H.S.side m p)) : (H.rep N p m).eval ∘ pull s b = (H.rep N p m).eval := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [(hc.starts N p).2]; exact funext fun U => by simp only [bare,Function.comp_apply,energy_pull]
  | of_succ k hk hi =>
    have he := (H.rep N p (k+1)).envelope (hc.represents N p (k+1) hk).good
    rw [(hc.steps N p k hk).1, ← push_pull H.levels k p _ _ (he.integrable _) s b, hi]

section Packet
variable {d N p : ℕ} {C : Family G} {E : Packet C d N p} {S : Finset Cover}

/-- Actual charge at m of E. -/
def charge (E : Packet C d N p) (m : ℕ) (v : SourceSpace (C.labels.level d)) :=
  (E.chain m v).density 0 (C.localSection d) (C.path.rep N p m)

lemma charge_roll (hc : C.Makes) (hE : E.ComesFrom S) (h : PhysicalAction E.weights)
    (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) (v : SourceSpace (C.labels.level d)) (s : Signed) :
    charge E m (sw _ s v) = charge E m v ∘ pull s 0 := by
  induction hm using Nat.decreasingInduction with
  | self =>
    funext U; unfold charge
    rw [comp_apply,hE.encode,hE.encode, h.Jorigin_roll]
    rw [show (C.path.rep N p N).eval (pull s 0 U) = (C.path.rep N p N).eval U from
      congr_fun (eval_pull hc.wilson N p N le_rfl s 0) U]
  | of_succ k hk hi =>
    let T := C.path.levels.clock.op k p
    have hh (v) : charge E k v = _ := hE.transfer k hr hk v
    rw [hh,hh]
    have he : (C.path.levels.clock.op k p).ratio.embed 0 = 0 := map_zero T.ratio.root
    have hz : T.push (C.path.β N p (k+1)) (charge E (k+1) (sw _ s v)) = T.push (C.path.β N p (k+1)) (charge E (k+1) v) ∘ pull s 0 := by
      rw [hi (hr.trans k.le_succ)]
      simpa only [he] using push_pull C.path.levels k p (C.path.β N p (k+1)) (charge E (k+1) v) (hE.density_int v hc _ (hr.trans k.le_succ) hk) s 0
    change _ • T.push _ (charge E (k+1) _) = (_ • T.push _ (charge E (k+1) _)) ∘ _
    rw [hz]; rfl

lemma charge_star (hE : E.ComesFrom S) (h : PhysicalAction E.weights)
    (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) (v : SourceSpace (C.labels.level d)) :
    charge E m (cw _ v) = star (charge E m v) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    funext U; unfold charge
    rw [Pi.star_apply,hE.encode,hE.encode, h.Jorigin_bar]
    simp
  | of_succ k hk hi =>
    let β := C.path.β N p (k+1)
    let T := C.path.levels.clock.op k p
    have hh (v) : charge E k v = ((C.S.block k).val : ℂ)^d • T.push β (charge E (k+1) v) := hE.transfer k hr hk v
    rw [hh,hh,hi (hr.trans k.le_succ), show T.push β (star (charge E (k+1) v)) = _ from
      push_star C.path.levels k p β (charge E (k+1) v)]
    simp [T]


end Packet
end YM.ProjectorNext.Equivariance
