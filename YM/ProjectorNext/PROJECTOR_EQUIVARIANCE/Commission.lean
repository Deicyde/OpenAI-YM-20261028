import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Anchors
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Flow
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Hues
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Move
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Panel


/-!
# One way to actually supply the transfer-action premises

When starting with covariant weight-side constructions, if obtaining
`ComesFrom` via an algorithm directly supplying `Customs` is difficult,
there is an alternative. HERE choose the packet, *before* any estimation
campaign on its contrasts or comparison to primary. From ANY chain proving
`ComesFrom` on these physical W, build another one (same F, history,
weights, densities, same orientation/ordinary convention), explicitly
averaged; it still meets the `ComesFrom` charges including cap, all fitted
levels, now also meets `Customs` including indexed support movement.

Do NOT use to change a prescription of a normalization after paying prices!
This can change `.chain` AND its `.matrixAt`, so all continuation estimates
(including Compares/Bill, rank ones, rank requirements at each period,
relay/detector data, etc.) have to use the resulting choice. Not an
assertion this obtains those hypotheses a campaign needs; not assuming
they are stable under averaging. Unmarked `Activities`, all level data and
tags actually held fixed (forced names too). Supply same C.Makes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
namespace Commission
open Function Filter Labels Lattice Wilson RG Source MeasureTheory Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {p N d : ℕ} {C : Family G} (hc : C.Makes) (E : Packet C d N p)

abbrev Key := Signed × Bool

def dealer : ℕ ≃ Key × ℕ := by
  classical
  letI : Encodable Key := Fintype.toEncodable _
  letI : Denumerable (Key × ℕ) := Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv _).symm

def fare : ℂ := (Fintype.card Key:ℂ)⁻¹

def shade {n : Side} {F : Frame G d} (b : Bool) (Q : Coefficient F n) : Coefficient F n :=
  if b then pigment Q else Q

def keydir (F : Frame G d) (k : Key) (w : SourceSpace F) : SourceSpace F :=
  let x := sw F k.1⁻¹ w
  if k.2 then cw F x else x

def motors (k : Key) (m : ℕ) (hm : m≤N) : (C.path.rep N p m).activities.Moves k.1 0 :=
  Classical.choice ((hc.wilson.represents N p m hm).good.labels.moves k.1 0)

def arc (w : SourceSpace (C.labels.level d)) (m : ℕ) (hm : m≤N) (k : Key) :=
  repaint fare (shifted (motors (p:=p) hc k m hm) (shade k.2 (E.chain m (keydir _ k w))))

def reserve (m : ℕ) (w : SourceSpace (C.labels.level d)) : Coefficient (C.labels.level d) (C.side m p) :=
  if hm : m ≤ N then panel dealer (arc hc E w m hm) else E.chain m w

lemma arc_x (m : ℕ) (hm : m≤N) (k : Key) : IsLinearMap ℂ fun w => (arc hc E w m hm k).x := by
  have hj := E.linear_x m
  rcases k with ⟨s,a⟩; cases a <;> constructor
  · intro x y; change fare • turn _ s _ = fare • turn _ s _ + fare • turn _ s _
    simp only [shade,keydir,Bool.false_eq_true, ↓reduceIte,map_add]; rw [hj.map_add]; simp
  · intro x y; change fare • turn _ s _ = x • fare • turn _ s _
    simp only [shade,keydir,Bool.false_eq_true, ↓reduceIte,map_smul]; rw [hj.map_smul]; simp [smul_comm x]
  · intro x y; change fare • turn _ s (star _) = fare • turn _ s (star _) + fare • turn _ s (star _)
    simp only [keydir,↓reduceIte,map_add,cw_add]; rw [hj.map_add]; simp
  intro x y; change fare • turn _ s (star _) = x • fare • turn _ s (star _)
  simp only [keydir,↓reduceIte,map_smul,cw_smul]; rw [hj.map_smul]; simp only [star_smul,star_star,map_smul]
  exact smul_comm ..

def issue : Packet C d N p where
  weights := E.weights
  chain := reserve hc E
  linear_x m := by
    by_cases hm : m≤N
    · simp_rw [reserve,dif_pos hm]
      have he := arc_x hc E m hm
      constructor
      · intro x y; unfold panel; simp_rw [fun i => (he i).map_add x y,Finset.sum_add_distrib]
      intro c x; unfold panel; simp_rw [fun i => (he i).map_smul c x,← Finset.smul_sum]
    simp_rw [reserve,dif_neg hm]; exact E.linear_x m

variable {S : Finset Cover}

lemma arc_format (hE : E.ComesFrom S) (w : SourceSpace (C.labels.level d)) (m : ℕ) (hr : C.ref d ≤ m) (hm : m≤N)
    (k : Key) : (arc hc E w m hm k).Format 0 C.params (C.path.rep N p m) := by
  have he := hE.format m hr hm (keydir _ k w)
  have hv : (shade k.2 (E.chain m (keydir _ k w))).Format 0 C.params (C.path.rep N p m) := by
    unfold shade; split
    · exact pigment_format he
    exact he
  have hz := paint_format fare (shifted.format (motors hc k m hm) 0 (always_room C m p) hv)
  rw [show affine k.1 (0:Site (C.side m p)) 0 = 0 by simp [affine]] at hz; exact hz

/-- Quantitative upper input propagates with these *specified* prices.
We only need existence of a cap for this exact-encoding check. -/
lemma arc_cap (hE : E.ComesFrom S) (w : SourceSpace (C.labels.level d)) (m : ℕ) (hr : C.ref d ≤ m) (hm : m≤N)
    (k : Key) (v c : ℝ) (he : (E.chain m (keydir _ k w)).remBound 0 (C.path.rep N p m) v c) :
    (arc hc E w m hm k).remBound 0 (C.path.rep N p m) v
      (‖fare‖ * (permission (C.path.rep N p m).p k.1 * c)) := by
  let Q := E.chain m (keydir _ k w)
  have hv := hE.format m hr hm (keydir _ k w)
  let M := shade k.2 Q
  have hu : M.Format 0 C.params (C.path.rep N p m) ∧ M.remBound 0 (C.path.rep N p m) v c := by
    unfold M shade; split
    · exact ⟨pigment_format hv,pigment_cap he⟩
    exact ⟨hv,he⟩
  have hz := paint_cap fare (shifted.cap (motors hc k m hm) hu.1 hu.2)
  rw [show affine k.1 (0:Site (C.side m p)) 0 = 0 by simp [affine]] at hz; exact hz

lemma arc_charge (h : PhysicalAction E.weights) (hE : E.ComesFrom S)
    (w : SourceSpace (C.labels.level d)) (m : ℕ) (hr : C.ref d ≤ m) (hm : m≤N) (k : Key) :
    (arc hc E w m hm k).density 0 (C.localSection d) (C.path.rep N p m) = fare • charge E m w := by
  let F := C.labels.level d
  let v := sw F k.1⁻¹ w
  let B := shade k.2 (E.chain m (keydir F k w))
  have he : B.density 0 (C.localSection d) (C.path.rep N p m) = charge E m v := by
    unfold B keydir shade; split <;> rename_i hq
    · have hz := pigment_density (C.localSection d) (hc.sections d) 0 (Q:=E.chain m (cw F v)) (R:=C.path.rep N p m)
      exact hz.trans ((congr_arg star (charge_star hE h m hr hm v)).trans (star_star _))
    rfl
  have hy := shifted.density (motors hc k m hm (p:=p)) (C.localSection d) (hc.sections d) B 0
  rw [show affine k.1 (0:Site (C.side m p)) 0 = 0 by simp [affine],he,
    ← charge_roll hc hE h m hr hm v k.1, show sw F k.1 v = w by unfold v; rw [← sw_mul, mul_inv_cancel,sw_one]] at hy
  exact (paint_density fare (C.localSection d) 0).trans (congr_arg (fare • ·) hy)

lemma check (h : PhysicalAction E.weights) (hE : E.ComesFrom S) : (issue hc E).ComesFrom S := by
  have hz (m : ℕ) (hm : m ≤ N) (w : SourceSpace (C.labels.level d)) :
      (issue hc E).chain m w = panel dealer (arc hc E w m hm) := dif_pos hm
  let v m := Real.sqrt (C.path.levels.clock.forcedAllowance m)
  have he (w : SourceSpace (C.labels.level d)) (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N)
      (k : Key) : ∃ c, (arc hc E w m hm k).remBound 0 (C.path.rep N p m) (v m) c := by
    obtain ⟨c,hc'⟩ := hE.cap m hr hm (keydir _ k w)
    exact ⟨_,arc_cap hc E hE w m hr hm k (v m) c hc'⟩
  have ht (m : ℕ) (hr : C.ref d ≤ m) (hm : m≤N) (w : SourceSpace (C.labels.level d)) :
      charge (issue hc E) m w = charge E m w := by
    funext U
    unfold charge; rw [hz m hm w, panel_density dealer (C.localSection d) _ (hc.wilson.represents N p m hm).good
      (fun k => ⟨v m, he w m hr hm k⟩)]
    simp_rw [arc_charge hc E h hE w m hr hm]
    rw [Finset.sum_const,nsmul_eq_mul]
    have hv : (Fintype.card Key : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    rw [Pi.smul_apply,smul_eq_mul,fare,Finset.card_univ, ← mul_assoc,mul_inv_cancel₀ hv,one_mul]; rfl
  refine ⟨hE.fit,hE.spatial,hE.fits,hE.coupling,hE.action,hE.coefficients,hE.depends,hE.moves,hE.reads,hE.gauge,
    ?_,?_,?_,?_⟩
  · intro m hr hm w; rw [hz m hm w]; exact panel_format dealer (arc_format hc E hE w m hr hm)
  · intro m hr hm w; rw [hz m hm w]; choose c hh using he w m hr hm; exact ⟨_,panel_cap dealer c hh⟩
  · intro w U; change charge _ _ _ _ = _; rw [ht N hE.fit le_rfl]; exact hE.encode w U
  intro m hr hm w
  -- unnormalized step transported literally for `issue`
  have hx (m) (hr) (hm) : ((issue hc E).chain m w).density 0 (C.localSection d) (C.path.rep N p m) =
        charge E m w := ht m hr hm w
  rw [hx m hr hm.le,hx (m+1) (hr.trans m.le_succ) hm]; exact hE.transfer m hr hm w









end Commission
end YM.ProjectorNext.Equivariance
