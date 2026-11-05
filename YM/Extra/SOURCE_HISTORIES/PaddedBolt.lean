import YM.Extra.SOURCE_HISTORIES.Pads

/-!
# How the planner can insist on the top shelf at no vacuum cap loss

Pad through **whole** Recipe & supplied Bolt, not just one R at use time.
Still conditional; the selected Bolt after this enrichment must be used
at all downstream appointments, & local step hypotheses requested there
(with this full alphabet). Curves pull/push explicitly. All levels retain
actual vacuum and genealogy, embeddings of old addresses always the same,
no perturbation of coefficients, supports or predicates. Does NOT upgrade
already-produced multi-source estimates on an old unpadded history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Pads
open Lattice Wilson RG Shoot Supply Input Precision Function Filter Set MeasureTheory Bid Labels Motion Org
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

def fromNew (A : Activities G n) := {A with forced:=A.forced ∘ old n,K:=A.K ∘ old n}
def legacy (R : Rep G n) := {R with activities:=fromNew R.activities}

lemma vanished (A : Activities G n) : fromNew (enhanced A)=A := by
  obtain ⟨a,b,c,d⟩ := A
  unfold fromNew enhanced
  simp only [show ∀ (f : ℕ → ForcedAddress G n) g, joins n f g ∘ old n=f from fun f g => funext fun j => joins_old f g j,
    show ∀ (f : ℕ → Config G n → ℝ) g, joins n f g ∘ old n=f from fun f g => funext fun j => joins_old f g j]

lemma recorded (R : Rep G n) : legacy (bulk R) = R := by unfold bulk legacy; rw [vanished]

lemma revert (A B : Activities G n) (P : BudgetPoint) {w : ℝ} (h : deviation P A B w) :
    deviation P (fromNew A) (fromNew B) w := by
  obtain ⟨a,b,ha,hb,hc,hD⟩ := h
  refine ⟨a,b ∘ old n,ha,fun i => hb _,hc,?_⟩
  let f := fun i => P.mass (A.forced i).support (b i)
  change SumBudget (f ∘ old n) w
  exact ⟨fun i => hD.1 _, hD.2.1.comp_injective (old n).injective,
    (tsum_comp_le_tsum_of_inj hD.2.1 hD.1 (old n).injective).trans hD.2.2⟩

lemma dev (A B : Activities G n) (P : BudgetPoint) {w : ℝ} (h : deviation P A B w) :
    deviation P (enhanced A) (enhanced B) w := by
  obtain ⟨a,b,ha,hb,hc,hD⟩ := h
  let u := joins n b (fun _ => 0)
  refine ⟨a,u,ha,fun i => ?_,hc,?_⟩
  · obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · unfold u; rw [joins_old,old_k,old_k]; exact hb j
    simp [u,joins_stock,ghost_k]
  let f := fun i => P.mass (A.forced i).support (b i)
  rw [show (fun i => P.mass ((enhanced A).forced i).support (u i)) = joins n f (fun _ => 0) from by
    funext i; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · unfold u; rw [joins_old,old_eq,joins_old]
    simp [u,joins_stock,BudgetPoint.mass]]
  exact budget_joins hD n

lemma inherits {P : BudgetPoint} {f : ℝ → Rep G n} {Y} (he : Curve P f Y) : Curve P (legacy ∘ f) Y := by
  refine ⟨he.beta,he.v,he.reg,fun i hi j hj => ?_,fun ε hε x hx => ?_⟩
  · change (f i).activities.forced ∘ old n = (f j).activities.forced ∘ old n; rw [he.forced i hi j hj]
  exact (he.continuous ε hε x hx).mono fun i hi => revert _ _ _ hi

lemma rebrands {P : BudgetPoint} {f : ℝ → Rep G n} {Y} (he : Curve P f Y) : Curve P (bulk ∘ f) Y := by
  refine ⟨he.beta,he.v,he.reg,fun i hi j hj => ?_,fun ε hε x hx => ?_⟩
  · change joins n (f i).activities.forced apparition = joins n (f j).activities.forced apparition
    rw [he.forced i hi j hj]
  exact (he.continuous ε hε x hx).mono fun i hi => dev _ _ _ hi

variable {a : Levels G}

def design (R : Recipe a) : Recipe a := {R with
    retain n m p v := v=bulk (legacy v) ∧ Lives R n m p (legacy v)
    first n p v := R.first n p (legacy v)
    next n m p v w := R.next n m p (legacy v) (legacy w)}

lemma alive {R : Recipe a} {n m p v} (h : Lives R n m p v) : Lives (design R) n m p (bulk v) := by
  refine ⟨h.path,h.point,h.clip,bulky v h.valid,?_⟩
  unfold design; simp only [recorded]; exact ⟨trivial,h⟩
lemma rise {R : Recipe a} {n p v} (h : R.Starter n p v) : (design R).Starter n p (bulk v) :=
  ⟨h.scalars, (charged _).trans h.raw,by simp only [design,recorded]; exact h.inits⟩

variable {M : Metals G} {D : Rolls M.p} (A : Alloy M D)

/-- New Alloy retains actual tests via design, on the old Wilson representation
embedded. -/
def device : Alloy M D := {A with B:={A.B with bake:=design A.B.bake} }

lemma moveUp {n m p v w} (h : A.B.Move n m p v w) :
    (device A).B.Move n m p (bulk v) (bulk w) := by
  refine ⟨?_,?_,alive h.bundle,zeros v.activities v.p _ h.forced, h.δ⟩
  · rw [charged,charged]; exact h.ident
  change A.B.bake.next _ _ _ (legacy (bulk v)) (legacy (bulk w)); rw [recorded,recorded]; exact h.step

lemma prolong (h : A.B.Program) : (device A).B.Program := by
  constructor
  · intro N p
    obtain ⟨F,hF,he⟩ := h.begins N p
    exact ⟨bulk ∘ F,rebrands hF, fun i hi =>
      ⟨(he i hi).1,alive (he i hi).2.1,rise (he i hi).2.2⟩⟩
  intro N p m hm l u hl Q hw hh
  have he (i : ℝ) (hi : i ∈ Icc l u) : Lives A.B.bake N (m+1) p (legacy (Q i)) := ((hh i hi).1.loads).2
  obtain ⟨T,hT,hV⟩ := h.advances N p m hm l u hl (legacy ∘ Q) (inherits hw)
     (fun i hi => ⟨he i hi, (hh i hi).2⟩)
  refine ⟨bulk ∘ T,rebrands hT,fun i hi => ?_⟩
  rw [show Q i=bulk (legacy (Q i)) from ((hh i hi).1.loads).1]; exact moveUp _ (hV i hi)

lemma enriched (Y : History G) (h : Y.Selected) : ({Y with rep:=fun i j k => bulk (Y.rep i j k)} : History G).Selected := by
  constructor
  · exact h.path_shared
  · intro i j k ht
    have hx := h.represents i j k ht
    exact ⟨hx.vac,hx.clip,bulky _ hx.good,hx.band⟩
  · intro i p; exact ⟨(h.starts i p).1,(charged _).trans (h.starts i p).2⟩
  · intro i p m hi; refine ⟨?_, (h.steps i p m hi).2⟩
    change (bulk (Y.rep i p m)).eval = _
    simp_rw [charged]; exact (h.steps i p m hi).1
  · exact h.reaches
  exact h.running

def jolt (Y : Bolt A) : Bolt (device A) := by
  let X N p m := bulk (Y.history N p m)
  refine ⟨prolong A Y.program, X,fun n p => ?_, enriched _ Y.choice,fun i p n hi => moveUp A (Y.moves i p n hi)⟩
  have he := Y.sticks n p
  exact ⟨fun i hi hI => ⟨alive (he.prices i hi hI).1,(he.prices i hi hI).2⟩, rise he.fromTop,
    fun i hi hI => (device A).B.links hI (moveUp A (Y.moves n i p hI))⟩


end YM.Extra.Histories.Pads
