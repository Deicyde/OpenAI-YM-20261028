import YM.Push.GRID_APPROXIMATION.Geometry
import YM.Push.GRID_APPROXIMATION.KernelLocal


/-!
# Pass a localized coarse observable against the given history

Not a new history starting at a bare law at the coarse level. Keep N in
all parameters. Prove properties even for iteration ending at intermediate
stations. Real starred copy convention commutes too.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Set Filter MeasureTheory Function Cells
open scoped Topology BigOperators

variable {G : Gauge} (A : History G) (N p : ℕ) {h k m : ℕ}

-- β arg at each step is FINER-level β. Some algebraic lemmas meaningful on
-- padding too; applications will require m ≤ N.

def backTo (q : k ≤ m) (F : Config G (A.S.side k p) → ℂ) : Config G (A.S.side m p) → ℂ :=
  Nat.leRecOn (C:=fun i => Config G (A.S.side i p) → ℂ) q (fun {i} => back (A.levels.clock.op i p) (A.β N p (i+1))) F

def pushTo (q : k ≤ m) : (Config G (A.S.side m p) → ℂ) → Config G (A.S.side k p) → ℂ :=
  Nat.leRecOn (C:=fun i => (Config G (A.S.side i p) → ℂ) → (Config G (A.S.side k p) → ℂ)) q
    (fun {i} F x => F ((A.levels.clock.op i p).push (A.β N p (i+1)) x)) id

@[simp] lemma backTo_self (F : Config G (A.S.side k p) → ℂ) : backTo A N p (show k≤k from le_rfl) F = F := Nat.leRecOn_self _
lemma backTo_next (q : k ≤ m) (F : Config G (A.S.side k p) → ℂ) :
    backTo A N p (Nat.le_succ_of_le q) F = back (A.levels.clock.op m p) (A.β N p (m+1)) (backTo A N p q F) := by
  unfold backTo; rw [Nat.leRecOn_succ q]

@[simp] lemma pushTo_self (F : Config G (A.S.side k p) → ℂ) : pushTo A N p (show k≤k from le_rfl) F = F := by
  unfold pushTo; rw [Nat.leRecOn_self]; rfl
lemma pushTo_next (q : k ≤ m) (F : Config G (A.S.side (m+1) p) → ℂ) :
    pushTo A N p (Nat.le_succ_of_le q) F = pushTo A N p q ((A.levels.clock.op m p).push (A.β N p (m+1)) F) := by
  unfold pushTo; rw [Nat.leRecOn_succ q]

variable {F W : Config G (A.S.side k p) → ℂ}

lemma backTo_env (q : k ≤ m) (he : Envelope F) : Envelope (backTo A N p q F) := by
  induction m, q using Nat.le_induction with
  | base => simpa
  | succ i q ih => rw [backTo_next A N p q]; exact back_env (A.levels.transition_mass ..) ih

lemma backTo_bound (q : k ≤ m) (hm : Measurable F) (C : ℝ) (he : ∀ V, ‖F V‖ ≤ C) :
    ∀ U, ‖backTo A N p q F U‖ ≤ C := by
  induction m, q using Nat.le_induction with
  | base => simpa
  | succ i q ih =>
    rw [backTo_next A N p q]
    exact back_bound (A.levels.transition_mass ..) (backTo_env A N p q (show Envelope F from ⟨hm,C,he⟩)).meas C ih

lemma backTo_const (q : k ≤ m) (z : ℂ) : backTo A N p q (fun _ => z) = (fun _ => z) := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ i q ih => rw [backTo_next A N p q,ih]; exact back_const (A.levels.transition_mass ..) z

lemma backTo_add (q : k ≤ m) (he : Envelope F) (hh : Envelope W) :
    backTo A N p q (F+W)=backTo A N p q F + backTo A N p q W := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih =>
    simp only [backTo_next A N p q,ih]; exact back_add (A.levels.transition_mass ..) (backTo_env A N p q he) (backTo_env A N p q hh)

lemma backTo_star (q : k ≤ m) (he : Envelope F) :
    backTo A N p q (fun V => star (F V)) = fun U => star (backTo A N p q F U) := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih => simp only [backTo_next A N p q,ih]; exact back_star (A.levels.transition_mass ..) (backTo_env A N p q he)

lemma pushTo_integrable (q : k ≤ m) (g : Config G (A.S.side m p) → ℂ)
    (hg : Integrable g (prior G (A.S.side m p))) : Integrable (pushTo A N p q g) (prior G (A.S.side k p)) := by
  induction m, q using Nat.le_induction with
  | base => simpa
  | succ m q ih => rw [pushTo_next A N p q]; exact ih _ (StepData.push_integrable (A.levels.transition_mass ..) _ hg)

lemma pushTo_integral (q : k ≤ m) (g : Config G (A.S.side m p) → ℂ)
    (hg : Integrable g (prior G (A.S.side m p))) :
    (∫ U, pushTo A N p q g U ∂prior G (A.S.side k p)) = ∫ U, g U ∂prior G (A.S.side m p) := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih =>
    have he := A.levels.transition_mass m p (A.β N p (m+1))
    rw [pushTo_next A N p q, ih _ (StepData.push_integrable he _ hg)]
    exact StepData.push_integral he _ hg

/-- Need both integral formula for normalization and adjointness for old/new coefficients. -/
lemma pushTo_dual (q : k ≤ m) (he : Envelope F) (g : Config G (A.S.side m p) → ℂ)
    (hg : Integrable g (prior G (A.S.side m p))) :
    (∫ V, pushTo A N p q g V * F V ∂prior G (A.S.side k p)) =
    ∫ U, g U * backTo A N p q F U ∂prior G (A.S.side m p) := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih =>
    have hx := A.levels.transition_mass m p (A.β N p (m+1))
    rw [pushTo_next A N p q, backTo_next A N p q,ih _ (StepData.push_integrable hx _ hg)]
    exact back_dual hx (backTo_env A N p q he) _ hg



lemma backTo_local (hk : h ≤ k) (q : k ≤ m) (i : Site (A.S.side h p)) (r : ℕ)
    (he : Interior (window (anchor A.S p hk i) r) F) :
    Interior (window (anchor A.S p (hk.trans q) i) (grows A.levels k r q)) (backTo A N p q F) := by
  induction m, q using Nat.le_induction with
  | base => simpa
  | succ m q ih =>
    rw [backTo_next A N p q, grows_next A.levels k r q]
    have hb := A.levels.blocks m p
    have hx := back_cylinder hb.branches ih (A.β N p (m+1)) (hb.gauge _)
    rw [← anchor_next A.S p (hk.trans q)]
    exact hx

lemma backTo_orient (hk : h ≤ k) (q : k ≤ m) (i : Site (A.S.side h p))
    (s : Signed) (he : Envelope F) :
    backTo A N p q (F ∘ pull s (anchor A.S p hk i)) =
      (backTo A N p q F) ∘ pull s (anchor A.S p (hk.trans q) i) := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih =>
    simp only [backTo_next A N p q,ih]; rw [← anchor_next A.S p (hk.trans q)]
    have hx := A.levels.blocks m p
    exact back_natural (A.levels.transition_mass ..) (backTo_env A N p q he) _ _ (prior_pull ..) (fun U V => hx.symmetric _ U V s _)

lemma backTo_copy (hk : h ≤ k) (q : k ≤ m) (i : Site (A.S.side h p)) (he : Envelope F) :
    backTo A N p q ((tilesAt A.S p hk).copy i F) =
      (tilesAt A.S p (hk.trans q)).copy i (backTo A N p q F) := by
  classical
  let s := (tilesAt A.S p hk).omega i
  have hb : (tilesAt A.S p (hk.trans q)).omega i=s := rfl
  let V : Config G (A.S.side k p) → ℂ := F ∘ pull s (anchor A.S p hk i)
  have hv : Envelope V := he.comp_env (continuous_pull ..).measurable
  have hy := backTo_orient A N p hk q i s he
  classical
  unfold Tiling.copy
  rw [hb,tile_translate,tile_translate]
  by_cases hm : (tilesAt A.S p hk).hand i
  · have he' : (tilesAt A.S p (hk.trans q)).hand i := hm
    simp only [hm,he', ↓reduceIte]
    change backTo A N p q (fun U => star (V U)) = _
    rw [backTo_star A N p q hv]
    unfold V; rw [hy]; rfl
  have he' : ¬ (tilesAt A.S p (hk.trans q)).hand i := hm
  simp only [hm,he',↓reduceIte]; exact hy
end YM.Push.GridApprox
