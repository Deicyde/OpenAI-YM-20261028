import YM.Fields.Lo

/-!
# One common recipe from actual spreads to E formula (tokens already quotiented)

Chronological order in all operators. From this library producer ports for
profile Cubs and contour, BEFORE contour; powers from AllCopy. Retains
morphism data used by all tasks. Dynamics sign -I duration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Set Filter MeasureTheory Measure OS OS.Semigroup Mink Spectral Complex Table
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ} {C : Chamber T timeAxis}

/-- abstract matrix input exposing actual centered insertions on THIS
quotient. Need axiomatic map at every NN width (0 unused). -/
structure Small (S : Table L) (C : Chamber T timeAxis) where
  bar (u : ℝ≥0) : S.Union→ₗ[ℂ] C.H.Op

namespace Small
variable (B : Small S C)

def concretized (P : Spread C) := ∀ d v (p : ℝ≥0), 0<p →
    B.bar p (S.pin d v) = P.place (p+p) [(position 0 p,⟨d,S.representative d v⟩)]

def bufferF (p : Space3) : Cross timeAxis := ⟨position p 0, by change YM.time (position p 0) = _; simp⟩

/-- first point of word relative to origin. t=nn width twice typically. -/
def interval (z : ℂ) (t : ℝ≥0) : ℂ := -I*z-duration t

def rip (w : ℂ) (t) (x : Space3) := (C.flow.F (interval w t)).comp (C.flow.U (bufferF x))

lemma down (w : ℂ) (t) : interval w t∈OS.Semigroup.inside ↔ (t:ℝ)<w.im := by
  change 0 < (interval w t).re ↔ _; simp [interval,duration]
lemma flanks (w : ℂ) (t : ℝ≥0) (x : Space3) (v : C.H)
    (h : (t:ℝ)<w.im) : ‖rip (C:=C) w t x v‖ ≤ ‖v‖ := by
  have he := (C.flow.F (interval w t)).le_opNorm (C.flow.U (bufferF x) v)
  rw [C.flow.unitary] at he
  exact he.trans (mul_le_of_le_one_left (norm_nonneg _) (C.flow.norm_row ((down _ _).2 h)))

/-- product recursively of all bars after first. -/
def trainB (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → S.Union) → ℂ → Space3 → C.H
  | 0,_,_,_,_,_ => C.omega
  | n+1,z,x,v,Z,X =>
      rip (z 0-Z) (p+p) (x 0-X) ((B.bar p (v 0)) (trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def matrix (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → S.Union) → ℂ
  | 0,_,_,_ => inner ℂ C.omega C.omega
  | n+1,z,x,v => inner ℂ C.omega (B.bar p (v 0) (B.trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def shot (p : ℝ≥0) : ∀ n, (Fin n → S.Union) → Heights n → Points n → C.H
  | 0,_,_,_ => C.omega
  | n+1,v,y,k => let z := shift k y; let x := trace k
                 rip (z 0) p (x 0) (B.bar p (v 0) (B.trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def enough (y : Heights n) (p : ℝ≥0) := 0<p ∧ p<1 ∧ ∀ i j : Fin n, i < j → 4*(p:ℝ)<y j-y i

def lit (z : Times n) := enough (fun i => (z i).im)

def rated (v : S.Union) := ∃ C : ℝ, ∃ A : ℕ, 0 < C ∧ ∀ p : ℝ≥0, p ∈ Ioo 0 1 →
    ‖B.bar p v‖ ≤ C*(p:ℝ)⁻¹^A

/-- Small local powers + independence means same matrix irrespective any spectator paths. -/
def Defined (F : Waves S) := ∀ n (z : Times n), z ∈ strict n → ∀ p, lit z p →
    ∀ x v, F.F n z x v=B.matrix p n z x v

def ample (p : ℝ≥0) (y : Heights n) := enough y p ∧ ∀ i : Fin n,4*(p:ℝ)<y i

def profile (t : ℝ) (n : ℕ) : Heights n := fun i => (i.val+1:ℝ)*t

lemma imminent {t : ℝ} (h : 0<t) : profile t n∈positiveHeight n := by
  constructor
  · intro i j hp; change _*t < _*t; gcongr; exact hp
  change ∀ i : Fin n,_*t>0; intro i; positivity

def logD (t : ℝ) : ℝ≥0 := (min t 1/8).toNNReal
lemma suitable {t : ℝ} (h : 0<t) : ample (logD t) (profile t n) := by
  have he : logD t∈Ioo (0:ℝ≥0) 1 := by
    have hv : 0< min t 1:=lt_min h zero_lt_one
    refine ⟨Real.toNNReal_pos.mpr (by positivity),Real.toNNReal_lt_one.mpr ?_⟩
    linarith [min_le_right t (1:ℝ)]
  have ht : ↑(logD t)≤ t/8 := by
    unfold logD; rw [Real.coe_toNNReal _ ((Real.toNNReal_pos.mp he.1).le)]
    gcongr; exact min_le_left ..
  refine ⟨⟨he.1,he.2,?_⟩,?_⟩
  · intro i j hk; have hh : (i.val:ℝ)+1≤ (j.val:ℝ) := by exact_mod_cast hk
    unfold profile; linarith [mul_le_mul_of_nonneg_right hh h.le]
  intro i; unfold profile; linarith [mul_nonneg (Nat.cast_nonneg i.val) h.le]

def heatCup (b : Sentence S) (t : ℝ) := ∫ x,(Joint.materialize b.length (fun i => (b.get i).2) x) •
    B.shot (logD t) b.length (fun i => (b.get i).1) (profile t b.length) x

/-- star coupler tying both B and independent corner W. No arbitrary Cups. -/
structure Lamp (W : Surface S) (J : StarOp S) (K : Spins S) : Prop where
  legit (b : Sentence S) (t : ℝ) (h : 0<t) : Integrable (fun x =>
    (Joint.materialize b.length (fun i => (b.get i).2) x) • B.shot (logD t) _ (fun i => (b.get i).1) (profile t b.length) x)
  here (v w) : Tendsto (fun p : ℝ×ℝ => inner ℂ (B.heatCup v p.1) (B.heatCup w p.2)) (till ×ˢ till) (𝓝 (W.kernel J v w))
  time (v b) (k : ℝ) (h : 0<k) : B.heatCup (K.po (Poincare.translation b) v) k = C.flow.unit.translation b (B.heatCup v k)
@[simp] lemma omega (t : ℝ) : B.heatCup [] t=C.omega := by
  unfold heatCup
  simp only [List.length_nil,Points.volume_nil]; rw [integral_dirac]
  change Joint.trivial _ • _=_; rw [Joint.trivial_at,one_smul];rfl

def bowls {W J K} (h : B.Lamp W J K) : Cups W J K C where
  hot := B.heatCup
  here := h.here
  omega := by rw [show B.heatCup []=(fun _ => C.omega) from funext B.omega]; exact tendsto_const_nhds
  time v b := Eventually.mono self_mem_nhdsWithin fun i hi => h.time v b i hi

end Small
end YM.Boundary
