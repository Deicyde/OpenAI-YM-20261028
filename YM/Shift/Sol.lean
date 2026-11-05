import YM.Shift.Closing


/-!
# Damping, supports, full tube ports

Use explicit cutoff, inverse constant `pref`, abs Points. Do not equate
arbitrary cutoff multipliers (need off-support proof). Shift/shores surfaces
are linear distributions. One direction to prove half via Air and superheight
tests. Values port (integrability also at ALL ordered Y scalar) to recover
nonloss.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Filter Set Function Distribution Probe MeasureTheory Mink Complex
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators ContDiff
variable {n : ℕ}

def lifts (p : Points n) (f : Joint n) (h : HasCompactSupport ⇑f) : Joint n :=
    let k := fun x => Complex.exp (inner ℝ p x)*f x
    have hk : ContDiff ℝ ∞ k := ((Complex.ofRealCLM.contDiff.comp (innerSL ℝ p).contDiff).cexp).mul (f.smooth ⊤)
    have hh : HasCompactSupport k := h.mul_left
    hh.toSchwartzMap hk
@[simp] lemma rises (p : Points n) (f : Joint n) (h : HasCompactSupport ⇑f) :
    ∀ x, lifts p f h x= Complex.exp (inner ℝ p x)*f x := fun _ => rfl
lemma remains (p : Points n) (f : Joint n) (h : HasCompactSupport ⇑f) : HasCompactSupport (lifts p f h : Points n → ℂ) := by
  apply HasCompactSupport.mul_left h

abbrev Full (n : ℕ) := EuclideanSpace ℂ (Fin n × Axis)

def reality (x : Full n) := Points.flatten.symm ((WithLp.toLp 2 fun i => (x i).re) : EuclideanSpace ℝ _)
def shade (x : Full n) := Points.flatten.symm ((WithLp.toLp 2 fun i => (x i).im) : EuclideanSpace ℝ _)
def glow (x y : Points n) : Full n := WithLp.toLp 2 fun i => ↑(Points.flatten x i)+ ↑(Points.flatten y i)*I
lemma valley (p : Full n) : glow (reality p) (shade p)=p := by ext1 i; simp [reality,shade,glow]
@[simp] lemma re_glow (x y : Points n) : reality (glow x y)=x := by
  apply Points.flatten.injective; ext i; simp [reality,glow]
@[simp] lemma im_glow (x y : Points n) : shade (glow x y)=y := by
  apply Points.flatten.injective; ext i; simp [shade,glow]

@[fun_prop] lemma cont_sh (n) : Continuous (@shade n) := by unfold shade;fun_prop
@[fun_prop] lemma cont_Re (n) : Continuous (@reality n) := by unfold reality;fun_prop
lemma home (n) : Continuous (fun p : Points n × Points n => glow p.1 p.2) := by unfold glow;fun_prop

def tube (n : ℕ) := shade ⁻¹' fields n
def edge (n : ℕ) := shade ⁻¹' shores n
lemma south (n : ℕ) : IsOpen (tube n) := (smooth_fields _).preimage (cont_sh n)
lemma warmer (n) : fields n ⊆ shores n := by
  intro i hp; simp only [fields,shores,Set.mem_iInter,Set.mem_setOf,inside,cone] at hp ⊢
  intro j k ht; exact (hp j k ht).le
lemma total_south (n : ℕ) : tube n ⊆ edge n := preimage_mono (warmer n)
@[simp] lemma flat (n) : (0:Points n) ∈ shores n := by
  simp [shores,cone]

/-- Coordinates fed holomorphic functions. Hol includes all spectator
arguments; no treating common variable by quotient. Use all pairs proper
for W. -/
def ShadeSet (r : ℝ) (n : ℕ) : Set (Points n) := {x | ∃ z∈coneM n, dist x z < r}

structure Blanket (n : ℕ) where
  cut : Points n → ℝ
  uses : HasTemperateGrowth cut
  immediate : ∀ i ∈ ShadeSet 1 n, cut i=1
  supported : tsupport cut ⊆ ShadeSet 3 n

namespace Blanket
variable (B : Blanket n)
def attenuate (y x : Points n) := Complex.exp (-inner ℝ y x) * (B.cut x : ℂ)
def diffuser (y : Points n) := (SchwartzMap.smulLeftCLM ℂ (B.attenuate y) : Joint n →L[ℂ] Joint n)
structure Modified : Prop where
  actual : ∀ y ∈ shores n, HasTemperateGrowth (B.attenuate y)
  seen (f : Joint n) : ContinuousOn (fun y => B.diffuser y f) (shores n)

/-- value probe at interior uses IQ constants next. -/
def lens (p : Full n) (x : Points n) := plane x (reality p) * B.attenuate (shade p) x

/-- closed partial dumps respecting attenuation -/
def partialD (u : Distn (Points n)) (y : Points n) : Distn (Points n) :=
    let v := (Distn.fourier u).comp (B.diffuser y)
    Distn.inverse v

theorem tends (h : B.Modified) (u : Distn (Points n)) (f : Joint n) : ContinuousOn (fun y => B.partialD u y f) (shores n) :=
    (Distn.fourier u).continuous.comp_continuousOn (h.seen (Probe.port f))

theorem flatD (h : B.Modified) {u : Distn (Points n)} (hp : dsupport (Distn.fourier u) ⊆ coneM n) : B.partialD u 0=u := by
  suffices he : ((Distn.fourier u).comp (B.diffuser 0))= Distn.fourier u by rw [partialD]; simp [he]
  ext1 f
  change Distn.fourier u (B.diffuser 0 f)=_
  apply sub_eq_zero.mp; rw [← map_sub]
  apply (Distn.due _ _ (closedM _)).1 hp
  intro p ht hs
  have HH : Disjoint (Metric.ball p 1) (Function.support (B.diffuser 0 f-f)) := Set.disjoint_left.mpr (fun x hx hX => ?_)
  · exact Set.disjoint_left.1 (HH.closure_right Metric.isOpen_ball) (Metric.mem_ball_self zero_lt_one) ht
  apply hX
  have hg : B.cut x=1 := B.immediate x ⟨p,hs,hx⟩
  change B.diffuser 0 f x-f x=0; simp [diffuser, SchwartzMap.smulLeftCLM_apply_apply (h.actual _ (flat _)),attenuate,hg]
end Blanket
variable {G : Gauge} {L : Register G} {S : Table L}
namespace Waves
/-- eq:oscfft on compact tests only. -/
def during (F : Waves S) (W : Surface S) := ∀ (n : ℕ) (v : Fin n → S.Union) (y : Heights n), y∈east n→ ∀ f : Joint n, ∀ h : HasCompactSupport ⇑f,
    Distn.fourier (W.W n v) f=F.psi v y (Probe.hat (lifts (dawn y) f h))
end Waves
namespace Surface

def cone_tests (W : Surface S) := ∀ n (v : Fin n → S.Union), dsupport (Distn.fourier (W.W n v)) ⊆ half n

/-- observed emission of analytic space-time contours. Inherits stars later. -/
structure Aurora (W : Surface S) (D : ∀ i : ℕ, Blanket i) where
  lens (n : ℕ) (p : Full n) : Joint n
  shape (n : ℕ) (p : Full n) (h : p∈tube n) : ∀ x, lens n p x = (D n).lens p x

namespace Aurora
variable {W : Surface S} {D : ∀ i : ℕ, Blanket i} (X : Aurora W D)

def emit (v : Fin n → S.Union) (p : Full n) := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier (W.W n v) (X.lens n p)

structure FullBody (F : Waves S) : Prop where
  hol (n : ℕ) (v : Fin n → S.Union) : AnalyticOnNhd ℂ (X.emit v) (tube n)
  builds (n : ℕ) (v : Fin n → S.Union) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    (D n).partialD (W.W n v) y f= ∫ x,X.emit v (glow x y) * f x
  leaned (n : ℕ) (v : Fin n → S.Union) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    Integrable (fun x => X.emit v (glow x y) * f x)
  pure (n : ℕ) (v : Fin n → S.Union) (x : Points n) (y : Heights n) (hp : y∈east n) : X.emit v (glow x (dawn y)) = F.restricted v y x

lemma sees {F : Waves S} (h : X.FullBody F) (v : Fin n → S.Union) (y : Points n) (p : y∈shores n) (hm : (D n).Modified) (f : Joint n) :
    Tendsto (fun z => ∫ x, X.emit v (glow x z)*f x) (𝓝[fields n] y) (𝓝 ((D n).partialD (W.W n v) y f)) :=
    (((D n).tends hm _ f y p).mono (warmer n)).congr' (Eventually.mono self_mem_nhdsWithin fun _ hz => h.builds n _ _ hz _)

lemma lower {F : Waves S} (h : X.FullBody F) (v : Fin n → S.Union) (y : Heights n) (x : Points n) (hp : y∈east n) :
    W.W n v =0 → F.restricted v y x=0 := by
  intro ht
  rw [← h.pure n v x y hp,emit,Distn.fourier_at,ht]; simp
end Aurora
end Surface
end YM.Boundary
