import YM.Distribution.Product
import YM.Euclid.Union

/-!
# Strict times and joint tempered boundary

Time last *real* axis of `Points`; ordered imaginary heights.
Convergence against every joint test and slope, not just tensor products.
Real positions all, n=0 included. For ease of gluing keep both W and
complex continuations defined multilinearly on Union (circuits can use any
finite levels, see P.joint). Conf nonempty positions at slice by monotonicity.
Do not demand smoothness of point W. Need actual Integrable statements; no
negative epsilon used. Partial-shift convergence in stronger libraries later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open MeasureTheory Filter Function Set Complex
open scoped Topology BigOperators ContDiff

abbrev Heights (n : ℕ) := Fin n → ℝ
abbrev Times (n : ℕ) := Fin n → ℂ
abbrev SpacePoints (n : ℕ) := Fin n → Space3

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

def east (n : ℕ) := {y : Heights n | StrictMono y}
def strict (n : ℕ) := {z : Times n | (fun i => (z i).im) ∈ east n}
def positiveHeight (n : ℕ) := {y : Heights n | y ∈ east n ∧ ∀ i, 0 < y i}

lemma open_east (n) : IsOpen (east n) := by
  classical
  have he : east n = ⋂ (i : Fin n) (j : Fin n) (_ : i<j), {y : Heights n | y i < y j} := by ext1; simp [east,StrictMono]
  rw [he]; exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply _) (continuous_apply _)

lemma open_strict (n) : IsOpen (strict n) := (open_east n).preimage
  (show Continuous (fun z : Times n => fun i => (z i).im) from by fun_prop)

/-- Physical-to-complex-time convention. -/
def shift (p : Points n) (h : Heights n) : Times n := fun i => ↑(time (p i))+↑(h i)*I

def trace (p : Points n) : SpacePoints n := fun i => spatial (p i)

def place (x : SpacePoints n) (y : Heights n) : Points n := points fun i => position (x i) (y i)

lemma clear {y : Heights n} (h : y ∈ east n) (x : SpacePoints n) : place x y ∈ conf n := by
  intro i j hij; apply h.injective
  have he := congr_arg time hij; simpa [place] using he

lemma on_profile (x : Points n) (u : Heights n) (ε : ℝ) (ht : 0<ε) (h : u ∈ east n) :
    shift x (ε • u) ∈ strict n := by
  intro i j hij; simp [shift, mul_lt_mul_iff_of_pos_left ht, h hij]

structure Surface (S : Table L) where
  W (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => S.Union) (Distn (Points n))

structure Waves (S : Table L) where
  F (n : ℕ) : Times n → SpacePoints n → MultilinearMap ℂ (fun _ : Fin n => S.Union) ℂ

namespace Waves
variable (P : Waves S)

def restricted (v : Fin n → S.Union) (y : Heights n) (p : Points n) := P.F n (shift p y) (trace p) v

def atSlopes (v : Fin n → S.Union) (h : Heights n) (ε : ℝ) (f : Joint n) :=
    ∫ x, P.restricted v (ε • h) x * f x

/-- E item strict contour, simultaneous coupling to T = S or alpha,
slots **from the same original quotient**. Need T.respects S in use.
-/
structure Region (T : Table L) : Prop where
  together (n : ℕ) (v : Fin n → S.Union) : ContinuousOn (fun p : Times n × SpacePoints n =>
    P.F n p.1 p.2 v) (strict n ×ˢ univ)
  hol (n : ℕ) (v : Fin n → S.Union) (x : SpacePoints n) :
    DifferentiableOn ℂ (fun z => P.F n z x v) (strict n)
  roots (n : ℕ) (v : Fin n → S.Tag) (x : SpacePoints n) (y : Heights n) (hy : y ∈ east n) :
    P.F n (fun i => ↑(y i)*I) x (fun i => S.pin (v i).1 (v i).2) = S.useAt T (place x y) v

lemma root_raw {T : Table L} (hp : T.Symmetric) (ht : T.respects S) (h : P.Region T)
    (v : Fin n → L.Token) (x : Points n) (hx : StrictMono (fun i => time (x i))) :
    P.F n (fun i => ↑(time (x i))*I) (trace x) (fun i => S.pin (v i).1 (S.project _ (v i).2))=T.read x v := by
  let y (i : Fin n) := time (x i)
  have he : place (trace x) y=x := by ext1; simp [trace,y,place]
  have hh := h.roots n (S.classTokens ∘ v) (trace x) y hx
  rwa [S.at_project T hp ht (clear hx _), he] at hh

/-- s-order, Lebesgue dt d³ x in `Points.volume_product,volume_divide`.
One limit positive profile `u` for every test, each *ordered* u. -/
structure Opens (F : Surface S) : Prop where
  int (n : ℕ) (v : Fin n → S.Union) (y : Heights n) (h : y ∈ east n) (f : Joint n) :
    Integrable (fun x => P.restricted v y x * f x)
  profile (n : ℕ) (v : Fin n → S.Union) (y : Heights n) (hy : y ∈ east n) (f : Joint n) :
    Tendsto (fun ε => atSlopes P v y ε f) (𝓝[>] (0:ℝ)) (𝓝 (F.W n v f))

/-- Stronger all-ordered-heights form, useful for Gram limits. -/
structure NonTangentialFree (F : Surface S) : Prop where
  int (n : ℕ) (v : Fin n → S.Union) (y : Heights n) (h : y ∈ east n) (f : Joint n) :
    Integrable (fun x => P.restricted v y x * f x)
  corner (n : ℕ) (v : Fin n → S.Union) (f : Joint n) :
    Tendsto (fun u => ∫ x, P.restricted v u x*f x) (𝓝[east n] (0:Heights n)) (𝓝 (F.W n v f))

lemma exposed (F : Surface S) (h : P.NonTangentialFree F) : P.Opens F := by
  refine ⟨h.int,fun i v y hy f => ?_⟩
  have he : Tendsto (fun ε : ℝ => ε • y) (𝓝[>] (0:ℝ)) (𝓝[east i] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · have hc := (continuous_id.smul (continuous_const (y := y))).continuousAt (x := (0:ℝ)) |>.tendsto
      change Tendsto (fun x : ℝ => x • y) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) • y)) at hc
      rw [show (0:ℝ) • y=0 from zero_smul ..] at hc; exact hc.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun a b hb => mul_lt_mul_of_pos_left (hy hb) (show 0 < x from hx)
  exact (h.corner i v f).comp he
end Waves

structure Contour (S : Table L) where
  waves : Waves S
  world : Surface S

structure Contour.From (C : Contour S) (T : Table L) : Prop where
  heat : C.waves.Region T
  emerges : C.waves.Opens C.world

end YM.Boundary
