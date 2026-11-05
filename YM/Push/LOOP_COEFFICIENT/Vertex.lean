import YM.Push.LOOP_COEFFICIENT.Frequency
import YM.Push.LOOP_COEFFICIENT.JetMatrix
import YM.Push.LOOP_COEFFICIENT.Routed


/-!
# Routed derivative vertices (period-independent symbols and exact finite uses)

No smoothness/closure at complex p assumed by the definitions. The two
external slots are arbitrary independently (polarized precision). All complex
readouts have their positions extended without any adjoint of the inserted
waves at complex momentum. `transpose` is the vertex for the real-position
matrix transpose, so exchanges and negates both internal routed momenta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators

structure Vertex (d a b : Type) where
  base (q : Momentum) : Matrix a b ℂ
  one (q p : Momentum) : CSpace d →ₗ[ℂ] Matrix a b ℂ
  two (q p p' : Momentum) : CSpace d →ₗ[ℂ] CSpace d →ₗ[ℂ] Matrix a b ℂ

variable {s : Side} {E F H J a b c d : Type}
    [Fintype E] [Fintype F] [Fintype H] [Fintype J] [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq E] [DecidableEq F] [DecidableEq H] [DecidableEq J] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

namespace Vertex

def const (M : Momentum → Matrix a b ℂ) : Vertex d a b := ⟨M,fun _ _ => 0,fun _ _ _ => 0⟩
def inc (V : Vertex d a b) : Vertex d a b := ⟨0,V.one,V.two⟩
def firstOrder (V : Vertex d a b) : Vertex d a b := ⟨0,V.one,fun _ _ _ => 0⟩
def add (V V' : Vertex d a b) : Vertex d a b := ⟨V.base + V'.base,V.one + V'.one,V.two + V'.two⟩
def smul (r : ℂ) (V : Vertex d a b) : Vertex d a b := ⟨r • V.base,r • V.one,r • V.two⟩
def neg (V : Vertex d a b) : Vertex d a b := ⟨-V.base,-V.one,-V.two⟩

def mul (V : Vertex d a b) (W : Vertex d b c) : Vertex d a c :=
  let L := matrixMulLinear a b c ℂ
  { base q := V.base q * W.base q
    one q p := (L (V.base (q+p))).comp (W.one q p) + (L.flip (W.base q)).comp (V.one q p)
    two q p s := (W.two q p s).compr₂ (L (V.base (q+p+s))) + L.compl₁₂ (V.one (q+s) p) (W.one q s) +
      (L.compl₁₂ (V.one (q+p) s) (W.one q p)).flip + (V.two q p s).compr₂ (L.flip (W.base q)) }

def inv (V : Vertex d a a) : Vertex d a a :=
  let C := const (fun q => (V.base q)⁻¹)
  let H := V.inc
  C.add (((C.neg.mul H).mul C).add ((((C.mul H).mul C).mul H).mul C))

def transpose (V : Vertex d a b) : Vertex d b a :=
  let L := (Matrix.transposeLinearEquiv a b ℂ ℂ).toLinearMap
  { base q := (V.base (-q)).transpose
    one q p := L.comp (V.one (-(q+p)) p)
    two q p s := (V.two (-(q+p+s)) p s).compr₂ L }
end Vertex

/-- A finite jet agrees literally with the vertices on this mesh. First grid
is for the external fields. The M and N grids are for the output and input
of the internal operators. No bounds here! -/
structure Synced (A : Grid s J d) (M : Grid s E a) (N : Grid s F b) (X : Jet J (Matrix E F ℂ)) (V : Vertex d a b) : Prop where
  base {q k} : Matches q k → Routed M N k k X.base (V.base q)
  one {q p k i} : Matches q k → Matches p i → ∀ v, Routed M N (k+i) k (X.lin (plane A i *ᵥ v)) (V.one q p v)
  two {q p p' k i j} : Matches q k → Matches p i → Matches p' j → ∀ v w, Routed M N (k+i+j) k
    (X.quad (plane A i *ᵥ v) (plane A j *ᵥ w)) (V.two q p p' v w)

open Vertex
namespace Synced
variable {A : Grid s J d} {M : Grid s E a} {N : Grid s F b} {K : Grid s H c}
  {X Y : Jet J (Matrix E F ℂ)} {V W : Vertex d a b}

omit [Fintype E] [Fintype J] [Fintype b] [DecidableEq E] [DecidableEq F] [DecidableEq J] in
lemma const {x : Matrix E F ℂ} {y} (h : ∀ k q, Matches q k → Routed M N k k x (y q)) :
    Synced A M N (Jet.const x) (Vertex.const y) := ⟨fun h₁ => h _ _ h₁,fun _ _ _ => Routed.zero,fun _ _ _ _ _ => Routed.zero⟩

omit [Fintype E] [Fintype J] [Fintype b] [DecidableEq E] [DecidableEq F] [DecidableEq J] in
lemma inc (h : Synced A M N X V) : Synced A M N { X with base := 0 } V.inc := ⟨fun _ => Routed.zero, h.one,h.two⟩

omit [Fintype E] [Fintype J] [Fintype b] [DecidableEq E] [DecidableEq F] [DecidableEq J] in
lemma add (hx : Synced A M N X V) (hy : Synced A M N Y W) : Synced A M N (X.add Y) (V.add W) :=
  ⟨fun h => (hx.base h).add (hy.base h),fun h h' v => (hx.one h h' v).add (hy.one h h' v),
    fun h h' h'' v w => (hx.two h h' h'' v w).add (hy.two h h' h'' v w)⟩

omit [Fintype E] [Fintype J] [Fintype b] [DecidableEq E] [DecidableEq F] [DecidableEq J] in
lemma smul (hx : Synced A M N X V) (t : ℂ) : Synced A M N (X.push (LinearMap.lsmul ℂ _ t)) (V.smul t) :=
  ⟨fun h => (hx.base h).smul t,fun h h' v => (hx.one h h' v).smul t, fun h h' h'' v w => (hx.two h h' h'' v w).smul t⟩

omit [Fintype E] [Fintype J] [Fintype b] [DecidableEq E] [DecidableEq F] [DecidableEq J] in
lemma neg (hx : Synced A M N X V) : Synced A M N (X.push (-LinearMap.id)) V.neg :=
  ⟨fun h => (hx.base h).neg,fun h h' v => (hx.one h h' v).neg,fun h h' h'' v w => (hx.two h h' h'' v w).neg⟩

omit [Fintype E] [Fintype J] [Fintype c] [DecidableEq E] [DecidableEq F] [DecidableEq J] [DecidableEq H] in
lemma mul (h : Synced A M N X V) {Y W} (h' : Synced A N K Y W) :
    Synced A M K (Jet.bilin (matrixMulLinear E F H ℂ) X Y) (V.mul W) := by
  refine ⟨fun hq => (h.base hq).mul (h'.base hq),fun hq hp v => ((h.base (hq.add hp)).mul (h'.one hq hp v)).add
    ((h.one hq hp v).mul (h'.base hq)),fun hq hi hj v w => ?_⟩
  refine ((((h.base ((hq.add hi).add hj)).mul (h'.two hq hi hj v w)).add ?_).add
    ((h.one (hq.add hi) hj w).mul (h'.one hq hi v))).add ((h.two hq hi hj v w).mul (h'.base hq))
  rename_i q p p' k i j
  rw [add_right_comm k]; exact (h.one (hq.add hj) hi v).mul (h'.one hq hj w)

omit [Fintype J] [DecidableEq J] in
lemma inv {X V} (hx : Synced A M M X V) (h : IsUnit X.base) (hv : ∀ q i, Matches (n:=s) q i → IsUnit (V.base q)) :
    Synced A M M X.reciprocal V.inv := by
  have hc : Synced A M M (Jet.const X.base⁻¹) (Vertex.const fun q => (V.base q)⁻¹) := Synced.const (fun i q hq => (hx.base hq).inv h (hv q i hq))
  exact hc.add (((hc.neg.mul hx.inc).mul hc).add ((((hc.mul hx.inc).mul hc).mul hx.inc).mul hc))

omit [DecidableEq E] in
lemma routed_transpose {M N} {X : Matrix E F ℂ} {p k : Site s} {W : Matrix a b ℂ}
    (h : ∀ k, ∃ W, Routed M N (k+p) k X W) (hw : Routed M N (-(k+p)+p) (-(k+p)) X W) :
    Routed N M (k+p) k X.transpose W.transpose := by
  choose f hf using h
  let g i := if i=-(k+p) then W else f i
  have he i : Routed M N (i+p) i X (g i) := by unfold g; split <;> simp_all
  simpa only [g, if_true] using Routed.transpose he k

omit [Fintype J] [DecidableEq E] [DecidableEq J] in
lemma transpose (hx : Synced A M N X V) : Synced A N M
    (X.push (Matrix.transposeLinearEquiv E F ℂ ℂ).toLinearMap) V.transpose := by
  constructor
  · intro q k hq
    have he (k) : ∃ W : Matrix a b ℂ, Routed M N (k+(0:Site s)) k X.base W := ⟨_,by rw [add_zero]; exact hx.base (mon_matches k)⟩
    simpa [Vertex.transpose] using! routed_transpose (k:=k) he (by simpa only [add_zero] using hx.base hq.neg)
  · intro q p k i hq hp v
    have he := hx.one ((hq.add hp).neg) hp v
    refine routed_transpose (fun j => ⟨_,hx.one (mon_matches j) hp v⟩) he
  intro q p p' k i j hq hi hj v w
  have hh k : ∃ W, Routed M N (k+(i+j)) k (X.quad (plane A i *ᵥ v) (plane A j *ᵥ w)) W := ⟨_, by rw [← add_assoc]; exact hx.two (mon_matches k) hi hj v w⟩
  have he := hx.two (((hq.add hi).add hj).neg) hi hj v w
  rw [add_assoc, add_assoc k i] at he
  rw [add_assoc]; exact routed_transpose hh he
end Synced
end YM.Push.Loops
