import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Critical


/-!
# Run the complex symbol contractions at real wave momenta

Explicit volumes and entry prices. `SceneLedger` permits the same σ,M
for all (take widest cap / narrowest common strip after earning them). Input `Published` is genuine Laurent periodization and strip support, independent
of ANY specified waves/external amplitudes. Producer later. This theorem watches only fixed-L
(except insofar as payments for slots therein can come from pre-L estimates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex RG
open scoped BigOperators Topology Classical
variable {α β : Type} [Fintype α] [Fintype β] {n : Side}

namespace Invoices
def colorize (I : Invoices α β n ℝ) : Invoices α β n ℂ:=
    ⟨darken I.seed,darken I.third,darken I.fourth, approached I.inv,darken I.nonLoop₁,darken I.nonLoop₂⟩
end Invoices

/-- Cover for in-force invoices. cov Fan with one input for ease of
same period coherence. Thus base reader there essentially a unary version
of badge with 0 marks. -/
structure SceneLedger (α β : Type) where
  scale : Fan (α⊕β) (α⊕β) 1
  spur : Fan (α⊕β) (α⊕β) 2
  cross : Fan (α⊕β) (α⊕β) 3
  cov : Fan β β 1
  tail₁ : Fan (α⊕β) (α⊕β) 0
  tail₂ : Fan (α⊕β) (α⊕β) 1

/-- Pack a k=0 badge matrix, no weights. -/
def headMatrix {α : Type} [Fintype α] {ι : Type} {R:Type} [CommRing R] (F : FrameCoeffs ι α 1 R) : Matrix ι α R := injectMatrix F (fun _:Fin 0=>0)
lemma headMatrix_drive {ι τ : Type} [Fintype τ] {R:Type} [CommRing R] (F : FrameCoeffs ι τ 1 R) (v:τ→R) : headMatrix F*ᵥ v=drive F ![v] := by
  unfold headMatrix; rw [injectMatrix_mulVec]; congr 1; ext1 s; fin_cases s; rfl
lemma headMatrix_at {ι τ : Type} [Fintype τ] {R:Type} [CommRing R] (F : FrameCoeffs ι τ 1 R) (i j) : headMatrix F i j=F i ![j] := by
  classical
  have h (l:Fin 0→τ):Fin.cons j l= ![j]:=by ext1 s; fin_cases s; rfl
  simp [headMatrix,injectMatrix,h]
lemma headMatrix_cast {ι τ : Type} [Fintype τ] (F : FrameCoeffs ι τ 1 ℝ) :
    approached (headMatrix F)=headMatrix (darken F):=by
  ext i j; rw [headMatrix_at]; unfold approached; rw [map_apply,headMatrix_at]; rfl

def headSymbol {ι τ : Type} [Fintype τ] (F : Fan ι τ 1) : Symbol ι τ := fun p=> headMatrix (colors F ![p])

lemma headRoute {ι τ : Type} [Fintype τ] (F : Fan ι τ 1) {η C} (h : Cap F η C) (he : 0≤η) (n : Side) :
    Routed (0:Site n) (approached (headMatrix (pieces F n))) (fun q=> headSymbol F (mon q)):= by
  intro p v
  rw [headMatrix_cast,headMatrix_drive]; change _=ray _ (headMatrix _*ᵥ _); rw [headMatrix_drive]
  have ht : ![ray p v]=(fun i=> ray ((![p]:Fin 1→_) i) ((![v]:Fin 1→_) i)):=by ext1 s; fin_cases s; rfl
  have hh : mon ∘ (![p]:Fin 1→_)= ![mon p]:=by ext1 s; fin_cases s; rfl
  rw [ht,fan_route h he,hh,Fin.sum_univ_one,add_zero]; rfl



namespace SceneLedger
variable (L : SceneLedger α β) (η C : ℝ)
structure Credits : Prop where
  level : 0<η
  funds : 0≤C
  scale : Cap L.scale η C
  spur : Cap L.spur η C
  cross : Cap L.cross η C
  green : Cap L.cov η C
  tail₁ : ∃ D : ℝ, Cap L.tail₁ η D
  tail₂ : ∃ D : ℝ, Cap L.tail₂ η D

/-- Physical agreement on same torus, true convolution. -/
structure Published (I : Invoices α β n ℝ) : Prop where
  full : I.seed=pieces L.scale n
  marks : I.third=pieces L.spur n
  marks₂ : I.fourth=pieces L.cross n
  green : I.inv=headMatrix (pieces L.cov n)
  other₁ : I.nonLoop₁=pieces L.tail₁ n
  other₂ : I.nonLoop₂=pieces L.tail₂ n

/-- Uniform site-color size of the stationary lifts. v's zero and first
variations are all evaluated at true external momenta, not continued on q
routes. These definitions accept arbitrary Momentum; results here only when
using mon (and prescribed sums of such). `riseAmp` uses the unwrapped sum
of K slots *kept in cell counting conventions.* -/
def riseAmp (p : Momentum) (v:α→ℂ) : (α⊕β)→ℂ := Sum.elim v (-(headSymbol L.cov p*ᵥ ((headSymbol L.scale p).submatrix Sum.inr Sum.inl*ᵥ v)))
def arc (p t : Momentum) (v w:α→ℂ) : (α⊕β)→ℂ :=
    Sum.elim 0 (-(headSymbol L.cov (p+t)*ᵥ (drive (colors L.spur ![p,t]) ![riseAmp L p v,riseAmp L t w] ∘ Sum.inr)))

-- internal leg q first after the distinguished output; directions
-- on vertical true queries; same conventions as base_route.
def stamp (p : Momentum) (v : α→ℂ) : Symbol β β:=fun q=> (badge L.spur ![p] ![riseAmp L p v] q).submatrix Sum.inr Sum.inr
def stamp₂ (p t : Momentum) (v w : α→ℂ) : Symbol β β:=fun q=>
    (badge L.cross ![p,t] ![riseAmp L p v,riseAmp L t w] q + badge L.spur ![p+t] ![arc L p t v w] q).submatrix Sum.inr Sum.inr

variable {L η C}
namespace Published
open Invoices
variable {I : Invoices α β n ℝ} (H : Published L I) (hc : Credits L η C)
include H hc
omit [Fintype α] in
lemma cov_route : Routed (0:Site n) I.colorize.inv (fun q=>headSymbol L.cov (mon q)):=by rw [colorize,H.green]; exact headRoute L.cov hc.green hc.level.le n



omit [Fintype α] H hc in
lemma cov_period (p t : Momentum) (z : Cover):headSymbol L.cov (p+t+reciprocal z)=headSymbol L.cov (p+t):=by
  ext i j; change headMatrix _ _ _=headMatrix _ _ _; rw [headMatrix_at,headMatrix_at]
  let q:=joint (![p+t]:Fin 1→Momentum); let y : Shift (Arm 1):=fun i=>z i.2
  have he:joint (![p+t+reciprocal z]:Fin 1→Momentum)=q+reciprocal y:=by ext1 ⟨l,i⟩; fin_cases l; rfl
  unfold colors; rw [he,Laurent.periodic]



omit H hc in
lemma Routed_add {X Y:EndTorus n α} {F Q:Site n→EndCell α} {p : Site n} (hX:Routed p X F) (hY:Routed p Y Q): Routed p (X+Y) (fun z=>F z+Q z):=by intro s v; rw [Matrix.add_mulVec, hX,hY,Matrix.add_mulVec, ray_add]




end Published
end SceneLedger
end YM.Primitives.TwoWave
