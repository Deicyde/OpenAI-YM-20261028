import YM.Euclid.Differential
import YM.OPE.Eye.Word
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Compatible choice of readout, independent of horizon

The trick is to pick **both** basis and detectors (of the actual Wilson
physical fields). With point detectors we can use kernels of actual
local evaluations for choosing higher-grade axis lifts. This realizes exactly
biorthogonal choices, rather than tuning a convention depending on the
horizon of the request, or varying stages on a logarithmic diagonal.

No particular real/spectral type of basis is imposed. These are complex
filtered bases. Changing any of these labels by filtration projection or
equation-null replacement still has the already constructed probability laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table LinearMap
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} (P:DiffPlan S) {m n d : ℕ}

def old (P:DiffPlan S)(n:ℕ) : Submodule ℂ (S.Field n) := match n with
    | 0=>⊥
    | n+1 => LinearMap.range (P.rise (Nat.le_succ n))
def addition (n:ℕ):ℕ:= Module.finrank ℂ (S.Field n ⧸ old P n)
abbrev Mode := (n : ℕ) × Fin (addition P n)
def bands (n:ℕ) : Finset (Mode P) := (Finset.range (n+1)).sigma fun i=> Finset.univ
lemma full_bands (x:Mode P) : x∈ bands P n↔ x.fst ≤ n:=by simp [bands, Nat.lt_succ_iff]

def quotientFrame (n:ℕ) := Module.finBasis ℂ (S.Field n ⧸ old P n)
abbrev Qname (n:ℕ) := Fin (addition P n)
def helpers (p: Exterior L→₀ ℂ)(d:ℕ): S.Field d→ₗ[ℂ] ℂ:= Finsupp.linearCombination ℂ (fun i:Exterior L=> (LinearMap.proj i : (Exterior L → ℂ)→ₗ[ℂ] ℂ).comp (S.spectra d)) p
lemma computes (p: Exterior L→₀ ℂ)(x:S.Field d): helpers p d x=∑ i∈p.support,p i * S.spectra d x i := by
    unfold helpers; rw [Finsupp.linearCombination_apply]; simp only [Finsupp.sum, LinearMap.sum_apply]; rfl
lemma reachReads (n:ℕ)(x:S.Field n→ₗ[ℂ] ℂ): ∃ B: Exterior L →₀ ℂ, helpers B n=x:=by
    let f:= (fun i:Exterior L=> (LinearMap.proj i : (Exterior L→ℂ) →ₗ[ℂ] ℂ).comp (S.spectra n))
    let V:= Submodule.span ℂ (Set.range f); have hs: V.dualCoannihilator=⊥:=by
       apply le_bot_iff.mp; intro x hx; refine (Submodule.mem_bot ..).mpr ((S.faithfully n) (funext fun i=>?_ )); change S.spectra n x i= _; rw [map_zero]; exact (Submodule.mem_dualCoannihilator _).mp hx (f i) (Submodule.subset_span (Set.mem_range_self _))
    have he : V=⊤:=by rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=V),hs]; simp
    have ht:= Finsupp.range_linearCombination .. |>.trans he; exact (LinearMap.range_eq_top.mp ht) x

structure Prescription (P: DiffPlan S) where
    needle (i : Mode P): S.Field i.1
    sheet (i : Mode P): Exterior L →₀ ℂ
namespace Prescription
variable {P}
def loaded (U: Prescription P)(x:Mode P)(d:ℕ): S.Field d:= if h:x.1 ≤ d then P.rise h (U.needle x) else 0
@[simp] lemma cost (U: Prescription P)(x:Mode P)(h:x ∈ bands P m) : U.loaded x m=P.rise ((full_bands ..).mp h) (U.needle x):= dif_pos ((full_bands ..).mp h)
def test (U:Prescription P)(x:Mode P)(d:ℕ): S.Field d →ₗ[ℂ] ℂ:= helpers (U.sheet x) d
lemma affinity (h:S.Symmetric)(hp:P.Inclusions S)(U:Prescription P)(i:Mode P)(x:S.Field m)(hm:m≤n): U.test i n (P.rise hm x)=U.test i m x:=by
    unfold test; rw [computes,computes,P.through_limit h hp]
lemma load_next (h:S.Symmetric)(hp:P.Inclusions S)(U:Prescription P)(i:Mode P)(hi:i∈ bands P m)(hm:m≤n): U.loaded i n = P.rise hm (U.loaded i m):=by
    rw [cost U i hi,cost U i ((full_bands ..).mpr (le_trans ((full_bands ..).mp hi) hm)),P.transit h hp]
structure Extends (n:ℕ)(U V: Prescription P) : Prop where
    needle (i) : i∈ bands P n→ U.needle i=V.needle i -- v larger
    sheet (i) : i∈ bands P n→ U.sheet i=V.sheet i
structure SignedOff (n:ℕ) (U:Prescription P): Prop where
    bothWays (i j: Mode P): i∈ bands P n → j∈ bands P n → U.test i n (U.loaded j n) = if i=j then 1 else 0
    rebuilds (x:S.Field n): ∑ i∈ bands P n,U.test i n x • U.loaded i n=x

def Coherent (U:Prescription P) := ∀ n,SignedOff n U
lemma SignedOff.of_extends {U V: Prescription P}(h:SignedOff n U)(hp:Extends n U V): SignedOff n V:=by
    constructor
    · intro i j hi hj; rw [test, ← hp.sheet i hi,cost V j hj,← hp.needle j hj, ← cost U j hj]; exact h.bothWays _ _ hi hj
    intro x; apply Eq.trans (b:=∑ i∈ bands P n,U.test i n x • U.loaded i n) _ (h.rebuilds x); refine Finset.sum_congr rfl fun i hi=>?_ ; rw [test,test,hp.sheet i hi,cost _ i hi,cost _ i hi, hp.needle i hi]
end Prescription
end YM.OPE
