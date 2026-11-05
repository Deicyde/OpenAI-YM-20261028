import YM.Spin.Close

/-!
# Algebraic criterion to descend weak matrices, proof (avoids Spin cover integration)

Admissible orth data in fixed closed constrained real subgroup of intertwiner space.
No complete reducibility of actual adjoint assumed. Only perfect commutator identities
needed if supply `Limbs`. P(n) canonical function of D (pre-L vs finite here at IN continuum levels).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Function Set Filter
open scoped Topology BigOperators
variable {I : Type*} [Fintype I] [Nonempty I] {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

abbrev Mat (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] := X →L[ℂ] X
abbrev End (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] := Mat (Mat X)

def effect (f g : Mat X) : End X := (ContinuousLinearMap.mul ℂ _ f)-((ContinuousLinearMap.mul ℂ _).flip g)
omit [CompleteSpace X] in
lemma atAct (f g i : Mat X) : effect f g i=f*i-i*g := rfl
omit [Fintype I] [Nonempty I] [CompleteSpace X] in
lemma relations (l r : I → I) (B C : I → Mat X) (h : Relations B l r) (hp : Relations C l r) :
    Relations (fun i => effect (B i) (C i)) l r := by
  intro i; ext1 x
  change effect (B i) (C i) x=effect (B (l i)) (C (l i)) (effect (B (r i)) (C (r i)) x)-effect (B (r i)) (C (r i)) (effect (B (l i)) (C (l i)) x)
  simp_rw [atAct] -- rhs comp rewrite
  -- substitute only left
  conv_lhs => rw [h i,hp i]
  noncomm_ring
omit [CompleteSpace X] in
lemma cont (g : Mat X) : Continuous fun f : Mat X => effect f g :=
  Continuous.sub (ContinuousLinearMap.mul ℂ (Mat X)).continuous continuous_const

def preserves (S : AddSubgroup (Mat X)) : Subring (End X) where
  carrier := {P | MapsTo P S S}
  add_mem' {_ _} hf hg _ hx := S.add_mem (hf hx) (hg hx)
  neg_mem' {_} hf _ hx := S.neg_mem (hf hx)
  mul_mem' {_ _} hf hg _ hx := hf (hg hx)
  one_mem' _ hx := hx
  zero_mem' _ _ := S.zero_mem

omit [CompleteSpace X] in
lemma closed (S : AddSubgroup (Mat X)) (h : IsClosed (S : Set (Mat X))) : IsClosed (preserves S : Set (End X)) := by
  rw [show (preserves S:Set (End X))=⋂ x:S, (fun u : End X => u x.val) ⁻¹' S from ?eq]
  · exact isClosed_iInter fun x => h.preimage ((ContinuousLinearMap.apply ℂ (Mat X) x.val).continuous)
  case eq =>
    ext x; simp only [mem_iInter]; constructor
    · exact fun h i => (show MapsTo x S S from h) i.property
    exact fun h => (show MapsTo x S S from fun i hi => h ⟨i,hi⟩)

/-- c's Casimir polynomial. Powers ascending, Horner. -/
def evaluate (p : List ℝ) (A : End X) : End X := p.foldr (fun i s => (i:ℂ) • 1 + A*s) 0

def wave (p : List ℝ) (B C : I → Mat X) : End X := evaluate p (∑ i, effect (B i) (C i)^2) -- negative semidef free

omit [CompleteSpace X] [Nonempty I] in
lemma wave_c (p : List ℝ) (B : I → ℕ → Mat X) (C' C : I → Mat X)
    (h : ∀ i, Tendsto (B i) atTop (𝓝 (C' i))) : Tendsto (fun n => wave p (fun i => B i n) C) atTop (𝓝 (wave p C' C)) := by
  induction p with
  | nil => exact tendsto_const_nhds
  | cons a p ih => exact Tendsto.add tendsto_const_nhds (Tendsto.mul (tendsto_finsetSum Finset.univ
      (fun i hi => ((cont (C i)).continuousAt.tendsto.comp (h i)).pow 2)) ih)

/-- Concrete closed inputs. Don't assume normal S on the ACTUAL one; root polynomial needs construction on C only. -/
structure Works (p : List ℝ) (C : I → Mat X) : Prop where
  idempotent : wave p C C*wave p C C=wave p C C
  fixes : wave p C C 1=1
  kills (i : I) : effect (C i) (C i) * wave p C C = 0

/-- e.g. commute with signed reality and H. -/
def Tracks (S : AddSubgroup (Mat X)) (p : List ℝ) (C : I → Mat X) (B : I → Mat X) :=
    wave p B C ∈ preserves S ∧ ∀ i, Commute (wave p B C) (effect (B i) (C i))

lemma realize (B : ℕ → I → Mat X) (C : I → Mat X) (l r : I → I) (hb : ∀ i, Tendsto (fun n => B n i) atTop (𝓝 (C i)))
    (hf : ∀ᶠ n in atTop, Relations (B n) l r) (hc : Relations C l r) (p : List ℝ) (hA : Works p C) (S : AddSubgroup (Mat X))
    (h : 1∈S) (hs : IsClosed (S : Set (Mat X))) (ht : ∀ᶠ i in atTop, Tracks S p C (B i)) : ∀ᶠ i in atTop,
    ∃ f : Mat X, IsUnit f ∧ f∈S ∧ ∀ j, B i j*f = f*C j := by
  let D j n := effect (B n j) (C j)
  have he j := (cont (C j)).continuousAt (x := C j) |>.tendsto.comp (hb j)
  have hv : ∀ᶠ i in atTop, Relations (flip D i) l r := hf.mono (fun i hi => relations _ _ _ _ hi hc)
  obtain ⟨Q,hQ,hy⟩ := onto _ _ D _ he hv _ _ (wave_c p (flip B) C C hb) hA.idempotent hA.kills (preserves S)
    (closed S hs) (ht.mono (fun i hi => hi.1)) (ht.mono (fun i hi => hi.2))
  let f n := Q n 1
  have hp : Tendsto f atTop (𝓝 1) := by
    rw [← hA.fixes]
    exact ((ContinuousLinearMap.apply ℂ (Mat X) (1 : Mat X)).continuous.tendsto _).comp hQ
  filter_upwards [hy, hp.eventually (Units.isOpen.mem_nhds isUnit_one)] with i hi hw
  refine ⟨f i,hw, (show MapsTo (Q i) S S from hi.1) h,fun j => sub_eq_zero.mp ?_⟩
  change effect _ _ ((Q i) 1)=0
  exact congr_arg (fun A : End X => A 1) (hi.2.2 j).2
end YM.Spin
