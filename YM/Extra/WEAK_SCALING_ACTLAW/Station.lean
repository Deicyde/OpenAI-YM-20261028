import YM.Bid.Craft
import YM.Extra.WEAK_SCALING_ACTLAW.Geometry
import YM.Next.EXTRACTION.Raw
import YM.Next.FOUNDATIONS.SU2

/-!
# Finite weak-scale requests (outstanding) and common ordered extraction

Data on the actual cutoff/Wilson/reference objects; the linear columns sent
by Xi may have *different* calibrations at each cap. They do not take quotient
values on the receiving side at finite period, and there is no invertibility,
inter-cap compatibility or limiting assumption in these estimates. Same maps
throughout placements and tests. The grid integer is deliberately separate
from the station index and from the centered-estimate widths. See also the
adapter from corrected rooted estimates (Rooted).

The height/band/calibration receipts upstream of these finite estimates are
not part of ActLaw and are NOT supplied here. Need the estimates for every
required finite demand on the SAME C (Might require new prices etc.).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function Filter MeasureTheory Extraction Climb Table Ward
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G}

abbrev Free (C : Family G) := Climb.Bel C.book
abbrev Column (C : Family G) (d : ℕ) := (Free C).Field d →L[ℂ] C.book.Ref d

structure Stations (C : Family G) where
  r : ℕ → ℝ
  positive k : 0 < r k
  shrinks : Tendsto r atTop (𝓝 0)
  grid : ℕ → ℕ
  fine : Tendsto (fun k => C.S.a (grid k) / r k) atTop (𝓝 0)
  coef (k d N p : ℕ) : Column C d

abbrev Stations.delta (b : Stations C) (k : ℕ) := C.S.a (b.grid k) / b.r k

def Stations.name (b : Stations C) (k N p : ℕ) (v : (Free C).Tag) : C.book.Token :=
  ⟨v.1,b.coef k v.1 N p v.2⟩

def Stations.rescaled {n : ℕ} (b : Stations C) (k : ℕ) (u : Fin n → Lattice.Cover) := tag (b.delta k) u
lemma Stations.physical (b : Stations C) {n : ℕ} (k : ℕ) (u : Fin n → Lattice.Cover) :
    b.r k • b.rescaled k u = Order.grid C (b.grid k) u := by
  rw [rescaled,smul_tag, mul_div_cancel₀ _ (b.positive k).ne']
  rfl

def Stations.cost (b : Stations C) (k N p : ℕ) {n : ℕ} (v : Fin n → (Free C).Tag) (u : Fin n → Lattice.Cover) : ℂ :=
  C.numeric N p (b.name k N p ∘ v) (fun i => Cells.location C.S (b.grid k) N p (u i))

abbrev capped {L : Register G} {S : Table L} {n : ℕ} (D : ℕ) (v : Fin n → S.Tag) := ∀ i, (v i).1 ≤ D

def Sym (b : Stations C) (f : Order) (h : (Free C).RealSpin) (k d : ℕ) := f.late fun N p =>
    let c := b.coef k d N p
    (∀ g u, c ((Free C).mirror h d g u) = C.book.mirrorGroup d g (c u)) ∧
      (∀ u, c ((Free C).conj h d u) = star (c u)) ∧ c ((Free C).unit d) = C.refUnit d

/-- Centered root estimates (on `seen`, not just the ordinary moment),
including conjugate/signed variants. As in E kyf B with delta=0 and fixed
c small depending on Q,n. Can pay `A^n = p^o(b)` here. Second cell width m
allows moving the tiling through projection ties to bound actual joint
values; need a schedule with room before the centered budget width j. Don't
round these comparisons by freely altering a previously supplied k,r.
-/
def CenterCosts (b : Stations C) (f : Order) (M D : ℕ) (Q : ℝ) : Prop :=
    ∀ n, n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v →
    ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ Tendsto (fun k => (A k)^n*b.delta k) atTop (𝓝 0) ∧
    ∀ᶠ k in atTop, ∃ m j : ℕ, m≤j ∧ C.S.a m < b.r k/Q ∧
      (n:ℝ)*(2*(3*C.S.a j)) < C.S.a m ∧ C.S.a j < b.r k/(4*Q) ∧
      f.late fun N p => ∀ i s, centeredBudget C
        (Extraction.Spin.token C.book (b.name k N p (v i)) s) (A k) j N p

/-- Missing aligned finite moment comparison, no tie tests and no derivative
or uniformity across *choices* of lists/vectors. `u` approaches no seam in
the ordered volume limit at fixed k. -/
def AlignedCosts (b : Stations C) (f : Order) (M D : ℕ) (Q : ℝ) : Prop :=
    ∀ n, n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ u : Fin n → Lattice.Cover, b.rescaled k u ∈ apart Q n →
        b.rescaled k u ∈ generic n → f.late fun N p =>
          ‖b.cost k N p v u - disc v (b.rescaled k u)‖ ≤ ε

/-- The estimates must be delivered together. Boundedness of coef requested
also above the tested cap only for typing convenience (can pad by zero).
Each k,d whose coefficients are chosen needs a bound, not uniform in k,d.
The p threshold p₀ is free because here we don't need these limits at small
p. -/
structure FiniteCosts (b : Stations C) (f : Order) (h : (Free C).RealSpin) (M D : ℕ) (Q : ℝ) : Prop where
  bounded (k d : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ᶠ j in atTop, ‖b.coef k d (f.mesh j) p‖ ≤ A
  sym k d : d ≤ D → Sym b f h k d
  center : CenterCosts b f M D Q
  aligned : AlignedCosts b f M D Q

variable {M D n : ℕ} {Q : ℝ} {f : Order} {h : (Free C).RealSpin} {b : Stations C}

lemma FiniteCosts.further (H : FiniteCosts b f h M D Q) (g : Order) : FiniteCosts b (f.refine g) h M D Q where
  bounded k d := by
    obtain ⟨A,hA,p₀,hp⟩ := H.bounded k d
    exact ⟨A,hA,p₀,fun p e => g.mesh.cofinal.eventually (hp p e)⟩
  sym k d hd := Order.late_refine f g (H.sym k d hd)
  center n hn v hv := by
    obtain ⟨A,hA,ha,ht⟩ := H.center n hn v hv
    refine ⟨A,hA,ha,ht.mono ?_⟩
    rintro k ⟨m,j,e,h₁,h₂,h₃,h₄⟩
    exact ⟨m,j,e,h₁,h₂,h₃,Order.late_refine _ _ h₄⟩
  aligned n hn v hv ε hε := (H.aligned n hn v hv ε hε).mono
    fun _ H _ he hu => Order.late_refine _ _ (H _ he hu)

open Next.Extract in
lemma FiniteCosts.select (H : FiniteCosts b f h M D Q) :
    ∃ g : Order, ∃ a : ∀ (_ d : ℕ), Column C d, ∀ k d, ∃ p₀ : ℕ,
      (f.refine g).limits (fun p => p₀ ≤ p) (b.coef k d) (a k d) := by
  choose A hA u hu using H.bounded
  let X (i : ℕ × ℕ) := Column C i.2
  haveI (i : ℕ × ℕ) : ProperSpace (X i) := FiniteDimensional.proper ℂ (Column C i.2)
  let T (i : ℕ × ℕ) N p : X i := b.coef i.1 i.2 N p
  have he (i : ℕ × ℕ) := f.per.cofinal.eventually (eventually_ge_atTop (u i.1 i.2))
  have ht : Reserve f (fun i p => u i.1 i.2 ≤ p) T := Reserve.of_norm (X:=X) (T:=T) he
    (fun i p hp => ⟨_,hA i.1 i.2, hu i.1 i.2 p hp⟩)
    (fun i => ⟨_,hA i.1 i.2,(he i).mono fun _ h => hu i.1 i.2 _ h⟩)
  obtain ⟨g,z,y,hg⟩ := ht.gather
  exact ⟨g, fun k d => y (k,d), fun k d => ⟨u k d,hg.limits (k,d)⟩⟩

/-- Use the ordered refinement only by consequence of the TWO limits, no
single joint diagonal identification. -/
structure Retained (b : Stations C) (f : Order) where
  a (k d : ℕ) : Column C d
  tends k d : Tendsto (fun j : ℕ × ℕ => b.coef k d j.1 j.2) f.fuse (𝓝 (a k d))

lemma FiniteCosts.ready (H : FiniteCosts b f h M D Q) : ∃ g : Order, Nonempty (Retained b (f.refine g)) := by
  obtain ⟨g,a,ha⟩ := H.select
  exact ⟨g,⟨a, fun k d => Order.along (ha k d).choose_spec⟩⟩

abbrev Maps (S : Table C.book) := ∀ (_ d : ℕ), (Free C).Field d →ₗ[ℂ] S.Field d

def routed {S : Table C.book} (U : Maps S) (k : ℕ) (v : (Free C).Tag) : S.Tag := ⟨v.1,U k v.1 v.2⟩
namespace Retained
variable (Z : Retained b f) (S : Table C.book)

def maps : Maps S := fun k d => (S.project d).comp (Z.a k d).toLinearMap
variable {S}

private lemma col_tends (k d : ℕ) (v : (Free C).Field d) : Tendsto (fun j : ℕ × ℕ => b.coef k d j.1 j.2 v)
    f.fuse (𝓝 (Z.a k d v)) := Dash.arcing (Z.tends k d) tendsto_const_nhds

lemma marks (H : FiniteCosts b f h M D Q) (hs : S.RealSpin) (k d : ℕ) (hd : d ≤ D) :
    (∀ g v, Z.maps S k d ((Free C).mirror h d g v) = S.mirror hs d g (Z.maps S k d v)) ∧
    (∀ v, Z.maps S k d ((Free C).conj h d v) = S.conj hs d (Z.maps S k d v)) ∧
      Z.maps S k d ((Free C).unit d) = S.unit d := by
  have he : ∀ᶠ j : ℕ × ℕ in f.fuse,
      let c := b.coef k d j.1 j.2
      (∀ g u, c ((Free C).mirror h d g u) = C.book.mirrorGroup d g (c u)) ∧
      (∀ u, c ((Free C).conj h d u) = star (c u)) ∧ c ((Free C).unit d) = C.refUnit d := H.sym k d hd
  change (∀ _ _, S.project _ _ = _) ∧ (∀ _, S.project _ _ = _) ∧ S.project _ _ = _
  constructor
  · intro g v
    rw [maps, LinearMap.comp_apply,S.mirror_project]
    apply congrArg
    apply tendsto_nhds_unique ((Z.col_tends k d _).congr' (he.mono (fun j hj => hj.1 g v)))
      (((C.book.mirrorGroup d g).continuous_of_finiteDimensional.tendsto _).comp (Z.col_tends k d v))
  constructor
  · intro v
    rw [maps,LinearMap.comp_apply,S.conj_project]
    exact congrArg (S.project d) (tendsto_nhds_unique
      ((Z.col_tends k d _).congr' (he.mono fun _ hj => hj.2.1 v)) ((Z.col_tends k d v).star))
  apply congrArg (S.project d) (tendsto_nhds_unique ((Z.col_tends k d _).congr' (he.mono fun _ hj => hj.2.2)) tendsto_const_nhds)

end Retained
end YM.Extra.WeakScaling
