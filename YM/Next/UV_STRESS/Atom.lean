import YM.Lane.Lease
import YM.Next.UV_STRESS.Rates
import YM.Next.UV_STRESS.Tiles


/-!
# Bounded substitutes for the cutoff fields: layout

Arbitrary far/fine assemblies have to use the *same* substitutes.
Copies can be after signs and mirrors (here construct `fine` choosing
the inputs at origin first with inverse actions). This lemma lets the
approximants depend on copy parity/type; the phase consumer only needs
that much. They go on the actual h grid. We prove estimates for arbitrary
lists of *distinct* sites on that grid at finite period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Around Wilson Cells Lattice
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {h d k N p : ℕ}

def paint {α : Type*} (g : α → ℝ) (x : α) : ℂ := g x

/-- Sup on the full function (fixed accuracy/station). Smallness on the
*difference*, in honest expectation of the ALL-site replica. Old atom is
C.seen with all literal coefficients, rendering covariance. A preliminary
port; below we want such receipts produced already from joint blocking.
-/
structure Origin (C : Family G) (f : Extraction.Order) (h : ℕ) (v : C.book.Token) (ε : ℝ)
    (g : (N p : ℕ) → Config G (C.side N p) → ℝ) (M : ℝ) : Prop where
  bound : 0 ≤ M
  honest : f.late fun N p => ∃ hk : h ≤ N,
    let T := center C.S p hk 0
    (∀ x, |g N p x| ≤ M) ∧ Interior (T.chamber 0) (paint (g N p)) ∧
      T.rootTest (C.beta N p) (paint (g N p) - C.seen v (0:Site (C.side N p))) ≤ ε

def Entitled (C : Family G) (d : ℕ) := {v : C.book.Token // v.1 ≤ d ∧ star v.2=v.2}

lemma encore (v : Entitled C d) (b : Extraction.Spin.Frame) :
    let x := Extraction.Spin.token C.book v.val b
    x.1≤d ∧ star x.2=x.2 := by
  rcases b with ⟨s,y|y⟩
  · let g := C.book.mirrorGroup v.val.1 s
    exact ⟨v.property.1,(C.book.star_mirror s _ _).trans (congr_arg g v.property.2)⟩
  let g := C.book.mirrorGroup v.val.1 s
  refine ⟨v.property.1,?_⟩
  change star (star (C.book.mirrorGroup _ s v.val.2))=star (C.book.mirrorGroup _ s v.val.2)
  rw [star_star]; exact ((C.book.star_mirror s _ _).trans (congr_arg g v.property.2)).symm

def variant (v : Entitled C d) (b : Extraction.Spin.Frame) : Entitled C d := ⟨_,encore v b⟩

def previous (v : Entitled C d) (b : Extraction.Spin.Frame) : Entitled C d := variant v (b.1⁻¹,b.2)

/-- Coherent use of the same individual preparations. -/
structure Maker (C : Family G) (f : Extraction.Order) (h d : ℕ) where
  purchase : (k : ℕ) → Entitled C d → (N p : ℕ) → Config G (C.side N p) → ℝ
  cash : ℕ → Entitled C d → ℝ
  terms (k : ℕ) (v) : Origin C f h v.val (costHint k) (purchase k v) (cash k v)

def copyReal {n : Side} (T : Tiling n) (i : T.Cell) (g : Config G n → ℝ) : Config G n → ℝ :=
  g ∘ Lattice.pull (T.omega i) (T.translateBy i)

lemma copy_real {n : Side} (T : Tiling n) (i : T.Cell) (g : Config G n → ℝ) :
    T.copy i (paint g)=paint (copyReal T i g) := by
  funext A; unfold Tiling.copy
  split
  · simp only [copyReal, paint, Complex.star_def, Complex.conj_ofReal]; rfl
  rfl

lemma budgets_at (H : C.Makes) (hS : CellHyp C f) (h : ℕ) (v : C.book.Token) :
    ∃ A : ℝ, 0 ≤ A ∧ f.late fun N p => ∃ hk : h≤N,
      let T := center C.S p hk 0
      let U := C.seen v (0:Site (C.side N p))
      Interior (T.chamber 0) U ∧ T.rootTest (C.beta N p) U ≤ A := by
  have ht : Tendsto (fun k => 9*C.S.a k) atTop (𝓝 0) := by simpa using C.S.shrinks.const_mul 9
  let t := fun _ : Fin 1 => v
  obtain ⟨k,hk,hw,A,hA,h⟩ := ((eventually_ge_atTop h).and ((ht.eventually (ge_mem_nhds (C.S.a_pos h))).and
    (grows hS t))).exists
  refine ⟨A,hA,?_⟩
  refine h.mono fun i hi => hi.mono fun j hj => ?_
  let N:=f.mesh j; let p:=f.per i
  have he : k ≤ N := hj.1
  let T := center C.S p (hk.trans he) 0
  let b := Cells.span C.S he p
  have hb : 9*b ≤ T.side.val := by
    apply (Nat.cast_le (α:=ℝ)).1; apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [C.S.embeds_scale]; push_cast
    change C.S.a N*(9*(↑b:ℝ)) ≤ C.S.a _
    rw [mul_left_comm, show C.S.a N * b= _ from C.S.embeds_scale (C.S.toDepth he p)]; exact hw
  have ha : 0<b := (C.S.toDepth he p).count.property
  have hv : (0:Site (C.side N p)) ∈ T.margin 0 (3*b) := by
    refine ⟨base_point C.S (p:=p) (hk.trans he) 0,fun i => ?_⟩
    have hi : T.coordinated 0 0 i=T.side.val/2:= handy C.S (hk.trans he) (p:=p) 0 i
    change 3*b≤_ ∧ T.coordinated (0:T.Cell) 0 i+3*b+1≤T.side.val
    rw [hi]; omega
  obtain ⟨U,hu,H,hh⟩ := Lease.alive (q:=t) H 0 _ hj he (inherits hk he) hv
  have hp : U=C.seen v 0 := (funext fun i => (T.copy_zero U i).symm).trans hu
  exact ⟨hk.trans he,hp ▸ H,hp ▸ hh⟩

namespace Maker
variable (P : Maker C f h d)

def fine (k N p : ℕ) (v : Entitled C d) (i : Site (C.side h p)) : Config G (C.side N p) → ℝ :=
  if hk : h≤N then
    let T := center C.S p hk 0
    let t := previous v (Extraction.Spin.way T i)
    copyReal T i (P.purchase k t N p) else 0

private lemma series_le {ι : Type*} [Fintype ι] (c : ι → ℝ) (h : ∀ i,0≤c i) (j : ι) : c j ≤ ∑ i, c i :=
  Finset.single_le_sum (f:=c) (fun i _ => h i) (Finset.mem_univ j)

theorem nearby (H : C.Makes) (hp : CellHyp C f) (v : Entitled C d) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ k, ∃ M : ℝ,0 ≤ M ∧ ∀ᶠ i : ℕ × ℕ in f.fuse, ∃ hk : h ≤ i.1,
      let T := center C.S i.2 hk 0
      ∀ j : T.Cell, ∃ X Y : Config G (C.side i.1 i.2)→ℂ,
        Interior (T.chamber 0) X ∧ Interior (T.chamber 0) Y ∧
        C.seen v.val (T.copyMap j 0)=T.copy j X ∧ paint (P.fine k i.1 i.2 v j)= T.copy j Y ∧
          T.rootTest (C.beta i.1 i.2) X ≤ A ∧ T.rootTest (C.beta i.1 i.2) (Y-X) ≤ costHint k ∧
            ∀ a, |P.fine k i.1 i.2 v j a| ≤ M := by
  classical
  choose C₀ hC hF using fun i : Extraction.Spin.Frame => budgets_at H hp h (previous v i).val
  refine ⟨∑ i,C₀ i,Finset.sum_nonneg (fun i _ => hC _),fun k => ?_⟩
  let K (i : Extraction.Spin.Frame) := previous v i
  have hx (j : Extraction.Spin.Frame) : C₀ j ≤ ∑ i : Extraction.Spin.Frame,C₀ i := series_le C₀ hC j
  have ho (j : Extraction.Spin.Frame) : P.cash k (K j) ≤ ∑ i : Extraction.Spin.Frame,P.cash k (K i) := series_le _
    (fun i => (P.terms k (K i)).bound) j
  refine ⟨∑ i : Extraction.Spin.Frame,P.cash k (K i),Finset.sum_nonneg (fun i _ => (P.terms k (K i)).bound),?_⟩
  let X (N p i) := C.seen (K i).val (0:Site (C.side N p))
  let G₁ (N p i) := P.purchase k (K i) N p
  have he (v : Extraction.Spin.Frame) : ∀ᶠ i in f.fuse, ∃ hk : h ≤ i.1,
      let T := center C.S i.2 hk 0
      Interior (T.chamber 0) (X i.1 i.2 v) ∧ T.rootTest (C.beta i.1 i.2) (X i.1 i.2 v) ≤ C₀ v := hF v
  have hv (v : Extraction.Spin.Frame) : ∀ᶠ i in f.fuse, ∃ hk : h ≤ i.1,
      let T := center C.S i.2 hk 0
      let D := G₁ i.1 i.2 v
      (∀ x, |D x| ≤ P.cash k (K v)) ∧ Interior (T.chamber 0) (paint D) ∧
        T.rootTest (C.beta i.1 i.2) (paint D-X i.1 i.2 v) ≤ costHint k := (P.terms k _).honest
  filter_upwards [eventually_all.mpr he,eventually_all.mpr hv,eventually_all.mpr
    (fun i : Extraction.Spin.Frame => large_mesh f (C.ref (K i).val.1)),large_mesh f h] with i hh hw hc hj
  obtain ⟨N,p⟩ := i
  refine ⟨hj, fun j => ?_⟩
  let T := center C.S p hj 0; let t := Extraction.Spin.way T j
  obtain ⟨_,hV,hZ⟩ := hh t
  obtain ⟨_,hG,hX,hY⟩ := hw t
  have hY' : P.fine k N p v j=copyReal T j (G₁ N p t) := by unfold fine; rw [dif_pos hj]
  have h' : T.copy j (X N p t)=C.seen v.val (T.copyMap j 0) :=
    (Extraction.Spin.uses H T j 0 _ (hc t)).trans (by
      rw [show Extraction.Spin.token C.book (K t).val t=v.val from Extraction.Spin.isotropy ..])
  refine ⟨X N p t,paint (G₁ N p t),hV,hX,h'.symm,?_,hZ.trans (hx t),hY,fun i => ?_⟩
  · change paint (P.fine k N p v j) = T.copy j _; rw [copy_real,hY']
  change |P.fine k N p v j i| ≤ _
  rw [hY']; exact (hG (pull (T.omega j) (T.translateBy j) i)).trans (ho t)
end Maker
end YM.Next.UVStress
