import YM.Next.RANK.Payload

/-!
# The one-step Estimate hypotheses

These are physics inputs, NOT consequences of Shape/Lawful/etc. Specialized
raw transfer estimates (may need e.g. significantly strengthened precursor
work from RBin/RAdvances/...). Includes source steps with the new clock (including on epochs which
won't use ANY comparison sectors in actual continuum extraction). Use candidacy
only on the ranked stretches and probes. Doesn't ask for normalized physical
estimates across the steps, nor for unforced energies compared to a W polynomial.
It concerns positions where `op j` is actual chosen frame. Care must be taken in
applications to supply these on *that* witness, throughout each paid arc.

- `Ignition`: appointment for principal term integration.

NO W or R inputs, must
  choose data on ANY specified good output field and target (even when flags still
  visible outside).

Full field/read for each tag, only channel closeness inputs
  requested (covariance is an important new input -- might aim for a derivation
  off compression fits etc with extra work; not known).

Wants membership in pre-step masks even on boundaries.
- `Pleases`: existence of LOCAL output labellings on the unscaled-r gyroscope
  specialized in chosen epochs.

Keep Bg (`Column` equality by compatibility key);
  raw family `D` denotes unforced H pieces with only principal W input(s), with
  anchored shape/cost.

`B` for R partners.

Hooks retain all mask inventory.

On mask, the D pieces themselves account
  for the single chosen law entered, at the restricted glyph, with prior W inputs.

This is a STEP estimate obligation before W polynomial probes (specialized version
  of K:Pcq call, prior to stops).

Quoted for W local footprints, quantifies any
  such small gauge values with the actual geometry.

No reformatting, all mask and
  correction moves additional.

The Bg agreement is intended to facilitate such an
  estimate through Step inputs (not a proof that grouping gives a valid comparison).
- `NonLeading`: rough response where no redistribution into leading W needed.

Same push, weaker energy at restored v, no layout gains.

Ratio
  exponents in budget needn't be the previous unmarked exponent; still ask for TRUE
  outputs at those budgets; classify as additional one-kernel estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V ι κ α : Type} [Fintype ι] [Fintype κ]
variable {C : Family G} {i k l j m p q d D a N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}

section
variable [DecidableEq V] [Fintype V] {τ : ℝ} {Ψ : V → Site n}

-- denom references in Portal. cost relative, stamp responsibility later
def glows (x : V → Site n) (t : Finset V) (z : ℕ) := fun i j=> i∈t ∧ j∈t ∧ separation (x i) (x j) ≤ z

structure Routes (s : ℕ) (W : SourceAt G Ψ) (b : ℕ) : Prop where
  -- when any physical unforced piece is kept as W (non-leading ones unrestricted)
  old i (H : i∈W.fires.val) j (h : j∈W.fires.val) : Relation.ReflTransGen (glows Ψ W.fires.val s) i j
  done i (h : i∈W.fires.val) : W.extent ⊆ Spindle.patch b (Ψ i)

def Shine (H : ι → SourceAt G Ψ) (p : BudgetPoint) (r : V→ℝ) (e z : ℝ) :=
    ∃ v : ι→ℝ,(∀ i,(H i).pays p r e (v i)) ∧
    ∀ i : V, ∑ j, (if i∈(H j).fires.val then v j else 0) ≤ z
def Stripes (p : BudgetPoint) (K : κ→ Lifted G Ψ p.threshold) (r : V→ℝ) (e z : ℝ) :=
    ∃ v : κ→ℝ,(∀ i,Lifted.pays p (K i) r e (v i)) ∧
    ∀ i : Site n, (∑ j, if i∈(K j).extent then v j else 0) ≤ z
end

def principle (C : Family G) (p' : BudgetPoint) (hN : k≤N) (x : Points m) (b : ℝ) (hk : i≤k) (q a : ℕ) (p : ℕ)
    (W : Lane C k b p a x hk→ SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN))) :=
    ∀ j,(W j).extent = dolmens x b q p'.B hN hk j.1 j.2.val ∧ (W j).fires=litWord p hN b C j.1 j.2.val

structure Ignition (R : Lead G C.S p) (b : ℝ) (x : Points m) (c : Course C N p k) (hk : i < k) (hi : middle C.path.levels b k ≤ i) (q d : ℕ) (P P' : BudgetPoint) (ε : ℝ) where
  tag (a : Lane C k b p d x hk.le) (U) (h : Healthy P'.threshold (dolmens x b q P'.B c.allow hk.le a.1 a.2.val) U) :
    StageX c R x b hk hi q a P.threshold U ε

-- R.Value bound for any requested realized activity. Need actual producers at eligible caps. Work on ONE compatible representation and flag incidence
section
variable (S : Era)
def load (S : Era) := S.coast.e+2

structure Pleases (P : Rep G (C.side (i+1) p)) (P' : Rep G (C.side i p)) (y φ : ℝ) (Q : Ignition R b x c hk h S.coast.Q a P.p P'.p y) (r : ℝ) : Prop where
  lump W (hg : principle C P.p c.allow x b (show i+1≤k from hk) S.coast.Q a p W) (H : Shine W P.p (fun _=>r) (load S) (Perch.bill (-4) (clim C.path.levels k)))
      (z : ℝ) (hp : 0 ≤ z) (hx : z ≤ Perch.bill (-4) (clim C.path.levels k))
      (ι κ : Type) (w : Fintype ι) (v : Fintype κ) :
    let ζ := readers (C:=C) (b:=b) (p:=p) x c.allow ((show i+1≤k from hk).trans c.allow)
    let ψ := readers (C:=C) (b:=b) (p:=p) x c.allow (hk.le.trans c.allow)
    ∀ (A : ι → SourceAt G ζ) (K : κ → Lifted G ζ P.p.threshold), Light P A K (fun _ => r) (load S) z (Perch.gas S.coast (clim C.path.levels (i+1))) → Background P K →
      ∃ (α β υ : Type),∃ (_ : Fintype α) (_ : Fintype β) (_ : Fintype υ), ∃ (B : α→SourceAt G ψ) (D : β→SourceAt G ψ) (L : υ→Lifted G ψ P'.p.threshold),
        let s:= clim C.path.levels k
        let f:= clim C.path.levels i
        Background P' L ∧ Shine B P'.p (fun _=>r) (load S) (S.α*z+Perch.bill (-φ) s) ∧ Stripes P'.p L (fun _=>r) (load S+1) (Perch.gas S.coast f^2) ∧
          Shine D P'.p (fun _=>r) (load S) (Perch.bill (-2) s) ∧ (∀ i,Routes (a*P'.p.B) (D i) (S.coast.Q*P'.p.B)) ∧
            (C.path.levels.clock.op i p).push (c.changeβ (i+1)) (Value.dust P (Sum.elim A W) K)=Value.dust P' (Sum.elim B D) L ∧
              ∀ (j : Lane C k b p a x hk.le) U hh,
                (∑ i,if (D i).fires=litWord p c.allow b C j.1 j.2.val then (D i).value U else 0)=
                    (leadQ (Q.tag j U hh) (fun i=> (W (j.1,i)).value)).part (tale j.2.val).val

-- called j = width .. middle-1. fresh hit there at post-L rate (the statement with previous-level hat). Different LD record. multiplier can still be jointly chosen pre-L. ε ratio input (positive). Same coefficient world; no comparison expectation needed.
structure NonLeading (x : Points m) (r : ℝ) (c : Course C N p k) (j : ℕ) (P : Rep G (C.side (j+1) p)) (P' : Rep G (C.side j p)) (b : ℝ) : Prop where
  rent (h : j+1≤ N) (α β : Type) (F : Fintype α) (v : Fintype β) :
    let ζ:= readers (C:=C) (b:=b) (p:=p) x c.allow h
    let ψ:= readers (C:=C) (b:=b) (p:=p) x c.allow ((Nat.le_succ _).trans h)
    ∀ (H : α→ SourceAt G ζ) (K : β→ Lifted G ζ P.p.threshold) (z : ℝ), 0 ≤ z → z ≤ Perch.bill (-1/2) (clim C.path.levels k) →
      Light P H K (fun _=>r) S.coast.e z (z*Perch.w (clim C.path.levels (j+1))) → Background P K →
        Value.Notice P' ψ ((C.path.levels.clock.op j p).push (c.changeβ (j+1)) (Value.dust P H K)) (fun _=>r)
          S.coast.e (S.α*z+Perch.bill (1/2) (clim C.path.levels k)*z^2) (Perch.gas S.coast (clim C.path.levels (j+1)))
end
end YM.Next.Rank.Tapes
