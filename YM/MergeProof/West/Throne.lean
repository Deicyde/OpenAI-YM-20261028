import YM.MergeProof.West.Mural
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V ι κ α : Type} [Fintype ι] [Fintype κ]
variable {C : Family G} {i k l j m p q d D a N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}

section
variable [DecidableEq V] [Fintype V] {τ : ℝ} {Ψ : V → Site n}
structure Carport (s : ℕ) (W : SourceAt G Ψ) (b : ℕ) : Prop where
  diam i (H : i∈W.fires.val) j (h : j∈W.fires.val) : separation (Ψ i) (Ψ j) ≤ s
  done i (h : i∈W.fires.val) : W.extent ⊆ Spindle.patch b (Ψ i)
end
def princFt (C : Family G) (p' : BudgetPoint) (hN : k≤N) (x : Points m) (b : ℝ) (hk : i≤k) (q a : ℕ) (p : ℕ)
    (W : Bale C k b p a x hk→ SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN))) :=
    ∀ j,(W j).extent = d_olm x b q p'.B hN hk j.1 j.2.val ∧ (W j).fires=litFt p hN b C j.1 j.2.val

structure IgnFt (R : Lead G C.S p) (b : ℝ) (x : Points m) (c : Course C N p k) (hk : i < k) (hi : middle C.path.levels b k ≤ i) (q d : ℕ) (P P' : BudgetPoint) (ε : ℝ) where
  tag (a : Bale C k b p d x hk.le) (U) (h : Healthy P'.threshold (d_olm x b q P'.B c.allow hk.le a.1 a.2.val) U) :
    StageNow c R x b hk hi q a P.threshold U ε

-- R.Value bound for any requested realized activity. Need actual producers at eligible caps. Work on ONE compatible representation and flag incidence
section
variable (S : Era)


structure PleaFt (P : Rep G (C.side (i+1) p)) (P' : Rep G (C.side i p)) (y φ : ℝ) (Q : IgnFt R b x c hk h S.coast.Q a P.p P'.p y) (r : ℝ) : Prop where
  lump W (hg : princFt C P.p c.allow x b (show i+1≤k from hk) S.coast.Q a p W) (H : Shine W P.p (fun _=>r) (load S) (Perch.bill (-4) (clim C.path.levels k)))
      (z : ℝ) (hp : 0 ≤ z) (hx : z ≤ Perch.bill (-4) (clim C.path.levels k))
      (ι κ : Type) (w : Fintype ι) (v : Fintype κ) :
    let ζ := readers (C:=C) (b:=b) (p:=p) x c.allow ((show i+1≤k from hk).trans c.allow)
    let ψ := readers (C:=C) (b:=b) (p:=p) x c.allow (hk.le.trans c.allow)
    ∀ (A : ι → SourceAt G ζ) (K : κ → Lifted G ζ P.p.threshold), Light P A K (fun _ => r) (load S) z (Perch.gas S.coast (clim C.path.levels (i+1))) → Background P K →
      ∃ (α β υ : Type),∃ (_ : Fintype α) (_ : Fintype β) (_ : Fintype υ), ∃ (B : α→SourceAt G ψ) (D : β→SourceAt G ψ) (L : υ→Lifted G ψ P'.p.threshold),
        let s:= clim C.path.levels k
        let f:= clim C.path.levels i
        Background P' L ∧ Shine B P'.p (fun _=>r) (load S) (S.α*z+Perch.bill (-φ) s) ∧ Stripes P'.p L (fun _=>r) (load S+1) (Perch.gas S.coast f^2) ∧
          Shine D P'.p (fun _=>r) (load S) (Perch.bill (-2) s) ∧ (∀ i,Carport (a*P'.p.B) (D i) (S.coast.Q*P'.p.B)) ∧
            (C.path.levels.clock.op i p).push (c.changeβ (i+1)) (Value.dust P (Sum.elim A W) K)=Value.dust P' (Sum.elim B D) L ∧
              ∀ (j : Bale C k b p a x hk.le) U hh,
                (∑ i,if (D i).fires=litFt p c.allow b C j.1 j.2.val then (D i).value U else 0)=
                    (leadFt (Q.tag j U hh) (fun i=> (W (j.1,i)).value)).part (tag j.2.val).val

end
end YM.Next.Rank.Tapes.West