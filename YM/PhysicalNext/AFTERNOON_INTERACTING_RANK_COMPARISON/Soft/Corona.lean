import YM.Next.RANK.Vessel
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Spire
import YM.Primitives.CUBIC_GRADED_RATE.Booking
/-!
# Through the Clipped test on this P & X

From Next/RANK/Vessel etc., including its private-helper approach (adapted
to the soft tests).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Next.Rank Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {c : Course C N p k} {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}
variable (F : Nylon c P X R ξ)

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable {x : Points m} (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (v : Fin m→ C.label d) (Z : ∀ i, coin (O.W (v i))≤ ξ.principal (clim C.path.levels k))

private lemma note_bill (p : Perch.Shelf ξ.era.coast 2 (clim C.path.levels k) (clim C.path.levels i)) (h : (P i).p.B= Perch.walls (clim C.path.levels i)) :
    let A:= Peak.Meter C.path.levels h p
    A.m0= ξ.cash (clim C.path.levels k) ∧ A.m1=ξ.cash (clim C.path.levels k) ∧ A.e+1+A.spare=load ξ.era := by
  intro A; let L:= C.path.levels; let t:= clim L k
  have he:A.radius=bill (1/16) t:= by
    change Ship.allowance L 2 k=bill (1/16) t; rw [← packaged]; unfold powder;norm_num; rfl
  have hv:A.radius * Real.exp (-A.narrow)=ξ.cash t:= by
    rw [he]; unfold Purse.cash bill; rw [← ξ.hour,← Real.exp_add]; change Real.exp (boil t * _+ -(ξ.era.coast.U * boil t))= _; congr 1; ring
  exact ⟨hv, (by unfold Dock.Change.m1; rw [show A.inside=A.narrow from congr_arg (·*boil t) ξ.common]; exact hv), show ξ.era.coast.e+1+1=ξ.era.coast.e+2 by ring⟩

private lemma pays_low {V : Type*} [DecidableEq V] [Fintype V] {ζ : V→Site n} {r} {H : SourceAt G ζ} {T a c b}
    (h : H.pays T r a b) (hx : ∀ i,0< r i) (hp : c≤a) : H.pays T r c b:= by
  refine ⟨h.1,fun U he=>?_⟩
  apply le_trans _ (h.2 U he); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (debt_mono T.B hp H.extent) (Poly.worth hx _).le) (norm_nonneg _)

private lemma readyLast {ι κ V μ : Type} [Fintype ι] [Fintype κ] [Fintype V] [Fintype μ] [DecidableEq μ] [DecidableEq V] {s : ℝ}
    (h : (P i).p.B= Perch.walls (clim C.path.levels i)) (pF : Perch.Shelf ξ.era.coast 2 (clim C.path.levels k) (clim C.path.levels i))
    {ζ : μ × V → Site (C.side i p)} (H : ι→ SourceAt G ζ) (K : κ → Lifted G ζ (P i).p.threshold) (X : Value.Light (P i) H K
      (fun _=> ξ.cash (clim C.path.levels k)) (load ξ.era) s (Perch.gas ξ.era.coast (clim C.path.levels i)))
    (he : s ≤ Perch.bill (1-(ξ.goal:ℝ)) (clim C.path.levels k)) : Dock.Reception (Peak.Meter C.path.levels h pF) H K:= by
  let T:= P i; let A:= C.path.levels; let t:=clim A k; let y:= ξ.cash t; let J:= Meter C.path.levels h pF
  obtain ⟨hf,hv,hg⟩:= note_bill (C:=C) pF h
  obtain ⟨⟨w,hw,hc⟩,z,h₁,h₂⟩:= X
  have hy:0<y:= Real.exp_pos _
  refine ⟨⟨w,fun i=>?_,fun i=> ?_,fun i=>?_⟩,z,fun i=>?_,fun i=> h₂ _⟩
  · split
    · rw [hv]; exact pays_low (hw i) (fun _=> hy) (le_add_of_nonneg_right (by norm_num : 0 ≤ (2:ℝ)))
    rw [hf]; apply pays_low (hw i) (fun _=> hy); change ξ.era.coast.e+1≤ ξ.era.coast.e+2; linarith only
  · refine le_trans (sum_le_sum (g:=fun j=> if i∈(H j).fires.val then w j else 0) ?_) ((hc i).trans ?_)
    · intro t _; split_ifs with h h' hk <;> first | exact le_rfl| exact (hw t).1| exact False.elim (h' h.2)
    exact he.trans (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (boil_pos _) (by
      have ht : (6:ℝ)≤ ξ.goal:= by exact_mod_cast ξ.tolerance
      linarith)))
  · refine le_trans (sum_le_sum (g:=fun j=> if i∈(H j).fires.val then w j else 0) ?_) ((hc i).trans ?_)
    · intro t _; split_ifs with h h' hk <;> first | exact le_rfl| exact (hw t).1| exact False.elim (h' h.2)
    exact he.trans (Glimmer.billed t (show 1-(ξ.goal:ℝ) ≤ -(((2:ℕ):ℝ)*ξ.era.coast.V)-2 by push_cast; linarith only [ξ.warp]))
  rw [hf,hg]; exact h₁ _

include H he Z
lemma v_clinker (hn : m≤2) (ht : Awakening ξ (clim C.path.levels k) m (G:=G))
    (h : v_carried F O (x:=x) v (le_refl (middle C.path.levels ξ.band k)) (before ..)) :
    Atlas.Clipped ξ.band X O.heater c P x v c.allow ξ.taylor ξ.era.coast 2:= by
  intro hv hs
  let A:=C.path.levels;let l:=middle A ξ.band k; let Y:= clim A k; let z:= clim A l;let q:=ξ.era; let r:=q.coast; let g:=before A ξ.band k
  let T:=Ship.yard C ξ.band c.allow p; let D:=P l
  obtain ⟨α,β,hα,hβ,u,L,hL,hK,hp⟩:=h; let W:= mimics x v O F.paths c.allow g le_rfl (anneals C c l)
  let f : Tapes.Marquee C k ξ.band p ξ.horizon x g ≃ flame (Fin m):={
    toFun u:=tale u.val
    invFun i:=⟨(bulletin hn).symm i,snug he _ p _⟩
    left_inv i:=Subtype.ext ((bulletin hn).symm_apply_apply i.val)
    right_inv i:=(bulletin hn).apply_symm_apply i }
  let Λ:=Equiv.prodCongr (Equiv.refl (CellP C k ξ.band p)) f
  let WX (j:T.Cell×flame (Fin m)) := W (Λ.symm j)
  have hh (j:T.Cell×flame (Fin m)) : tale (Λ.symm j).2.val=j.2:= f.apply_symm_apply j.2
  refine ⟨α,β,hα,hβ,u,L,WX,readyLast hv hs _ _ hp (H.races.pos le_rfl).1,hK,hL.trans ?_,fun i=>?_,fun i U hU=>?_⟩
  · ext1 i; unfold Value.dust
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr];rw [Fintype.sum_equiv Λ (fun j=> (W j).amount D.p.threshold i) (fun j=> (WX j).amount D.p.threshold i) (fun j=> congr_arg (fun j=> (W j).amount D.p.threshold i) (Λ.symm_apply_apply j).symm)]; try rfl
  · let i':= Λ.symm i; have he₁:(WX i).fires=litWord p c.allow ξ.band C i.1 i'.2.val:= rfl
    have ht:(WX i).extent=dolmens x ξ.band r.Q (walls z) c.allow g i.1 i'.2.val:=rfl
    rw [ht,he₁]; unfold litWord; rw [show tale _=_ from hh i, doll c.allow he,← show D.p.B=walls z from hv ]; exact ⟨(by rfl),rfl⟩
  have hv' : D.p.B= walls z:=hv; obtain ⟨g',hg,hP⟩:= v_façade F O H he v Z hn ht i U ((congr_arg (Peak.route A ξ.band k p r.Q · i) hv') ▸ hU)
  refine ⟨g',hg,fun u=> ?_⟩
  let t:= (Λ.symm (i,u)).2; have hp:tale t.val=u:=hh (i,u)
  refine le_trans (le_of_eq ?_) (hP t); rw [hp]; rfl

omit H he Z
section phase
open Paint Vac.Numbers Read
variable {y : Points (m+1)} {e : ℝ} (H : C.Makes) (hp : C.ref d≤ k)

include F
lemma v_stir {w} (U : Launch C k ξ w e) (W : survivors C N k p U.pane (P k)) (he : Fit C.path.levels ξ.band k y) (s : Fin (m+1) → C.label d)
    (M : Boot k d ξ.taylor e m ξ.band ξ.f y s H) (hs : ξ.band*d+saves C d≤ ξ.credit) (hr : m+1 ≤ 2)
    (Y : Fin (m+1)→ C.label d) (hx : ∀ i,Price.Solves C (mag C.path.levels ξ.band k) d k N p O.T (s i) (Y i))
    (Z : Stake m y ξ.band c.allow Y H hp c (Hat (clim C.path.levels k)^e)) (V : Crew c P R ξ y) :
    Atlas.Clipped ξ.band X O.heater c P y Y c.allow ξ.taylor ξ.era.coast 2:= by
  obtain ⟨hZ,hu⟩:= M.parcel hp U.year c.allow c (P k) U.pane W O U.grant U.coup.heft he Y hx
  have hv:= U.coup; let t:=clim C.path.levels k; let p':= P k
  have hY i : coin (O.W (Y i)) ≤ ξ.principal (clim C.path.levels k):= (hZ i).trans (Glimmer.billed _ hs)
  refine v_clinker F O hv he Y hY hr (U.numbers _ hr) (v_keptUp F O Y hv he hr V hY ?_)
  simp only [v_carried]; rw [Nat.sub_self,Purse.epoch,pow_zero,one_mul,bootwarm C c c.allow]
  let f:= ξ.era.coast
  have ht: Perch.gas f t=Real.exp (-Paint.trib f.a t):=by unfold Perch.gas Paint.trib; ring_nf
  refine ht ▸ ?_
  exact marched c.allow c O F.paths y Y (F.fixture (before ..) (le_refl k)|>.budget) (hu Z)
end phase
end YM.PhysicalNext.InteractingRank.Soft
