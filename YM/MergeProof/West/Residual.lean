import YM.MergeProof.West.Beluga
import YM.MergeProof.West.Vroom
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition Filter
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points m} {ξ:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}
variable {V:Fin m→poly (Chamber G C.S k p)} (F:Ceremony ξ c P R Ψ)(H:Kith (A:=C.path.levels) V x ξ)
    (Q:Caff (G:=G) ξ (clim C.path.levels k) (k-middle C.path.levels ξ.band k) u m)

private lemma note_bill (p : Perch.Shelf ξ.era.coast u (clim C.path.levels k) (clim C.path.levels i)) (h : (P i).p.B= Perch.walls (clim C.path.levels i)) :
    let A:= Peak.Meter C.path.levels h p
    A.m0= loot ξ (clim C.path.levels k) u ∧ A.m1=loot ξ (clim C.path.levels k) u ∧ A.e+1+A.spare=load ξ.era := by
  intro A; let L:= C.path.levels; let t:= clim L k
  have he:A.radius=bill (1/(8*u:ℝ)) t:= by
    change Ship.allowance L u k=bill (1/(8*u:ℝ)) t; rw [← packaged]; unfold powder;rfl
  have hv:A.radius * Real.exp (-A.narrow)=loot ξ t u:= by
    rw [he]; unfold loot bill; rw [← Real.exp_add]; change Real.exp (boil t * _+ -(ξ.era.coast.U * boil t))= _; congr 1; unfold cashFt; ring
  exact ⟨hv, (by unfold Dock.Change.m1; rw [show A.inside=A.narrow from congr_arg (·*boil t) ξ.common]; exact hv), show ξ.era.coast.e+1+1=ξ.era.coast.e+2 by ring⟩

private lemma pays_low {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {ζ : V→Site n} {r} {H : SourceAt G ζ} {T a c b}
    (h : H.pays T r a b) (hx : ∀ i,0< r i) (hp : c≤a) : H.pays T r c b:= by
  refine ⟨h.1,fun U he=>?_⟩
  apply le_trans _ (h.2 U he); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (debt_mono T.B hp H.extent) (Poly.worth hx _).le) (norm_nonneg _)

include Q in
private lemma readyLast {ι κ V μ : Type} [Fintype ι] [Fintype κ] [Fintype V] [Fintype μ] [DecidableEq μ] [DecidableEq V] {s : ℝ}
    (h : (P i).p.B= Perch.walls (clim C.path.levels i)) (pF : Perch.Shelf ξ.era.coast u (clim C.path.levels k) (clim C.path.levels i))
    {ζ : μ × V → Site (C.side i p)} (H : ι→ SourceAt G ζ) (K : κ → Lifted G ζ (P i).p.threshold) (X : Value.Light (P i) H K
      (fun _=> loot ξ (clim C.path.levels k) u) (load ξ.era) s (Perch.gas ξ.era.coast (clim C.path.levels i)))
    (he : s ≤ Perch.bill (1-(ξ.goal:ℝ)) (clim C.path.levels k)) : Dock.Reception (Peak.Meter C.path.levels h pF) H K:= by
  let T:= P i; let A:= C.path.levels; let t:=clim A k; let y:= loot ξ t u; let J:= Meter C.path.levels h pF
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
    exact he.trans (Glimmer.billed t (show 1-(ξ.goal:ℝ) ≤ -((u:ℝ)*ξ.era.coast.V)-2  from Q.flare))
  rw [hf,hg]; exact h₁ _

private lemma e_snug (he:Fit C.path.levels ξ.band k x)(v:Manner m)(p a:ℕ): cosy C.path.levels x ξ.band p a (walls (clim C.path.levels (middle C.path.levels ξ.band k))) (before C.path.levels ξ.band k) v:=by
  intro i hi j hj; unfold core; rw [Station.at_stop he,Station.at_stop he,separation_self]; exact Nat.zero_le _
private lemma mulch (hN:k≤N)(he:Fit C.path.levels ξ.band k x)(v : Site (C.S.side (Station.width C.path.levels ξ.band k) p))(W B : ℕ)(T:Manner m) :d_olm (C:=C) x ξ.band W B hN (before ..) v T=Peak.route C.path.levels ξ.band _ p W B v:=by unfold d_olm readers; rw [he.stop]; rfl

/-- Supply compared P at l along Lead, actual curve coarse. -/
def Chast (P:(i:ℕ)→ Rep G (C.side i p))(c: Course C N p k)(Ψ:AtlasData G C.S p) (x:Points m) (V: Fin m → poly (Chamber G C.S k p))(ξ : Purse)(u:ℕ)(L :Config G (C.side N p)→ veil ((Ship.yard C ξ.band c.allow p).Cell × Fin m)):=
    let A:=C.path.levels
    let l:=middle A ξ.band k
    let t:=clim A k
    let h:= before A ξ.band k
    let T:=Ship.yard C ξ.band c.allow p
    let f:= readers (C:=C) (b:=ξ.band) (p:=p) x c.allow (h.trans c.allow)
    let B:= (P l).p
    let ψ:=Peak.route A ξ.band k p ξ.era.coast.Q B.B
    ∀ g : B.B=walls (clim A l),∀ hs : Perch.Shelf ξ.era.coast u t (clim A l),
      ∃ (α β : Type), ∃ (_ : Fintype α) (_ : Fintype β), ∃ (H : α → SourceAt G f) (K : β → Lifted G f B.threshold)
        (W : T.Cell × flame (Fin m) → SourceAt G f),
        Dock.Reception (Peak.Meter A g hs) H K ∧ Background (P l) K ∧
          c.flow L l (h.trans c.allow)=dust (P l) (Sum.elim H W) K ∧
          (∀ i,(W i).fires=sectionAt i ∧ (W i).extent=ψ i.1) ∧
          ∀ i U, Healthy B.threshold (ψ i) U →
          ∃ u : Chamber G C.S l p → ℝ, Wind A u (fraction m ξ.taylor t) ∧
            ∀ a : flame (Fin m), ‖(W (i,a)).value U-(Array.reorient T i (t_cum (track Ψ) V h u)).part a.val‖ ≤ Perch.bill (-3/2) t

lemma clasp (X:Config G (C.side N p)→veil ((Ship.yard C ξ.band c.allow p).Cell×Fin m))(h:leased F H Q (before ..) le_rfl X)(he: Fit C.path.levels ξ.band k x) : Chast P c Ψ x V ξ u X:= by
  intro hv hs
  let A:=C.path.levels;let l:=middle A ξ.band k; let Y:= clim A k; let z:= clim A l;let q:=ξ.era; let r:=q.coast; let g:=before A ξ.band k
  let T:=Ship.yard C ξ.band c.allow p; let D:=P l
  obtain ⟨α,β,hα,hβ,u0,L,hL,hK,hp⟩:=h; let W:= tapestry H Q g (le_refl l) F.sens c
  let f : ViewFt C k ξ.band p ξ.horizon x g ≃ flame (Fin m):={
    toFun u0:=tag u0.val
    invFun i:=⟨i,e_snug he _ p _⟩
    left_inv i:=by rfl
    right_inv i:=rfl }
  let Λ:=Equiv.prodCongr (Equiv.refl (CellP C k ξ.band p)) f
  let WX (j:T.Cell×flame (Fin m)) := W (Λ.symm j)
  have hh (j:T.Cell×flame (Fin m)) : tag (Λ.symm j).2.val=j.2:= f.apply_symm_apply j.2
  refine ⟨α,β,hα,hβ,u0,L,WX,readyLast Q hv hs _ _ hp (F.grant.races.pos le_rfl).1,hK,hL.trans ?_,fun i=>?_,fun i U hU=>?_⟩
  · ext1 i; unfold Value.dust
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr];rw [Fintype.sum_equiv Λ (fun j=> (W j).amount D.p.threshold i) (fun j=> (WX j).amount D.p.threshold i) (fun j=> congr_arg (fun j=> (W j).amount D.p.threshold i) (Λ.symm_apply_apply j).symm)]; try rfl
  · let i':= Λ.symm i; have he₁:(WX i).fires=litFt p c.allow ξ.band C i.1 i'.2.val:= rfl
    have ht:(WX i).extent=d_olm x ξ.band r.Q (walls z) c.allow g i.1 i'.2.val:=rfl
    rw [ht,he₁]; unfold litFt; rw [show tag _=_ from hh i, mulch c.allow he,← show D.p.B=walls z from hv ]; exact ⟨(by rfl),rfl⟩
  have hv' : D.p.B= walls z:=hv; obtain ⟨g',hg,hP⟩:= e_facade F H Q he i U ((congr_arg (Peak.route A ξ.band k p r.Q · i) hv') ▸ hU)
  refine ⟨g',hg,fun u0=> ?_⟩
  let t:= (Λ.symm (i,u0)).2; have hp:tag t.val=u0:=hh (i,u0)
  refine le_trans (le_of_eq ?_) (hP t); rw [hp]; rfl

lemma legion (hu:2≤u)(hx:Fit C.path.levels ξ.band k x)(E:Plessey ξ x c P R u) (L)(hp:leased F H Q (le_refl k) (before ..) L) : Chast P c Ψ x V ξ u L:=by
  have ht (j:ℕ) (h: j ≤ k) (he: middle C.path.levels ξ.band k ≤ j): leased F H Q h he L:=by
    induction h using Nat.decreasingInduction with
    | self=> exact hp
    | of_succ j hj IH=> exact galactic F H Q E hu hx he hj _ (IH (he.trans (Nat.le_succ j)))
  exact clasp F H Q L (ht _ _ _) hx
end YM.Next.Rank.Tapes.West
