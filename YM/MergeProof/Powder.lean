import YM.Extra.FREE_DETECTOR_ALGEBRA.Vane
import YM.MergeProof.SteamW
import YM.MergeProof.Thrush
import YM.Next.RANK.Beam
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Star



/-! Vote-to-Rank. Stop after Seed (Basis, Spans, Cleaner, corrected, actual Rank matrix). -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {S:Table C.book} {D:Bin S} {F:Extraction.Order} {V : Push.Mark.Weave G} {Y Xf}
lemma savings (h:Scotia C V Y Xf) {Z} (ht:Projected Xf F D Z) (d:ℕ) : Detect.EquationCount D F d := by
   apply Filter.Eventually.frequently
   filter_upwards [] with u
   rw [← show Xf.step d= _ from (ht.same d).symm]
   let v:= bindP C V d u.1 u.2 (Y d u)
   rw [(show _=_ from (h.step d u.1 u.2).ker)]
   let W:= C.labels.level d; let T:= Maxwell.freeTable C.labels; let B:= Maxwell.equationIdeal G d
   have hg : T.null d=B.map W.coords.toLinearMap:=by
      ext x; obtain ⟨i,rfl⟩:= W.coords.surjective x
      change W.coords i∈ T.null d ↔ _
      have hh : W.coords i∈T.null d ↔ i∈B:= by
        have H := Maxwell.projectionExact C.labels (c:=W.coords i)
        rw [Extra.FD.no_residual] at H
        refine H.symm.trans ?_ ; simp only [Submodule.mem_bot]
        constructor
        · intro h; apply LinearMap.mem_ker.mpr
          have hh : Maxwell.observable G d ((C.labels.level d).coords.symm (W.coords i))=0 := congr_arg Subtype.val h
          rw [W.coords.symm_apply_apply] at hh; exact hh
        intro h; apply Subtype.ext
        change Maxwell.observable G d ((C.labels.level d).coords.symm (W.coords i))=0; rw [W.coords.symm_apply_apply]; exact h
      rw [hh]; exact ⟨fun hi=> ⟨i,hi,rfl⟩,fun ⟨j,h,hj⟩=> W.coords.injective (show W.coords j= W.coords i from hj) ▸ h⟩
   have he := LinearEquiv.finrank_eq (v.submoduleMap B)
   have hz := LinearEquiv.finrank_eq (W.coords.submoduleMap B)
   have ha : Module.finrank ℂ (T.Field d)+Module.finrank ℂ (T.null d) = Module.finrank ℂ (C.label d):= (T.null d).finrank_quotient_add_finrank
   have hz' : Module.finrank ℂ (T.null d)=Module.finrank ℂ B:=
      (congr_arg (fun L : Submodule ℂ (C.label d)=> Module.finrank ℂ L) hg).trans hz.symm
   rw [hz'] at ha
   change _ ≤ Module.finrank ℂ (B.map v.toLinearMap)+ Module.finrank ℂ (T.Field d)
   rw [← he, Nat.add_comm,ha]
lemma rated (M : C.Makes) (h:Scotia C V Y Xf) (hg:G.Simple) (hC:Wcmain C) (f:Extraction.Order)
    {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (he:Scrim C W u ψ φ δ (fly C.path.levels) r D)
    {O : HaarBudget G} (Q : ∀ d:ℕ,Tapes.Panel d) (H:∀ i:ℕ,0 ≤ generator G i)
    (J : ChartRatio G) {B:PhysicalNext.RankCovariance.Binding C}
    (hr:∀ i:ℕ, ∃ᶠ j:ℕ in atTop, let v:= (Q i).patronize C (H i); Tender v j ∧ Metering v O j (-3) ∧ (∃ l r, ShowHours J B (v.current j) j (-3) l r ∧ Vents B (v.current j) J l r j)) : ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (Z : ∀ d,ℕ → CoordMap C d) (T:Table C.book) (E:DiffPlan T), Projected Xf (f.refine g) R Z ∧ Base C (f.refine g) A L R T E ∧ ∃ s:Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin:=by
   obtain ⟨g0,S,L,hP⟩:= Extraction.crops M (hC.projects C f M)
   let F:= f.refine g0
   obtain ⟨g1,R,z,hX⟩:= include_projections S Xf (h.packed F); let G':= F.refine g1
   have h0 : RawLimits C G' S L:= Extraction.copy_down C F hP g1
   let X(d:ℕ): Columns C S d:= Extra.FD.vane C S (Extra.FD.recorded C.labels d) _ _ Extra.FD.vane_possible
   have ht (d:ℕ): ∃ Z : (X d).Trials, Market.Purchases Z:=by
      let Ξ := (Q d).patronize C (H d)
      obtain ⟨p⟩:=Next.Rank.Price.from_labels C (X d)
      have hx : ∃ᶠ k in atTop, Tender Ξ k∧ Metering Ξ O k (-3)∧ (∃ l r, ShowHours J B (Ξ.current k) k (-3) l r ∧ Vents B (Ξ.current k) J l r k)∧ LanternMarks M Ξ (X d) k:=by
        refine ((hr d).and_eventually (bursts C (O:=O) (e := -3) d M hg he.1 he.2 (X d) Ξ rfl le_rfl)).mono ?_
        rintro k ⟨⟨T,H,hV⟩,hh⟩; exact ⟨T,H,hV,hh H⟩
      obtain ⟨Z,h,hZ⟩:= Soft.wheeled M Ξ (X d) O p hg (Soft.cast_off B M J Ξ (X d) (w:=-3) hg hx)
      exact ⟨Z,hZ⟩
   choose U hU using ht
   obtain ⟨g,Y,p,hp,hS,⟨T,E,hE⟩,K⟩:= Beam.arriving_seed M (hC.projects C _ M) h0 R (fun i=> (hX.ready i (h.relay G' i))) (savings h hX) X U hU
   have hF := Tails.refine G' g; have hd := (K T E hE).1
   have ht : Base C (G'.refine g) S L R T E := ⟨M,hC.projects C _ M,fun i=>(hF.projected hX).ready i (h.relay _ i),p,hp,hE,Work.D05.answer M (hC.projects C _ M) hE.smooth hd.generic,hd.kernel⟩
   exact ⟨g0.refine (g1.refine g),S,L,R,z,T,E,hF.projected hX,ht,hd,Mark.thrush h (hF.projected hX) ht (X 0).H (Extra.FD.no_residual G)⟩
end YM.MergeProof.Accent
