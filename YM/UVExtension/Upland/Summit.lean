import YM.MergeProof.Summit
import YM.UVExtension.Upland.Noel

/-!
 # Public through fully analytic VACUUM & coupling. Incremental Acme upgrade.
 The same Family, every order; additional provisions **unconditional**.
 Consumer demonstrates e.g. the norm topology evaluated in the calibrated
 family, not an existence claim for a converging Bolt elsewhere.

 Physical marked insertions not handled by this file.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Upland
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec
open Next.UVStress
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology ContDiff BigOperators
variable {G: Gauge}

theorem acme (h:G.Simple)(b:ℝ)(hb:0<b):∃ C:Family G,C.Makes∧ Spec.Calibrated C ∧ Einstein h C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∀ (f:Extraction.Order),∃ (g:Extraction.Order) (T:Table C.book), (∃ s:Seed C (f.refine g) T, Maxwell.Ranks T s.kernel.spin)∧ (∃ (M:MaxwellData C)(I:IR (C:=C) T)(V:DiffPlan T), I.J≠0∧UV C (f.refine g) T V M I)∧ Nonempty (Final C (f.refine g) T):=by
    obtain ⟨C,hB,hC,hM,hW,hE,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.uv_noel h hb
    refine ⟨C,hM,hC,hE,hB,hW,fun f=>?_⟩
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=YM.MergeProof.Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    exact ⟨g,T,⟨s,hN⟩,⟨M,I,E,hI,p⟩,YM.MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩

open RG Wilson 
variable {C:Family G}
/-!
No restriction to periodic-in-UV or diagonal extraction.

Summability of
 budgets only eventual at the meaning.

Local uniform hol convergence
 `Arc.uv`.

Here for explicit actual-family use in lemmas, strip
 representation witnesses and assert the physically normalized E/K
 and β on all admitted levels have norm/sup limits (not just tests).

For the actual rep itself subtracts NO VAC divergent constant until
 valuation; `partition_eq` still true.
-/

def Normal (C: Family G)(m n N:ℕ): Tabernacle.Readings G (C.path.levels.budget m) (C.side m n):= Tabernacle.tuning (C.path.levels.budget m) (C.path.levels.clock.allowance m) (C.path.levels.clock.forcedAllowance m) ((C.path.rep N n m).activities.E,(C.path.rep N n m).activities.K)

lemma paid {h:G.Simple}(H:Einstein h C) (N p:ℕ): -- recorded reaching laureate ALL mesh+per
    ∃ (M:Metals G)(P:RG.Supply.Rolls M.p)(A:Alloy M P)(R:Roost.Factor A)(U:Spire.Uses R h), (U.Trial N p 0 (C.beta N p) ∧ A.B.bake.make (U.realBeat 0)=C.path):=by
    obtain ⟨M,P,A,R,T,S,hA,t,F,hc,-⟩:= H; subst C; refine ⟨M,P,A,R,S,?_,?_⟩
    · change S.Trial N p 0 ((T.history N p N).beta); rw [hA.atPeak]; exact S.terminates N p (Spire.Uses.centerP _)
    rw [← hA.atPeak]

lemma winding {h:G.Simple}(H:Einstein h C) (m p :ℕ): Arrives (Normal C m p) ∧ Arrives (fun N=> C.path.β N p m):= by
    obtain ⟨M,P,A,R,T,S,hA,t,F,h,-⟩:= H; subst C
    obtain ⟨he,h⟩:= Camp.artistry S p hA.crowns hA.fields 0 (Spire.Uses.centerP _) m
    constructor
    · apply he.copy; filter_upwards [eventually_ge_atTop m] with i hi; unfold Normal; change _=Tabernacle.tuning _ _ _ ((T.history i p m).activities.E,(T.history i p m).activities.K); rw [hA.atPeak]; rfl
    apply h.copy; filter_upwards with i; change _ = (T.history i p m).beta; rw [hA.atPeak]; rfl

-- downstream gold standard checkpoint proof consumer
lemma treetops (G:Gauge)(h:G.Simple) : ∃ (C:Family G)(f:Extraction.Order)(Q:Table C.book),Nonempty (Final C f Q) ∧ Einstein h C ∧ (∀ N p, (∫ U,(C.path.rep N p 0).eval U ∂prior G (C.side 0 p))=partition G (C.side N p) (C.beta N p))∧ ∀ m n,Arrives (Normal C m n)∧ Arrives (fun i=> C.path.β i n m):=by
   obtain ⟨C,hC,-,h,-,-,H⟩:= acme h 1 one_pos; obtain ⟨f,Q,hF,hP,hK⟩:= H Extraction.Order.full
   exact ⟨C,_,Q,hK,h,fun N p=> C.path.partition_eq hC.wilson N p 0 (Nat.zero_le _),fun i j=> winding h i j⟩
end YM.UVExtension.Upland
#print axioms YM.UVExtension.Upland.acme
#print axioms YM.UVExtension.Upland.Arc.finiteCut
#print axioms YM.UVExtension.Upland.treetops
