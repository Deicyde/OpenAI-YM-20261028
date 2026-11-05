import YM.TraceExtension.Shelves.Shape
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Slate Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
open Next.UVStress Asymptotics
variable {S: Table C.book} (HE:S.Hierarchy)(hx:CellHyp C F)(hp:F.PointLimits C S) {Y:DiffPlan S}(hf:Y.Derivatives S)
section tensor
local notation "V₄"=> C.labels.level 4
local notation "V₅"=> C.labels.level 5
def Ard(d:ℕ)(m:Motion) : Module.End ℝ (S.Field d):= if m.2 then (conjQ HE.spin).comp (spinQ HE.spin m.1) else spinQ HE.spin m.1
lemma Ard_image(m:Motion)(x:C.label d): S.project d (Prism (C.labels.level d) m x)= Ard HE d m (S.project d x):=by
    rw [Ard]; change S.project _ (Motion.patch _ _ _)=_; unfold Motion.patch;split_ifs with h
    · change _= S.conj HE.spin d (S.mirror HE.spin d m.1 (S.project d x)); rw[Table.mirror_project,Table.conj_project]
    change _= S.mirror HE.spin d m.1 (S.project d x); exact (Table.mirror_project ..).symm
lemma portrait_4(x:Axis→ Axis→ C.label 4)(a b:Axis): S.project 4 (Plot (Prism V₄) x a b)=Plot (Ard HE 4) (fun i j=> S.project 4 (x i j)) a b:=by
    let Y:=(S.project 4).restrictScalars ℝ; rw[plotEq,plotEq]; change Y _=_; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (Y.map_smul _ _).trans (congr_arg ((rent*hued i a*hued i b) • · ) (Ard_image HE _ _))
lemma portrait_5(x:Axis→ C.label 5)(a:Axis): S.project 5 (Reed (Prism V₅) x a)= Reed (Ard HE 5) (fun i=> S.project 5 (x i)) a :=by
    let Y:=(S.project 5).restrictScalars ℝ; rw[reedEq,reedEq]; change Y _=_; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (Y.map_smul _ _).trans (congr_arg ((rent*hued i a) • · ) (Ard_image HE _ _))
lemma Ard_der(o:Y.Orientation HE.spin)(m:Motion)(a:Axis)(v:S.Field d): Ard HE (d+1) m (Y.deriv d a v)=StressFlux.sign m.1 a • Y.deriv d (m.1.perm a) (Ard HE d m v):=by
   unfold Ard; cases hx:m.2; · exact deriv_mirror _ o ..
   change conjQ HE.spin (S.mirror HE.spin _ _ _)=_ • Y.deriv d _ (S.conj HE.spin _ _); rw [deriv_mirror Y o, (conjQ HE.spin|>.map_smul ..)]; exact congr_arg ((StressFlux.sign m.1 a) • · ) (o.realDer d (m.1.perm a) (S.mirror HE.spin d m.1 v))
lemma led(o:Y.Orientation HE.spin)(m:Motion)(a:Axis)(v:S.Field d): Y.deriv d a (Ard HE d m v)=hued m a • Ard HE (d+1) m (Y.deriv d (prev m a) v):= by rw[Ard_der HE o, show m.1.perm (prev m a)=a from m.1.perm.apply_symm_apply a]; exact (sign_sign m.1 (prev m a) _).symm
set_option maxRecDepth 4096 in
lemma primary_nab(o:Y.Orientation HE.spin)(v:S.Stress)(b:Axis): nabla Y (Plot (Ard HE 4) v) b = Reed (Ard HE 5) (nabla Y v) b:=by
    unfold nabla; rw [reedEq]; let Gm(i:Motion)(a:Axis):= (rent*hued i a*hued i b) • Ard HE 4 i (v (prev i a) (prev i b));
    have hm(a:Axis):Y.deriv 4 a (Plot (Ard HE 4) v a b)=∑ i:Motion,Y.deriv 4 a (Gm i a):=by rw[plotEq,map_sum];
    rw[Finset.sum_congr rfl (g:=fun a=>∑ i:Motion,Y.deriv 4 a (Gm i a)) (fun a _=>hm a),Finset.sum_comm]; apply Finset.sum_congr rfl fun i _=>?_ ; rw [map_sum,Finset.smul_sum]; refine Fintype.sum_equiv i.1.perm.symm _ _ fun a=> ?_
    unfold Gm; rw [show Y.deriv 4 a ((_:ℝ) • _)= (_:ℝ) • Y.deriv 4 a _ from ((Y.deriv 4 a).restrictScalars ℝ).map_smul _ _,led HE o,smul_smul]; congr 1; unfold hued; linear_combination (norm:=ring) rent*sign i.1 (prev i b) * sign_sq i.1 (prev i a)
def inter {E:Type*}[AddCommGroup E][Module ℝ E](f:Axis→Axis→E)(a b:Axis):E:= (1/2:ℝ) • (f a b + f b a)
lemma inter_link(f:Axis→Axis→ C.label d) (a b:Axis): S.project d (inter f a b)=inter (fun i j=> S.project d (f i j)) a b:=by let L:=(S.project d).restrictScalars ℝ; unfold inter; rw [show ∀ (x:C.label d), S.project d ((1/2:ℝ) • x)=(1/2:ℝ) • S.project d x from fun x=> L.map_smul _ _,map_add]
lemma inter_sym {E:Type*}[AddCommGroup E][Module ℝ E](f:Axis→Axis→E)(a b:Axis): inter f a b=inter f b a:=by unfold inter; rw[add_comm]
lemma inter_unit {E:Type*}[AddCommGroup E][Module ℝ E](f:Axis→Axis→E)(a:Axis): inter f a a=f a a:=by unfold inter; module
-- conversion.Kernel
variable {L:PaceBook C}
def press (L:PaceBook C)(k:ℕ):= Plot (Prism V₄) (inter (StormP C L k))
def baron(S : Table C.book) (L:PaceBook C)(k:ℕ)(a b:Axis):= centering S 4 (S.project 4 (press L k a b))
lemma stitch_k(L:PaceBook C)(k:ℕ): baron S L k∈ KernelSpace HE.spin:=by
    let H:= inter (StormP C L k); let T':Cone V₄ := ⟨ Plot (Prism V₄) H,shard V₄ H (inter_sym _)⟩; let F:= ((centering S 4).comp (S.project 4)).restrictScalars ℝ
    let U:= tensorMap (K:=reflA V₄) (D:=spinQ HE.spin) (R:=reflB V₄) (T:=conjQ HE.spin) F (by intro s x; change centering S 4 (S.project 4 (reflA V₄ s x))=S.mirror HE.spin _ _ (centering S 4 _); rw [show S.project 4 (reflA V₄ s x)=S.mirror HE.spin _ s _ from (Ard_image HE (s,false) x), mirror_center HE]) (fun x=>by change centering S 4 (S.project 4 (star _))= S.conj HE.spin _ (centering _ _ _); rw[conj_center HE, Table.conj_project])
    have hp: baron S L k∈ TableTwo HE.spin:= (U T').property; refine ⟨?_,fun i j=>centers_field HE.laws _⟩; exact (sym_mem.mpr ⟨hp.1,hp.2.1,raw_eq hp⟩)
end tensor
end YM.Trace.Shelves
