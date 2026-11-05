import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Bid.Drops
import YM.Next.RANK.Patchable
import YM.Next.RANK.Pin
import YM.Next.RANK.Ray
import YM.Next.RANK.Stepped

/-!
# Single calibration after moving its ancilliary slot

Work on EACH flag inventory. Pay the actually chosen coefficient delivered by
`.Based`. For constructor of RRaw/RMixed still needs to deliver it AS THIS
singleton representation with others combined at higher marker modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells 
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V : Type} [DecidableEq V] [Fintype V]
variable {F : PathData G}

-- Need invariant exponent before density even though final density matches actual Wilson.

lemma base_at (p : BudgetPoint) (c : Clip) (U : Config G n) (x : Face (Per n)) :
    F.baseTerm c p U x= F.baseTerm c p (pull 1 x.1 U) (0,x.2) := by
  rcases x with ⟨x,i⟩
  unfold PathData.baseTerm; dsimp only
  have he : Face.send 1 x (0,i)=(x,i):= by
    unfold Face.send Face.lower; simp [atFace,posDir,affine,PlaqAxes.rotate,PlaqAxes.ordered,i.property.le]
  simp only [keeper_shift,ell_shift,Face.send_price U (0,i) 1 x G.chord G.chord_inv (fun k g=>G.chord_conj g k), he]

lemma exponent_rag (F : PathData G) (p : BudgetPoint) (c : Clip) (b : ℝ) (U : Config G n) :
    let f:=fun U : Config G n=> b*((∑ i, F.baseTerm c p U (0,i))+(PathData.atomSeries F.cubic p U 0+PathData.atomSeries F.quartic p U 0))+PathData.atomSeries F.loop p U 0
    F.inChannels c p b U=rag f U:= by
  intro f; unfold PathData.inChannels rag; apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·)
  apply Finset.sum_congr rfl; intro i _; apply Eq.trans _ (spin_shift f U i)
  let V := pull i 0 U
  have ht (x : Site n) p' (F : ℕ→Atom G p') : PathData.atomSeries F p V x= PathData.atomSeries F p (pull 1 x V) 0 := tsum_congr fun i=> (atoms ..).symm
  have hh : F.principal c p b V=∑ x,f (pull 1 x V):= by
    unfold f; rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_add_distrib]; unfold PathData.principal
    have hX:Fintype.card (Site n)=n.val^4:=site_card n
    refine congr_arg₂ (· + ·) (congr_arg (b*·) (congr_arg₂ (·+·) ?_ ?_)) ?_
    · refine (Fintype.sum_prod_type ..).trans (Finset.sum_congr rfl fun i _=> ?_); refine Finset.sum_congr rfl fun j _=> base_at _ _ V (i,j)
    · apply Finset.sum_congr rfl; intro i _; exact congr_arg₂ (·+·) (ht i _ F.cubic) (ht i _ F.quartic)
    apply Finset.sum_congr rfl; intro i _; exact ht ..
  exact hh

lemma rag_rip (F : Config G n→ℝ) (s : Signed) (x : Site n) (U) : rag F (pull s x U)=rag F U:= by
  apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·); refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ (fun i=> Fintype.sum_equiv (sends s x) _ _ fun j=>?_)
  exact congr_arg F (pull_pull s i x j U)

lemma expSym {σ c Λ δ w} (H : Q.Lawful σ c Λ δ w) (s : Signed) (x : Site n) : Q.exponent ∘ pull s x= Q.exponent:= by
  ext U; change Q.exponent _= _; obtain ⟨P⟩:= H.labels.moves s x
  unfold Rep.exponent; rw [exponent_rag,rag_rip,← exponent_rag]
  unfold Activities.additive; nth_rw 2 [← P.ep.tsum_eq]; apply congr_arg; apply tsum_congr; intro i; rw [← Alarm.comp_turn (u:=s) (P:=P) Q.activities]

lemma s_extra (a b : veil V) : (a*b).part (quiet V)=a.part (quiet V)*b.part (quiet V):= by rw [Glyph.part_mul]; simp [quiet, Census.quiet]
lemma mul_solo (a b : veil V) (i : V) : (a*b).part (slot i)=a.part (quiet V)*b.part (slot i)+a.part (slot i)*b.part (quiet V):= by
  have hp : (Finset.powerset ({i}:Finset V))={∅,{i}}:=by ext;simp [Finset.subset_singleton_iff]
  rw [Glyph.part_mul]; simp [slot,Census.fire,scene,quiet,Census.quiet,hp]
lemma selectMode (F : veil V) (h : F.part (quiet V)=0) (i : V) : (Poly.pass F).part (slot i)= F.part (slot i):= by
  have ht : (slot i: modes V)≠quiet V:= by simp only [slot,quiet,Census.fire,Census.quiet,ne_eq,Subtype.ext_iff];simp
  unfold Poly.pass; rw [Poly.part_sum,Finset.sum_eq_single 1]
  · simp
  · intro b _ hq
    by_cases hb:b=0
    · rw [hb]; simp [ht]
    rw [Poly.part_smul,Poly.high F h b _ ?_,mul_zero]; change ({i}:Finset V).card< _; rw [Finset.card_singleton]; omega
  intro hp; exfalso; have : Nonempty V:=⟨i⟩; exact hp (Finset.mem_range.mpr (by simpa using Fintype.card_pos (α:=V)))

def attached {ζ : V→Site n} {τ : ℝ} (K : Lifted G ζ τ) : Baler.Neat n := ⟨(K.extent,K.inventory),K.needed,K.records⟩

lemma gather_plate {ι : Type} {ζ : V→Site n} {τ : ℝ} (K : ι→Lifted G ζ τ) (U : Config G n) (p : Finset ι) : Lifted.pack K p U=Baler.peeled (fun i=> attached (K i)) (fun i=> (K i).amount U) (flags τ U) p := by
  unfold Lifted.pack Baler.peeled; split_ifs<;> first|rfl| contradiction

-- base record special for old unmarked gas (value equality per group)
structure IsoVac (B : Rep G n) (R : Baler.Neat n → Baler.Burst G n B.p.threshold) (w : ℝ) : Prop where
  points i : (R i).city=i
  smooth : Baler.SumHit (p:=B.p) R B.p.supportExponent w
  value i U : (R i).value U=∑' j,if Baler.locator (B.activities.forced j)=i then B.activities.K j U else 0
  symmetry : Baler.Rhythm R
  gas U : B.activities.gas B.p U=∑ i,Baler.placed R i U
lemma somebody {σ c Λ δ w} (H : Q.Lawful σ c Λ δ w) : ∃ R,IsoVac Q R w:= by
  let F:= Baler.orig Q.activities Q.p H.labels.forced
  have ht:=(Baler.old_cost H.labels)
  choose R hr he using Baler.prepare F
  refine ⟨R,hr,Baler.maintain F ht Q.p.exponent_pos.le R hr he,he,Baler.hymn F (Baler.old_hymn H.labels) R hr he,fun U=>?_⟩
  unfold Activities.gas; simp_rw [Baler.gas_at Q.activities Q.p H.labels.forced]; unfold Baler.placed
  let Y:=fun i=>(F i).city
  let P i:=(F i).value U
  have hz: Summable P:= Baler.summable_present F ht Q.p.exponent_pos.le U
  have hx:=((Activities.gasSeries H.labels).summable U).congr (fun i=>Baler.gas_at _ _ H.labels.forced i U)
  have ha (i) : Summable fun j=> if Y j=i then P j else 0 := by
    refine (hz.indicator (s:={x|Y x=i})).congr fun j=> ?_; by_cases h:Y j=i<;>simp [Set.indicator,h]
  change (∑' i,Baler.peeled Y P _ i)=_
  rw [Baler.all Y P _ hx ha]; exact (congr_arg₂ (fun x p=>∑ i,Baler.peeled x p (flags Q.p.threshold U) i) (funext hr).symm (funext (show ∀ i,Baler.piece Y P i= (R i).value U from fun i=>(he i U).symm)))
end YM.Next.Rank.Edition
