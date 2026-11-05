import YM.MergeProof.Buys
import YM.MergeProof.Close
import YM.MultiNext.VACUUM_STABILITY.Localized.Cascade
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Local Extra.Multi Source
variable (A:Activities G n)(P:BudgetPoint)(B:Census V)
variable {o: V→Site n}
    {u b c d t v : ℝ} (h:A.Valid P b c)
    (w:V→ℝ)(hw:∀ i,0<w i)
include h

def exclaim (x:Box n)(U:Config G n):Poly B:= bar A B U x
def muteF (U:Config G n)(i:ℕ):Poly B:= Poly.send B.quiet (↑(A.K i U):ℂ)
lemma mom (U : Config G n): Summable (fun i=>muteF A B U i):=by
   let w(V:V):=(1:ℝ); have he:Summable (fun i=> Poly.price w (muteF A B U i)):=by simp only [muteF,Poly.solo,Complex.norm_real,Poly.quiet_toll,one_mul]; exact (mass_crest A h U).norm
   exact (Poly.budgeted (w:=w) (fun _=>zero_lt_one) he (fun _=>le_rfl)).1
lemma gathers : exclaim A B=tally (barcode A) (fun i U=>muteF A B U i):=by
   funext i U; ext j; unfold tally; rw [Poly.share (f:=fun x:{ x // barcode A x=i}=> muteF A B U x.val) ((mom A P B h U).comp_injective Subtype.val_injective)]
   by_cases ht:j=B.quiet<;>simp [muteF,exclaim,bar,profile,cram,Poly.bead,ht]
lemma granular (i:Box n) : Flow o i (exclaim A B i) P.threshold:=by
   rw [gathers A P B h]; apply transitK (barcode A) (r:=id) _ (fun U=> mom A P B h _) i; intro i
   let F:= A.forced i; let b:= h.forced
   refine ⟨⟨fun V U hp ht=> congr_arg (fun v:ℝ=> Poly.send B.quiet v) (b.reads i V U hp ht),fun t U=>congr_arg (fun v:ℝ=> Poly.send B.quiet v) (b.sym i t U),fun q=>?_,fun i=>scope_send _ _ _ (by simp [Census.quiet])⟩,fun U hv=>⟨?_,F.inventory_ne,F.inventory_sup⟩⟩
   · unfold muteF; simp_rw [Poly.part_send]; split; exact Complex.continuous_ofReal.measurable.comp (b.meas _); exact measurable_const
   exact (b.permit i U (fun h=> hv (by rw [muteF,h];simp))).1
include hw
lemma vacant : Towed w Prod.fst (exclaim A B) P.B P.supportExponent c:=by
   rw [gathers A P B h]; apply towing (barcode A) _ ?_ hw; obtain ⟨f,hf,hp⟩:= h.boundK
   refine ⟨f, Activities.summable_charge (fun i=>(A.forced i).inventory_ne.mono (A.forced i).inventory_sup) (fun i=>(hf i).1) hp, fun i=> ?_, fun i=>?_⟩
   · refine Extra.Multi.Budget.mono (hp i) (fun i=>?_) (fun j=>?_) le_rfl
     · split;exact mul_nonneg (hf ..|>.1) (Real.exp_pos _).le;rfl
     split
     next h=> exact (mul_comm ..).le.trans (if_pos (show i∈ (A.forced j).support from h)).symm.le
     next h=> exact (hp _).1 j
   have ht:= satin (Complex.ofReal ∘ A.K i) B.quiet (f i) (w:=w) (hf i).1 (fun V=> (Complex.norm_real _).le.trans (hf i |>.2 V))
   simpa only [muteF, Poly.quiet_toll,Function.comp_apply,one_mul] using ht
omit hw in
lemma hawk (U:Config G n) : field (fun i=> exclaim A B i U) (flags P.threshold U)= Poly.bead B (A.gas P U):=by
   ext i; by_cases hq:i=B.quiet
   · rw [hq]; simp only [Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.part_send, ↓reduceIte]; apply stage₀ A P U (mass_crest A h U) _; intro i; unfold exclaim bar; exact (Poly.part_send ..).trans (if_pos rfl) -- syntax
   simp only [Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.part_send,if_neg hq]
   unfold field; rw [Poly.part_sum]; refine sum_eq_zero fun p _=> ?_; unfold grid; split; next=> unfold exclaim bar; rw [← map_prod]; exact (Poly.part_send ..).trans (if_neg hq)
   next=> rfl
omit h hw

variable {A} (R: Rep G n) (F:V→ Config G n→ℂ)
def birth (U:Config G n):Poly B:= (R.eval U:ℂ) • Poly.pass (Mach B (fun i=>F i U))
local notation "J"=> R.activities
local notation "P₀"=> R.p
variable (hp:R.activities.Valid R.p b c)
include hp
lemma starting : birth B R F=play R B (exclaim R.activities B) (fun U=>Mach B (fun i=>F i U)):=by
   funext U; unfold birth play; rw [hawk _ _ _ hp U, mul_comm,Poly.product_bead,← mul_smul, ← Complex.ofReal_mul]; rfl
omit hp
lemma boot (U) i : (birth B R F U).part (B.fire i)= (R.eval U:ℂ)* F i U:=by unfold birth; rw [Poly.part_smul, whisper _ _ (mute B _),sing]

include hp hw
lemma unveiled {M:ℕ} {L:V→ Config G n→ℂ}{K:V→ℕ→ Config G n→ℂ} (χ:V→MergeProof.Response G n)(hb:Garnish R.p o χ w t u)(hv:Occupancy o M)(hu:0 ≤ u)
     (hX:t ≤ R.p.supportExponent) (hd:0≤d)(he:((R.p.B + R.p.B + 1:ℕ):ℝ)^4 * (c+M*siteFactor R.p.B*u) ≤ t-d)
     (hk:Real.exp (c+M*siteFactor R.p.B*u)-1 ≤ v)(hit:∀ U,R.eval U≠0)(hV: 0 ≤ v)
     (hC:∀ i,Dominated (K i)) (h':∀ i,hook R.activities R.p.threshold (χ i) =profile R.activities (K i))
     (hT:∀ i U,(R.eval U:ℂ)*F i U=coin R (L i) (K i) U): Served R L (fun i=>profile R.activities (K i)) (birth B R F) o w d v :=by
    let K':= exclaim J B; let X:= fun U=> Mach B (fun i=> F i U); let H : Support n→ Config G n→Poly B:=fun _ _=>0
    have hf: ∀ i, Burns o i (H i) (P₀).threshold := fun i=> ⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun _ h=>False.elim (h rfl),fun _=> rfl⟩
    have hh : Towed w id H (P₀).B (d+0) v:=by
       refine ⟨0,Summable.of_finite,fun i=> by simp [SumBudget,hV],fun i=> ⟨0,le_rfl,fun U p=> ?_,?_⟩⟩
       · rw [show H i U=0 from rfl,Poly.part_nil,norm_zero]; rfl
       unfold wordsPrice; simpa using hV
    have hg:=starting B R F hp -- order
    rw [hg]; apply closeup R χ K' X hb (granular J P₀ B hp) (fun i U=> (Poly.part_send ..).trans (if_pos rfl)) hp (a:=1) (H:=H) (fun U=>mute B _) ?_ hw hu hv hf hh ((vacant J P₀ B hp w hw).shrink hX le_rfl hw) (by ring) (show 0 ≤ d+0 from by simpa) he hw ?_ zero_le_one ?_ ?_ ?_ ?_ hC hit
    · intro U i h; unfold X; rw [hush _ _ h]; simp [H]
    · simp [Repegs]
    · rw [one_mul]
    · rwa [one_mul]
    · intro i j U; change (Poly.send B.quiet _).part _+_= _; rw [Poly.part_send,if_neg (B.fire_hot j),zero_add,h']
    intro i U; exact congr_arg (fun i'=> (i' U).part (B.fire i)) hg.symm|>.trans ((boot _ _ _ _ _).trans (hT ..))
end YM.MergeProof.Accent
