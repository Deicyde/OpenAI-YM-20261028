import YM.MultipleContact.FieldBound
import YM.MultipleContact.Tests

/-! Taylor prescription at total collapse starting from a function on the puncture (e.g. any comparable pair).
Existence interface includes arbitrary normal tests. Partial diagonals need additional recursive constructions beyond this estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Power
open Function Filter MeasureTheory Set TopologicalSpace Metric Table Direct Analysis Extraction
open scoped Topology BigOperators ContDiff Distributions Classical
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E]
 [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
variable {G : Gauge} {L:Register G} {S:Table L} {P:DiffPlan S}

variable (B:Splitting P) (D:∀ h,Detector S h)
variable {R:ℝ} {σ Hmax k:ℕ} {A:Set (Target L)}

def critical (σ:ℕ) (E:Type*)[AddCommMonoid E][Module ℝ E] : ℕ:=σ-Module.finrank ℝ E

def piece (Y:Target L→E→ℂ)(k i:ℕ) : Target L→E→ℂ:= centerRead i (fun y=>B.part i k (readField D Y k y))

def primary (R s:ℝ)(m:Option ℕ)(Y:Target L→E→ℂ)(f:E→ℂ)(t:Target L) :ℂ:=term R s m (Y t) f
/-- Exact power counting at total collapse in dimension `Module.finrank ℝ E`. -/
def rule (R s:ℝ)(σ:ℕ)(Y:Target L→E→ℂ)(t:Target L)(f:E→ℂ):ℂ:=
    if Module.finrank ℝ E ≤ σ then primary R s none (miss D (critical σ E) Y) f t +
                               ∑ i:Fin (critical σ E+1), primary R s (some (critical σ E-i.val)) (piece B D Y (critical σ E) i.val) f t
    else primary R s none Y f t

structure Admitted (A:Set (Target L)) (R:ℝ) (m:Option ℕ) (Z:Target L→E→ℂ) where
   power : ℝ
   cost : ℝ
   live : -(Module.finrank ℝ E:ℝ)< power + price m
   estimates t : t∈A→ Kas R power cost (Z t)

variable {B D} {Y:Target L→E→ℂ} (H:Estimates P D σ Hmax R Y A)
include H
lemma pieceAdmitted (hk:k=critical σ E)(hK:Module.finrank ℝ E ≤ σ)(h:k≤Hmax)(i:Fin (k+1)):
   Nonempty (Admitted A R (some (k-i.val)) (piece B D Y k i.val)) :=by
    obtain ⟨c,γ,hγ,_,he⟩:=piecePrice H B i.val (Nat.le_of_lt_succ i.isLt) h
    obtain ⟨c,hc,hc'⟩:= centerPrice H (by omega : i.val ≤ Hmax) he
    refine ⟨_,_,?_,hc'⟩
    unfold price; push_cast [Nat.cast_sub (R:=ℝ) (show i.val≤k by exact Nat.le_of_lt_succ i.isLt)]; unfold critical at hk
    have hm:= congr_arg (fun n:ℕ => (n:ℝ)) hk; rw [Nat.cast_sub (R:=ℝ) hK] at hm; linarith
lemma signedAdmitted {k:ℕ} (hk:σ≤Module.finrank ℝ E+k)(h:k≤Hmax): Nonempty (Admitted A R none (miss D k Y)):=by
    obtain ⟨c,γ,hγ,he⟩:= H.signed k h
    exact ⟨_,_,by unfold price; push_cast; exact (by linarith [show (σ:ℝ)≤Module.finrank ℝ E+k from by exact_mod_cast hk]),he⟩
lemma basicAdmitted (hk:σ<Module.finrank ℝ E):Nonempty (Admitted A R none Y):=by
    obtain ⟨c,he⟩:= H.grow (1/2) (by norm_num)
    exact ⟨_,_,by simp only [price,Nat.cast_zero]; exact (by linarith [show (σ:ℝ)+1 ≤ Module.finrank ℝ E from by exact_mod_cast hk]),he⟩
variable (hd:1≤ Module.finrank ℝ E)
namespace Admitted
open TestFunction
variable {V:Target L→ E→ℂ} {m:Option ℕ} (v:Admitted A R m V)
include hd v in
omit H in
lemma valid (s:ℝ)(hs:0<s) (t:Target L)(ht:t∈A) (f:E→ℂ)(hf:ContDiff ℝ ∞ f)(hc:∃C,JetBounds (price m) f C):
    IntegrableOn (fun x=>diff s m f x • V t x) (ball 0 R):=(localPair hd (v.estimates t ht) hf hc.choose_spec hs v.live).1

omit H in
def dist (s:ℝ)(hs:0<s)(t:Target L)(ht:t∈A) (U:Opens E) : 𝓓(U,ℂ)→L[ℂ]ℂ:= Direct.functional hd (v.estimates t ht) s hs m v.live
omit H in
lemma activate (s:ℝ)(hs:0<s)(t:Target L)(ht:t∈A) (U:Opens E)(f:𝓓(U,ℂ)):dist hd v s hs t ht U f = primary R s m V f t :=rfl
end Admitted

def patch {s:ℝ} (hs:0<s)(hw:critical σ E≤Hmax)(t:Target L)(ht:t∈A) (U:Opens E):𝓓(U,ℂ)→L[ℂ]ℂ :=if hk : σ≥Module.finrank ℝ E then
   let n:= critical σ E
   let v : Admitted A R none (miss D n Y):= (signedAdmitted H (by change σ≤Module.finrank ℝ E+critical σ E; unfold critical; omega) hw).some
   let w (i:Fin (n+1)) : Admitted A R (some (n-i.val)) (piece B D Y n i.val) := (pieceAdmitted H rfl hk hw i).some
   v.dist hd s hs t ht U + ∑ i:Fin (n+1), (w i).dist hd s hs t ht U
  else (basicAdmitted H (by omega)).some.dist hd s hs t ht U
lemma patch_on {s:ℝ} (hs:0<s)(hw:critical σ E≤Hmax)(t:Target L)(ht:t∈A) (U:Opens E)(f:𝓓(U,ℂ)):patch (B:=B) H hd hs hw t ht U f= rule B D R s σ Y t f:=by
  rw [patch,rule]; split_ifs
  · dsimp only
    simp [add_apply, sum_apply,Admitted.activate]
  exact Admitted.activate ..
omit H in
private lemma jets_off {f:E→ℂ} (hf:0∉tsupport f)(m:Option ℕ)(s:ℝ):diff s m f=f:=by
    cases m with
    | none=>rfl
    | some m=>
       have he(i:ℕ):iteratedFDeriv ℝ i f 0=0 := notMem_support.mp (show (0:E)∉Function.support (iteratedFDeriv ℝ i f) from fun hd=>hf (support_iteratedFDeriv_subset i hd))
       ext1 x; simp [diff,polyJet,coeff,he]

include H in
lemma extend_eq {s:ℝ} (hs:0<s)(hw:critical σ E≤Hmax)(t:Target L)(ht:t∈A) (U:Opens E)(f:𝓓(U,ℂ)) (h0:0∉tsupport f)(hR:tsupport f⊆ball 0 R):
      patch (B:=B) H hd hs hw t ht U f=∫ x:E, f x * Y t x:= by
   rw [patch_on]; let k:=critical σ E; unfold rule; split_ifs with he
   · obtain ⟨v⟩:=signedAdmitted H (by change σ≤Module.finrank ℝ E + k; unfold k critical; omega) hw
     let w(i:Fin (k+1)) := (pieceAdmitted (B:=B) H rfl he hw i).some
     have hv:= v.valid hd s hs t ht f f.contDiff (has_bound f _)
     have hW(i) := (w i).valid hd s hs t ht f f.contDiff (has_bound f _)
     simp_rw [jets_off h0] at hW; change IntegrableOn (fun x:E=>f x • _) _ at hv
     suffices h':primary R s none (miss D k Y) f t + ∑ i:Fin (k+1),primary R s _ _ f t=∫ x in ball 0 R,f x * Y t x by rw [h',setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=> ?_)]; exact mul_eq_zero_of_left (notMem_support.mp (fun hp=>hx (hR (subset_tsupport _ hp)))) _
     change _=
       ∫ x in ball 0 R,f x • Y t x
     unfold primary; simp_rw [term,jets_off h0]; rw [← integral_finsetSum _ (fun i _=>hW i)]; rw [← integral_add hv (integrable_finsetSum _ fun i _=>hW i)]
     apply setIntegral_congr_fun isOpen_ball.measurableSet
     intro x hx
     simp_rw [← Finset.smul_sum,← smul_add]; apply congr_arg (f x • ·)
     let z:= readField D Y k x
     have hh : (∑ i:Fin (k+1), piece B D Y k i.val t x)=response t.1 k t.2 z := by
       rw [← B.recombine H.symmetric H.respects k z,map_sum]
       apply Finset.sum_congr rfl; intro i _
       exact (H.inherit t ht i.val k _ _).symm
     rw [show miss D k Y t x=Y t x - response t.1 k t.2 (z) from rfl,hh,sub_add_cancel]
   change (∫ x in ball 0 R,f x* Y t x)=_; rw [setIntegral_eq_integral_of_forall_compl_eq_zero]; exact fun x hx=> mul_eq_zero_of_left (notMem_support.mp (fun hp=>hx (hR (subset_tsupport _ hp)))) _
end YM.MultipleContact.Power
