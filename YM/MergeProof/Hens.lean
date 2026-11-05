import YM.MergeProof.Grant
import YM.MergeProof.Stretch

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open Local Extra.Trajectories Source
variable [Fintype V] (A:Rep G n) (B:Census V)
-- pointwise any prescribed linear displacement. Not use fixed d.
def coin (F:Config G n→ℂ) (K:ℕ→Config G n→ℂ) (U:Config G n):ℂ:= ((A.eval U:ℝ):ℂ)*F U+ (Real.exp (A.exponent U):ℂ)*∑' i,nickel A.p A.activities i U (fun j=>K j U)
lemma coin_primary {d:ℕ}{F:Labels.Frame G d} (T:SectionData F)(P:Coefficient F n) (o:Site n):coin A (P.exponentialEntry o T A) P.forced=P.density o T A:=rfl -- decEq
variable (K:Box n→Config G n→Poly B)(F:Config G n→ Poly B)(U:Config G n)
def play : Poly B:= (Real.exp (A.exponent U):ℂ) • (Poly.pass (F U)* field (fun j=>K j U) (flags A.p.threshold U))
variable {σ δ v a b : ℝ}
    (α:V→ Config G n→ℂ)(κ: V→ ℕ→Config G n→ℂ)
    (hr:A.activities.Valid A.p δ v)
    (h : ∀ i,(K i U).part B.quiet=profile A.activities (fun j=>Complex.ofReal ∘ A.activities.K j) i U)
    (hs: (F U).part B.quiet=0)
include h hr hs
lemma bronze : (play A B K F U).part B.quiet=A.eval U:=by rw [play,Poly.part_smul,Poly.quiet_mul,Poly.pass_part _ hs,stage₀ _ _ _ (F:=fun p=>K p U) (mass_crest _ hr _) h,one_mul]; exact Complex.ofReal_mul ..|>.symm
lemma beach (v:V) (hz: Summable (fun j=> κ v j U))(hp : ∀ i,(K i U).part (B.fire v)= profile A.activities (κ v) i U): (play A B K F U).part (B.fire v)=coin A (fun U=> (F U).part (B.fire v)) (κ v) U :=by
   rw [play,Poly.part_smul,shock,Poly.pass_part _ hs,whisper _ _ hs,stage₀ _ _ _ (F:=fun p=>K p U) (mass_crest _ hr _) h]; unfold coin
   rw [stageR _ _ _ (F:=fun p=> K p U) (mass_crest _ hr _) h hz hp, Rep.eval,Complex.ofReal_mul]; ring
lemma ascent (i:V) (hz: Summable (fun j=> κ i j U))(hp : ∀ j,(K j U).part (B.fire i)= profile A.activities (κ i) j U)(hw:A.eval U≠0)(he:(play A B K F U).part (B.fire i)=coin A (α i) (κ i) U): (F U).part (B.fire i)=α i U:=by
   rw [beach _ _ _ _ _ κ hr h hs _ hz hp] at he; unfold coin at he; exact mul_left_cancel₀ (show (A.eval U:ℂ)≠0 from by exact_mod_cast hw) (add_right_cancel he)
omit h hs
-- if high terms explicitly same, carry. dont require any Era ornament
lemma plank {H : Support n→Config G n→Poly B} {o:V→Site n}
    (h:∀ i U,(K i U).part B.quiet=profile A.activities (fun j=>Complex.ofReal ∘ A.activities.K j) i U)(hs:∀ U,(F U).part B.quiet=0)
    (hx:∀ p,Burns o p (H p) A.p.threshold)(hk:∀ i,Flow o i (K i) A.p.threshold)
    (hy:∀ v,Dominated (κ v))(hp:∀ v U j,(K j U).part (B.fire v)=profile A.activities (κ v) j U)(he:∀ i U,(play A B K F U).part (B.fire i)=coin A (α i) (κ i) U)(hw:∀ U,A.eval U≠0)
    (hH:∀ U (p:B.Mode), 2 ≤ p.val.card → (F U).part p = (∑ i,H i U).part p): let G i U:= octave (K i U); let R i U:= octave (H i U); Carton o R G A.p.threshold ∧ play A B K F=restore A α (fun i=>profile A.activities (κ i)) R G:=by
   intro Z Y
   refine ⟨⟨fun i=> ⟨(hx i).sift,fun _=>octaves _⟩,fun i=>⟨(hk i).sift,fun _=>octaves _⟩⟩,?_⟩
   funext U; have ht(p):K p U= bar A.activities B U p+Mach B (fun i=> profile A.activities (κ i) p U)+Z p U:= (ballots _).trans (by rw [h p U]; simp_rw [show ∀ i, _ from fun i=>hp i U p]; rfl)
   have hf : F U = Mach B (fun i=>α i U) + ∑ i,Y i U:=by
      ext i; simp only [Poly.part_plus,Poly.part_sum]; by_cases hy': 2 ≤ i.val.card
      · rw [hH _ _ hy',hush _ i hy',zero_add];rw [Poly.part_sum]; exact Finset.sum_congr rfl fun j _=> (crest _ _ hy').symm
      rcases Nat.eq_zero_or_pos i.val.card with h1 | h1
      · have hz:i=B.quiet:=Subtype.ext (card_eq_zero.mp h1); rw [hz,mute,hs]; unfold Y; simp_rw [hop B _ (octaves _),sum_const_zero,add_zero]
      obtain ⟨v,hv⟩:=Finset.card_eq_one.mp (show i.val.card=1 from by omega); have hg:i=B.fire v:=Subtype.ext hv
      rw [hg,sing,ascent A B K F U α κ hr (fun p=>h p U) (hs U) v (hy v|>.summable U) (hp v U) (hw U) (he v U)]; unfold Y; simp_rw [hop₁ B _ (octaves _),sum_const_zero,add_zero]
   unfold play restore; rw [hf]; congr!; exact ht _
end YM.MergeProof.Accent
