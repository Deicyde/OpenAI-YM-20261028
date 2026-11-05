import YM.RG05Readout.Address.Balance
import YM.MergeProof.Ballet
/-!
# Ancestors -- full central fiber before normalization

When shifting root presentations on the centered torus we pay the shifted
full cover norm including turns. No test outside its native cell is used.
Projection symmetry (which can fail e.g. for naive periodic copies using
an ambiguous winding direction) is deliberately not requested.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

section shift
variable {G:Gauge}{n:Side}{d:ℕ}{R:Rep G n}{F:Labels.Frame G d}
variable (o:Site n) (π:R.activities.Moves (1:Signed) o)
def shiftTape : Three G n→ₗ[ℂ] Three G n where
   toFun V := (V.fst ∘ (Lattice.pull (1:Signed) o), V.snd.1 ∘ (Lattice.pull (1:Signed) o), fun i=> V.snd.2 (π.kp.symm i) ∘ (Lattice.pull (1:Signed) o))
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
abbrev shiftFee (p:BudgetPoint):= turnCost p.order p.power
lemma shift_pays : 1≤ shiftFee R.p:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
lemma offset (S:SectionData F){A: Hol G}(hn:2 ≤ n.val)(P:Coefficient F n){v w:ℝ}(ht:S.Sound A)(hf:P.Format 0 A R) (hv:P.remBound 0 R v w) : ∃ Q:Coefficient F n,
     Q.Format o A R ∧ invoice Q o S R=shiftTape o π (invoice P 0 S R) ∧ Q.x=P.x∧Q.remBound o R v (shiftFee R.p*w):=by
    let M:Motion:=(1,false); let Q:= audition (z:=M) π P; obtain ⟨a,b,hq,hA⟩:= rem_tabs.mp hv
    obtain ⟨h0,h1,h2⟩:= audition_turn M o π hn ht hf hq; rw [show affine M.1 o 0=o by simp [affine,M]] at h0 h1 h2
    have hS : Q.exponentialEntry o S R=P.exponentialEntry 0 S R ∘ Lattice.pull (1:Signed) o:=by
       have he := bow (o:=0) M P o ht π; rw [show affine M.1 o 0=o by simp [affine,M]] at he; exact he
    have hX : Q.x=P.x:=by
       change F.act ((1:Signed).ortho) P.x =_
       rw [show (1:Signed).ortho=1 from map_one Signed.inclusionO,Frame.act_one]
    refine ⟨Q,h0, Prod.ext h2 (Prod.ext hS ?_), hX,h1.bound (le_trans (add_le_add_right (le_mul_of_one_le_left hq.second shift_pays) _) (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hA (zero_le_one.trans shift_pays)))⟩
    funext i; obtain ⟨j,rfl⟩:= π.kp.surjective i
    change ((reorient π P).forced (π.kp j))=_ -- o arg?
    rw [forced_reorient]
    change _ = P.forced (π.kp.symm (π.kp j)) ∘ _; rw [Equiv.symm_apply_apply]

lemma moveprint {S:Family G}(P:Tape G n)(a b:Palette S d) {v t:ℝ} (hn:2 ≤ n.val)(H:S.Makes)(h:Printed S d R 0 v P a b t):
    ∃ z:Palette S d, Printed S d R o v ((shiftTape o π).comp P) a z (shiftFee R.p*t):=by
   rcases h with @⟨T,V,u,c,Y,hU,hT,hK,hx,hy,hc⟩
   choose W hw hf ht hZ using fun i=> offset o π (S.localSection (kept i)) hn (T i) (H.sections _) (hU i) (hT i)
   have h_tail:∀ {U : Tape G n} {b:ℝ}, Necklace (S.labels.level 0) (S.localSection 0) S.params R 0 v d U b→∃ w,Necklace (S.labels.level 0) (S.localSection 0) S.params R o v d ((shiftTape o π).comp U) w ∧ w≤ shiftFee R.p*b:=by
      intro U b h
      induction h with
      | empty=> refine ⟨0, ?_,by rw [mul_zero]⟩; rw [LinearMap.comp_zero]; exact Necklace.empty
      | @chain V p u c f hz hA u' h hP ht ih=>
          obtain ⟨P',hF,hW,hx,hp⟩:= offset o π (S.localSection 0) hn u' (H.sections _) h hP
          obtain ⟨w,hq,hv⟩:=ih
          let v':=invoice u' 0 (S.localSection 0) R
          have heq:=congr_arg (glyph f) hW; rw [show glyph f (shiftTape o π v')=(shiftTape o π).comp (glyph f v') from LinearMap.ext fun i=>(map_smul ..).symm] at heq
          rw [LinearMap.comp_add,←heq]
          refine ⟨_, Necklace.chain f hz hA P' hF hp hq,?_⟩
          let q:= (S.labels.level 0).coeffSize u'.x; rw [mul_add (shiftFee R.p), hx, mul_left_comm]
          exact add_le_add (mul_le_mul_of_nonneg_left (by rw [mul_add]; exact add_le_add_left (le_mul_of_one_le_left (Work.G08.size_nonneg ..) shift_pays) _) (Priced.nonneg _ hA)) hv
   obtain ⟨z,HZ,hW⟩:= h_tail Y
   refine ⟨_,Printed.bind W _ HZ hw hZ ?_ (hx.trans (funext fun i=>(ht i).symm)) rfl ?_⟩
   · rw [← hK, LinearMap.comp_add]; congr 1; ext1 I; simp only [LinearMap.comp_apply,together,LinearMap.sum_apply,glyph_apply,map_sum,hf,map_smul]
   rw [← Finset.mul_sum]; apply le_trans ?_ (mul_le_mul_of_nonneg_left hc (zero_le_one.trans (shift_pays (R:=R))))
   rw [mul_add]; exact add_le_add le_rfl hW
end shift
section sites
variable {G:Gauge}(C:Family G)(p m:ℕ)
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p).ratio
abbrev Bud := Site (Z).count
def child (s:Bud C p m):Site (C.side (m+1) p):=(Z).assemble (0,s)
def displacement (s:Bud C p m):E4:= (((Z).count.val:ℝ)⁻¹) • WithLp.toLp 2 (fun i => (lift s i:ℝ))
lemma Bud.personal (s:Bud C p m): (Z).parent (child C p m s)=0:= Ratio.assemble_parent ..
lemma count_bud :(C.path.levels.clock.op m p).ratio.count.val=(C.path.S.block m).val:=rfl
lemma dist_box (s:Bud C p m): MapsTo (fun x:E4=> displacement C p m s+(((C.S.block m).val:ℝ)⁻¹) • x) Native.box Native.box:=by
    let y:= (Z); let d:=displacement C p m s; let L:= y.count.val; intro x hx a
    let k:= lift s; have ht : -(L:ℤ) <2*k a ∧ 2*k a < (L:ℤ):= ⟨(lift_centers ..).1, Ratio.unambiguous (C.S.block_odd m) s a⟩
    have he : 0 < (L:ℝ):= by have ht:= y.count.property; unfold L; positivity
    have h : -(L:ℝ)+1 ≤ 2* (k a:ℝ) ∧ 2*(k a:ℝ)+1 ≤ (L:ℝ) := ⟨by exact_mod_cast (show -(L:ℤ)+1 ≤ _ from Int.add_one_le_of_lt ht.1),by exact_mod_cast Int.add_one_le_of_lt ht.2⟩
    have hv := abs_le.mp (hx a)
    apply abs_le.mpr
    simp only [displacement,PiLp.add_apply, PiLp.smul_apply,smul_eq_mul]
    change _ ≤ (L:ℝ)⁻¹*(k a:ℝ) + (L:ℝ)⁻¹*(x a) ∧ (L:ℝ)⁻¹ * (k a:ℝ)+(L:ℝ)⁻¹*(x a) ≤ _
    simp_rw [← mul_add, mul_comm ((L:ℝ)⁻¹),← div_eq_mul_inv]
    rw [le_div_iff₀ he,div_le_iff₀ he]; constructor <;> linarith
end sites
end YM.RG05Readout.Address
