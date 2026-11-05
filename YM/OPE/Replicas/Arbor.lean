import YM.MergeProof.North.Arbor
import YM.OPE.Replicas.Thumb

/-!
# Many slots per cell: port of YM/MergeProof/North/Arbor.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V I : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}{w:V→ℝ}
variable {o:V→ Site n}{u:V→ℂ} {F : Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
-- raw morphology gives canonical state provisional Blade at every source
set_option quotPrecheck false
-- When m aligned ancestors Harmony E. Bracket low Branch after projection Prop independent.Account overlap high.Horn.
variable {P:V→Motion}{E:V→Site n}{β:V→Equiv.Perm V}{μ:(V×slotsZ)→ Site n}
variable {g:(V×slotsZ)→ Config G n→ℂ}{k:(V×slotsZ)→ℕ→ Config G n→ℂ} {r:(V×slotsZ)→ℂ}{J:(V×slotsZ)→ℝ} {h':Config G n→Poly (Names V slotsZ)} {Z y c q d z:ℝ}
def May (v:V)(P:V→Motion)(E:V→Site n)(β:V→Equiv.Perm V)(g:(V×slotsZ)→ Config G n→ℂ)(k:(V×slotsZ)→Res G n)(r:(V×slotsZ)→ℂ):Prop:=∀ i,i≠v→ β i v=i∧∀ b:slotsZ,g (i,b)=stepUp (P i) (E i) (g (v,b))∧ k (i,b)=floatUp (P i) (E i) (k (v,b))∧r (i,b)=scalar (P i) (r (v,b))
variable {F:(V×slotsZ)→ Config G n→ℂ} {L:(V×slotsZ)→ ℕ→ Config G n→ℂ}
lemma stem (A:Arsenal R) (h: Arc R F L h' v P E β μ J (R.p.supportExponent+c) (R.p.supportExponent+q) a b x r)(hr:R.activities.Valid R.p z d)(he:∀ i,i≠v→∀ j:slotsZ,r (i,j)=scalar (P i) (r (v,j)))(hw:∀ i,0< J i)(hb:b≤ a)(hc:0≤ c)(hq:0≤ q)(hit:∀ U,R.eval U≠0): ∃ g:(V×slotsZ)→ Config G n→ℂ,∃ k:(V×slotsZ)→ℕ→ Config G n→ℂ, (∀ i,Dominated (k i)∧Blade R (μ i) (g i) (profile R.activities (k i)) (r i) (2*(a/J i)+2*(b/J i))) ∧ May v P E β g (fun i=>profile R.activities (k i)) r ∧ Serves R g (fun i=>profile R.activities (k i)) h' v P E β μ J R.p.supportExponent a:=by
    obtain ⟨G₀,K,ψ,hG,hK,hF,ht,hX,hV,hY,hC,hZ,rfl⟩:=h.see; let F' U := Mach (Names V slotsZ) r+∑ i,G₀ i U; let g(v:(V×slotsZ))(U):=(F' U).part ((Names V slotsZ).fire v)
    have he':= hF.shrink (le_add_of_nonneg_right hc) le_rfl hw; have hx:= ht.shrink (le_add_of_nonneg_right hq) le_rfl hw
    obtain ⟨k,Hq,hp,hF,hK⟩:= plume A hr hX hV he' hx hw hC hit r
    refine ⟨g,k,Hq,?_,_,_,hF, Towed.sift he',Towed.sift (hx.shrink le_rfl hb hw),?_, hK⟩
    · intro i H; have H' := hY i H; let y:=P i; let x:= E i
      refine ⟨H'.1,fun b'=>⟨?_,?_,he i H b'⟩⟩
      · funext U; unfold stepUp g F'
        simp_rw [Poly.part_plus,Accent.sing,Poly.part_sum, scalar_add,he i H b']; congr 1; rw [Float.summer]; rw [← Equiv.sum_comp (sky (P i) (E i))] -- which side?
        refine Finset.sum_congr rfl fun j _=>?_ ; have he:= (H'.2 U).1 j ((Names V slotsZ).fire (v,b')) ((which ..).mpr rfl); rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
      funext j U; unfold floatUp stepUp; obtain ⟨j,hx⟩:= (puff y x).surjective j; rw [← hx]; dsimp only; rw [← hp,← hp]; have he:= (H'.2 U).2 j ((Names V slotsZ).fire (v,b')) ((which ..).mpr rfl); change _=scalar _ ((K ((puff y x).symm (puff y x j)) _).part _); rw [Equiv.symm_apply_apply]; rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
    intro i H; have H' := hY i H; exact ⟨H'.1,fun U=>⟨fun j=>Harps ((H'.2 U).1 j),fun j=>Harps ((H'.2 U).2 j)⟩⟩
end YM.MergeProof.Ribbons.ManyCopies
