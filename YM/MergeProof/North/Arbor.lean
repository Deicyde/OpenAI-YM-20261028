import YM.MergeProof.North.Frost
import YM.MergeProof.North.Thumb
import YM.MergeProof.North.Verve
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}{w:V→ℝ}
variable {o:V→ Site n}{u:V→ℂ} {F : Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
-- raw morphology gives canonical state provisional Blade at every source
set_option quotPrecheck false
lemma plume (A:Arsenal R)(hp:R.activities.Valid R.p t x)(hq:∀ i,Burns o i (F i) R.p.threshold)(hK:∀ i,Flow o i (K i) R.p.threshold)(h:Towed w id F R.p.B R.p.supportExponent a)(ht:Towed w Prod.fst K R.p.B R.p.supportExponent b)(hw:∀ i,0<w i)(hC:∀ i U,(K i U).part B.quiet=profile R.activities (fun j=> Complex.ofReal ∘ R.activities.K j) i U)(hit:∀ U,R.eval U≠0)(u:V→ℂ):
     let P:= fun U=>Mach B u + ∑ i,F i U; let g(v:V)(U):=(P U).part (B.fire v)
     ∃ k: V→ℕ→ Config G n→ℂ, (∀ i,Dominated (k i)∧ Blade R (o i) (g i) (profile R.activities (k i)) (u i) (2*(a/w i)+2*(b/w i))) ∧ (∀ i j U,(K j U).part (B.fire i)=profile R.activities (k i) j U) ∧
        (let F':=fun i U=>octave (F i U); let K':=fun i U=>octave (K i U); Carton o F' K' R.p.threshold ∧ play R B K P= restore R g (fun i=> profile R.activities (k i)) F' K'):=by
    intro P g; have he v: Blade R (o v) (g v) (fun p U=>(K p U).part (B.fire v)) (u v) (2*(a/w v)+2*(b/w v)):=by
       have hs:= (blade₀ (R:=R) (o:=o v) (u:=u v) (a:=0) le_rfl).comp (sprouts v A hq hK h ht hw); rw [zero_add, zero_add, add_zero] at hs -- order
       have hF : g v = (fun _=> u v)+(fun U=>(∑ i,F i U).part (B.fire v)):= by funext U; unfold g P; rw [Poly.part_plus,Accent.sing]; rfl
       rw [hF]; exact hs
    choose k hy hH using fun v=>socket (he v); have hs(i j U): (K j U).part (B.fire i)=profile R.activities (k i) j U:=by rw [hH]
    have hx(U): (P U).part B.quiet=0:=by unfold P; simp_rw [Poly.part_plus,mute,Poly.part_sum,fun i=>(hq i).sil U,sum_const_zero,add_zero]
    refine ⟨k, fun i=>⟨hy i,by rw [hH]; exact he i⟩,hs,?_⟩
    exact plank R B K P g k hp hC hx hq hK hy (fun i U j=> hs i j U) (fun i U=>beach R B K P U k hp (fun j=>hC j U) (hx U) i (hy i |>.summable U) (fun p=> hs i p U)) hit (fun U p hz=>by unfold P; rw [Poly.part_plus,hush _ _ hz,zero_add])

-- When m aligned ancestors Harmony E. Bracket low Branch after projection Prop independent.Account overlap high.Horn.
variable {P:V→Motion}{E:V→Site n}{β:V→Equiv.Perm V}{μ:Name V→ Site n}
variable {g:Name V→ Config G n→ℂ}{k:Name V→ℕ→ Config G n→ℂ} {r:Name V→ℂ}{J:Name V→ℝ} {h':Config G n→Poly (Aged V)} {Z y c q d z:ℝ}
def May (v:V)(P:V→Motion)(E:V→Site n)(β:V→Equiv.Perm V)(g:Name V→ Config G n→ℂ)(k:Name V→Res G n)(r:Name V→ℂ):Prop:=∀ i,i≠v→ β i v=i∧∀ b:Bool,g (i,b)=stepUp (P i) (E i) (g (v,b))∧ k (i,b)=floatUp (P i) (E i) (k (v,b))∧r (i,b)=scalar (P i) (r (v,b))
variable {F:Name V→ Config G n→ℂ} {L:Name V→ ℕ→ Config G n→ℂ}
lemma stem (A:Arsenal R) (h: Arc R F L h' v P E β μ J (R.p.supportExponent+c) (R.p.supportExponent+q) a b x r)(hr:R.activities.Valid R.p z d)(he:∀ i,i≠v→∀ j:Bool,r (i,j)=scalar (P i) (r (v,j)))(hw:∀ i,0< J i)(hb:b≤ a)(hc:0≤ c)(hq:0≤ q)(hit:∀ U,R.eval U≠0): ∃ g:Name V→ Config G n→ℂ,∃ k:Name V→ℕ→ Config G n→ℂ, (∀ i,Dominated (k i)∧Blade R (μ i) (g i) (profile R.activities (k i)) (r i) (2*(a/J i)+2*(b/J i))) ∧ May v P E β g (fun i=>profile R.activities (k i)) r ∧ Serves R g (fun i=>profile R.activities (k i)) h' v P E β μ J R.p.supportExponent a:=by
    obtain ⟨G₀,K,ψ,hG,hK,hF,ht,hX,hV,hY,hC,hZ,rfl⟩:=h.see; let F' U := Mach (Aged V) r+∑ i,G₀ i U; let g(v:Name V)(U):=(F' U).part ((Aged V).fire v)
    have he':= hF.shrink (le_add_of_nonneg_right hc) le_rfl hw; have hx:= ht.shrink (le_add_of_nonneg_right hq) le_rfl hw
    obtain ⟨k,Hq,hp,hF,hK⟩:= plume A hr hX hV he' hx hw hC hit r
    refine ⟨g,k,Hq,?_,_,_,hF, Towed.sift he',Towed.sift (hx.shrink le_rfl hb hw),?_, hK⟩
    · intro i H; have H' := hY i H; let y:=P i; let x:= E i
      refine ⟨H'.1,fun b'=>⟨?_,?_,he i H b'⟩⟩
      · funext U; unfold stepUp g F'
        simp_rw [Poly.part_plus,Accent.sing,Poly.part_sum, scalar_add,he i H b']; congr 1; rw [Float.summer]; rw [← Equiv.sum_comp (sky (P i) (E i))] -- which side?
        refine Finset.sum_congr rfl fun j _=>?_ ; have he:= (H'.2 U).1 j ((Aged V).fire (v,b')) ((which ..).mpr rfl); rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
      funext j U; unfold floatUp stepUp; obtain ⟨j,hx⟩:= (puff y x).surjective j; rw [← hx]; dsimp only; rw [← hp,← hp]; have he:= (H'.2 U).2 j ((Aged V).fire (v,b')) ((which ..).mpr rfl); change _=scalar _ ((K ((puff y x).symm (puff y x j)) _).part _); rw [Equiv.symm_apply_apply]; rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
    intro i H; have H' := hY i H; exact ⟨H'.1,fun U=>⟨fun j=>Harps ((H'.2 U).1 j),fun j=>Harps ((H'.2 U).2 j)⟩⟩
end YM.MergeProof.Ribbons
