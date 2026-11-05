import YM.TraceExtension.Cask.King
import YM.TraceExtension.Cask.Elude
import YM.TraceExtension.Cask.Saline
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {I V:Type}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]{G:Gauge}[Fintype I]
variable (P:Staff V I n) (R:Rep G n)(F:I→ Config G n→ Rain V G→ℂ)(w:Duel V→ℝ)
def robeT (s:Finset I) (U:Config G n)(v:Rain V G):= (-1:ℂ)^(crew P s).card * ∏ i∈s,F i U v
def lyrics (U:Config G n) (s:Finset I):= ∫ v,robeT P F s U v ∂freq V G
structure Decked (e u:ℝ):Prop where
    meters i : Envelope (uncurry (F i))
    draws i U : rule (P.cast i) (F i U)
    gaze : ∀ g:Site n→G.El, ∃ t:Rain V G,∀ i U v, F i (Lattice.gauge g U) (t*v)= F i U v
    pole (v) i : UsesFinal R.p.threshold (P.foot i) (fun U=>F i U v)
    pinch i U v: F i U v≠0 →P.pole i∩flags R.p.threshold U=P.flag i
    form i : P.pole (i:BareP P).val=P.foot i.val
    crams p U v: cram (wharf P) (fun i:BareP P=> F i.val U v) p = profile R.activities (fun i=> Complex.ofReal ∘ R.activities.K i) p U
    bucks : 0≤ e ∧ ∃ (ρ:ℝ)(a:I→ℝ), (∀ i,0 ≤ a i) ∧ Hit P.foot R.p.B a (e+1) ρ ∧ (((R.p.B + R.p.B +1)^4:ℕ):ℝ)*ρ ≤ 1 ∧ Real.exp ρ-1 ≤ u ∧
        ∀ s:Finset I,Spark P.foot s→ Woven P s → (crew P s).Nonempty → ∀ U v, (Poly.toll w (spanZ (crew P s))) * (∏ i∈s,‖F i U v‖) ≤ ∏ i∈s,a i
variable {e u:ℝ}
set_option quotPrecheck false
local notation "E"=> Config G n
local notation "F!"=> Rain V G
local notation "R!"=>robeT P F
local notation "Y"=>lyrics P F
local notation "m!"=>freq V G
variable {P w} (M:Decked P R F w e u)
include M
lemma floorsV (s:Finset I): Envelope (uncurry (robeT P F s)):= envUmul (constV _) (envUprod s (fun i=> uncurry (F i)) (fun i _=>M.meters _))
lemma hymns (hw:∀ i,0<w i): Cache P R Y w e u:=by
   refine ⟨fun s U V h hx=> ?_,fun s=> (sealM m! (floorsV R F M s)).meas,fun s g U=> ?_,fun U s ht i hi=> ?_,M.form, fun U i b h=>?_,fun U p=> ?_,?_⟩
   · refine congr_arg (fun f:F!→ℂ=>∫ v,f v ∂m!) (funext fun v=> show (_:ℂ)=_ from congr_arg₂ (· * ·) rfl (prod_congr rfl (fun j hj=>?_)))
     exact Work.H03.reads_larger (subset_biUnion_of_mem _ hj) (M.pole v j) U V h hx
   · obtain ⟨t,ht⟩:=M.gaze g; let W:=gauge g U
     have hv: Measurable (robeT P F s W):= show Measurable ((uncurry (robeT P F s)) ∘ Prod.mk W) from (floorsV R F M s).meas.comp (measurable_const.prodMk measurable_id)
     exact (vortex t (robeT P F s W) hv).symm.trans (congr_arg (fun f:F!→ℂ=>∫ v, f v∂m!) (funext fun v=> by unfold robeT; simp_rw [W,ht]))
   · by_contra hp; apply ht; have hh(v): robeT P F s U v=0:=by unfold robeT; rw [prod_eq_zero hi (Classical.byContradiction fun hn=>hp (M.pinch i U v hn)),mul_zero]
     unfold lyrics; simp_rw[hh,integral_zero]
   · let t:= dispel i b; have he(v:F!) : robeT P F (grab i b) U v=∏ j∈t,robeT P F j U v:=by
        unfold robeT; change _* ∏ i'∈ t.biUnion id,F i' U v= _; rw [prod_mul_distrib,prod_biUnion h.pieces]
        have hh:crew P (grab i b)= t.biUnion (crew P):=by unfold grab crew bulk; rw[biUnion_biUnion];rfl
        rw [hh, card_biUnion h.apart]; simp only [Finset.prod_pow_eq_pow_sum,id_eq]; rfl
     unfold lyrics; simp_rw [he]; refine harvest _ (crew P) _ h.apart (fun j _=>fun a b hv=>?_) ; apply congr_arg (_ *·); exact prod_congr rfl (fun i hi=>M.draws i U a b (fun k hk=>hv k (mem_biUnion.mpr ⟨i,hi,hk⟩)))
   · have hp(i:BareP P): lyrics P F U {i.val}= F i.val U (1:Rain V G):=by
         unfold lyrics; have hh(v : Rain V G): robeT P F {i.val} U v=F i.val U 1:=by
             unfold robeT; rw [crew_silent, prod_singleton,card_empty,pow_zero,one_mul]; exact M.draws _ _ _ _ (fun _ h=>False.elim (notMem_empty _ (i.property ▸ h)))
         simp_rw [hh]; simp
     exact (congr_arg (fun f:BareP P→ℂ=> cram (wharf P) f p) (funext hp)).trans (M.crams p U 1)
   obtain ⟨he,ρ,a,ha,hA,hv,hρ,H⟩:=M.bucks
   refine ⟨he,ρ,a,ha,hA,hv,hρ,fun s hs ht hh U=> ?_⟩
   let b:=Poly.toll w (spanZ (crew P s)); have hB:0 < b:= Poly.worth hw _
   rw [mul_comm]; refine (le_div_iff₀ hB).mp (meanN (fun v=> ?_) m!)
   · unfold robeT; simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul, norm_prod]; exact (le_div_iff₀ hB).mpr ((mul_comm ..).trans_le (H s hs ht hh U v))
end YM.Trace.Cask
