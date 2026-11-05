import YM.RG05Readout.Many.Bundle
import YM.MergeProof.ChaletS
import YM.OPE.Replicas.Budget
/-!
# Birth invoice on the tuned pencil

Use the actual microscopic stencils, order-summed. Singleton profiles
explicitly reproduced with the Crown response at the top gauge measure.
Budget pays the SAME D and parameters as preimage advances use. Larger
site-count cost bought separately from Scrim on this path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
section port
variable {G:Gauge}{n:Side}{S:Rep G n} {I:Type}{o:Site n}{P:Three G n}
   {d e x y c β v:ℝ}
def Crown (S:Rep G n)(o:Site n)(P:Three G n)(d:ℝ):Prop:=Useful S P∧∃ Z:MergeProof.Response G n, Attainment S.p o Z d∧ profile S.activities P.2.2=hook S.activities S.p.threshold Z
variable (he:Crown S o P d)
include he
lemma Crown.bill (hp:d≤e) : Crown S o P e:=by obtain ⟨a,Z,hV,hW⟩:=he; exact ⟨a,Z,stackFee hV hp,hW⟩
lemma Crown.mass : 0≤d:=sumBudget_credit he.2.choose_spec.1.toll.choose_spec.1 -- inference
lemma Crown.adjoin {Q:Three G n}(hf:Crown S o Q e)(hr:S.Lawful x y c β v): Crown S o (P+Q) (d+e):=by
   obtain ⟨hp,Z,hA,hB⟩:=he; obtain ⟨hq,V,hE,hF⟩:=hf
   exact ⟨Useful.join S hr hp hq,Z+V,hA.plus hE,by rw [hook_add,← hB,← hF];exact MergeProof.Float.prof_add _ hp.normK hq.normK⟩
lemma Crown.sprays (a:ℂ): Crown S o (a • P) (‖a‖*d):=by
   obtain ⟨hp,Z,hA,hB⟩:=he; exact ⟨Useful.smul S _ _ hp,a • Z,stack_of hA a,by rw [hook_scale,← hB]; exact profile_scale ..⟩
omit he
lemma Crown.dark : Crown S o 0 0:= ⟨Useful.zero S,0,Attainment.blank _,by ext; simp [profile,cram,hook]⟩
lemma Crown.ribbon {P:I→Three G n}{d:I→ℝ}(F:Finset I)(hf:∀ i,Crown S o (P i) (d i))(hr:S.Lawful x y c β v): Crown S o (∑ i∈F,P i) (∑ i∈F,d i):=by
   induction F using Finset.induction_on with
   | empty=> rw [Finset.sum_empty, Finset.sum_empty]; exact Crown.dark
   | @insert i s hi ih=>rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (hf _).adjoin ih hr
end port

variable {G:Gauge}{C:Family G} {n m p N d:ℕ}{V W : Type}[DecidableEq V] [Fintype V] {R:Census V}{a b x t y z β:ℝ}
    {ψ u f g:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{D:Rail C}{r:ℕ→ℕ}{w: Worth}
    (h:C.Makes) (hs: Scrim C w ψ u f g ζ r D)
set_option quotPrecheck false
local notation "Z"=> C.path
local notation "P"=> C.path.rep N p N
local notation "H"=> C.side N p
local notation "Σ₀"=> (C.path.levels.budget N).B
local notation "B'"=> C.path.levels.budget N

include h hs
lemma crowntop (i:Letter d)(v: (C.labels.level (kept i)).Index) (hc:C.ref (kept i) ≤ N) (F:Body) :
     Crown P 0 (Bare C d N p ⟨i,v⟩ F) (‖readJ i 0 F‖*(ψ N / ζ (kept i) N)):=by
    let q:=kept i; let Q:=C.labels.level q; let A:=Size.axis Q v; let X:= bareK C d N p i A
    obtain ⟨M,hT,hU,hY,hZ⟩:=(hs.costs.aim _ N p hc).lyrics
    have he : X=(M.tone N).plays A:=by unfold X bareK; rw [hT];rfl
    let f' := ‖alto C.path N q‖; have ht : bond C.path N p M N A=f':=by unfold bond; rw [← hU.head.heard.currents A,hU.head.out,Size.size_axis,mul_one]
    obtain ⟨X0,hF,hL,hW,hO,hE⟩:= hs.costs.heights _ _ N p hc le_rfl
    let s':=ζ q N; have hu:0<s':=hs.grows _ _ hc; have hw : 0 < f':=by unfold f'; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
    obtain ⟨σ,hv,hp⟩:= erected C.path C.params (C.localSection q) _ _ _ X0 (C.ref q) N p M A (s'/f') (hT:=h.sections _) hE h.wilson hU (by rw [ht,div_mul_cancel₀ _ hw.ne']) hW hO (div_nonneg hu.le hw.le)
    have hx:Useful P (invoice X 0 (C.localSection q) P):=by rw [he]; exact Useful.invoice _ 0 _ _ (h.wilson.represents _ _ _ le_rfl).good (hU.head.heard.earns ..|>.2) (hU.head.heard.earns ..|>.1)
    have hg: Crown P 0 (invoice X 0 (C.localSection q) P) (ψ N/s'):=by
       refine ⟨hx,booster (C.localSection q) P 0 A,stackFee hv ?_,?_⟩
       · apply (le_div_iff₀ hu).mpr; exact (le_of_eq (b:=s'/f'*(f'*σ)) (by field_simp)).trans hp
       rw [he]; exact hZ _
    exact hg.sprays _

def pricesTop (ζ:ℕ→ℕ→ℝ)(ψ:ℕ→ℝ)(N d:ℕ):ℝ := pulseFee d * ∑ i:Letter d, ψ N/(ζ (kept i) N) -- C unused remove

lemma arrives (hX:∀ i≤d,C.ref i ≤ N){F:Body}(hF:Cap (d+2) F b) (k:Palette C d)(x:Motion) (o:Site (C.side N p)) (π:(C.path.rep N p N).activities.Moves x.1 o):
    Crown P o (spin x π ((basisTop C d N p k) F)) (b*size k* pricesTop ζ ψ N d):=by
    let A:=fun i: Mark C d=>‖val k i‖*(‖readJ i.1 0 F‖*(ψ N/ζ (kept i.1) N))
    have hy(i:Mark C d) := (crowntop (p:=p) h hs i.1 i.2 (hX _ (Nat.sub_le ..)) F).sprays (val k i)
    have ha : Crown P 0 ((basisTop C d N p k) F) (∑ i: Mark C d,A i):=by
        change Crown P 0 ((∑ i:Mark C d,val k i • Bare C d N p i) F) _
        rw [LinearMap.sum_apply]; exact Crown.ribbon Finset.univ hy (h.wilson.represents _ _ _ le_rfl).good
    have hz : (∑ i:Mark C d,A i)≤b*size k*pricesTop ζ ψ N d:=by
       let f i:= ψ N/ζ (kept (d:=d) i) N
       have hm(i:Letter d):0≤ f i:=by apply div_nonneg (hs.costs.night.endow N|>.1) ((hs.grows _ _ (hX _ (Nat.sub_le ..))).le)
       unfold size pricesTop; rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_le_sum (fun i _=> ?_)
       have hx:= mul_le_mul (fees d i.1 box0 hF) (show f i.1≤∑ j:Letter d,f j from Finset.single_le_sum (fun i _=>hm i) (Finset.mem_univ _)) (hm _) (mul_nonneg (feepos d).le hF.nonneg)
       exact ((mul_le_mul_of_nonneg_left hx (norm_nonneg (val k i)))).trans_eq (by ring) -- f defeq
    obtain ⟨hq,F',hW,hK⟩:= ha.bill hz
    have he:= rise x o hW; rw [show affine x.1 o 0=o by simp [affine]] at he
    exact ⟨signpost_use h le_rfl x π hq,upwards x o F',he,(spin_at ..).lens.trans (by rw [hK,hooked x o π])⟩

variable {s: V→ℕ}{Θ:V→Body}{X:(i:V)→Palette C (s i)} {Z':V→Motion}{o:V→ Site (C.side N p)}{e:V→ℝ} -- remove
local notation "B₀"=> fun i:V=> stepUp (Z' i) (o i) (entrance C (s i) N p (X i) 0 (Θ i))
-- keep Z0 supplied. apply endow maybe new.
structure Festive (A: Levels G)(r:ℕ)(u:ℝ)(x:ℕ):Prop where
    endow : let Q:=A.budget x; 0 ≤ u ∧ 0 ≤ Q.supportExponent-3 ∧ let C:ℝ:= A.clock.forcedAllowance x + r*siteFactor Q.B*u
            ((Q.B+Q.B+1:ℕ):ℝ)^4*C ≤ 3 ∧ Real.exp C-1≤1
set_option maxHeartbeats 800000 in
lemma initiate (π: ∀ i,(C.path.rep N p N).activities.Moves (Z' i).1 (o i)) (ht:∀ i:V,∀ j≤ s i,C.ref j≤N) (hm:Festive C.path.levels m t N) (ho:Occupancy o m) {r:V→ℝ} (hp:∀ i:V,0 < r i)(hΘ:∀ i,Cap (s i+2) (Θ i) (e i)) (hy:∀ i:V,r i*(e i*size (X i)*pricesTop ζ ψ N (s i)) ≤ t):
    MenuBoard (P) (fun i:V=>spin (Z' i) (π i) (basisTop C (s i) N p (X i) (Θ i))) (birth R P (B₀)) o r ((C.path.levels.budget N).supportExponent-3) 1:=by
    let q(i:V):= spin (Z' i) (π i) (basisTop C (s i) N p (X i) (Θ i))
    let f:= B₀
    have hf:= fun i=> arrives h hs (ht i) (hΘ i) (X i) (Z' i) (o i) (π i)
    choose φ hF hU using fun i:V=> (hf i).2
    have hP':=(h.wilson.represents N p N le_rfl); let s₀:= (P).p; have hS:s₀=B':= hP'.vac
    obtain ⟨hu,hH,hJ,hy'⟩:= hm.endow; let v':= (P).p; let κ:=C.path.levels.clock.forcedAllowance N; let wC:= κ + m * siteFactor s₀.B*t
    have h1: (((s₀.B + s₀.B+1:ℕ):ℝ)^4*wC ≤ s₀.supportExponent - ((B').supportExponent-3)):=by unfold wC; rw [hS]; exact hJ.trans_eq (by ring)
    have h2 : Real.exp wC-1 ≤ 1:=by unfold wC; rw [hS]; exact hy'
    let g(i:V):=(q i).2.2; let Y(i:V):=(q i).2.1
    have hh(i:V) U: ((P).eval U:ℂ)* f i U=coin P (Y i) (g i) U:=by
       rw [show coin P _ _ _ = _ from congr_fun (hf i|>.1.read) U]; unfold f spin stepUp
       change _=Motion.scalar (Z' i) ((basisTop C (s i) N p (X i) (Θ i)).fst (Lattice.pull (Z' i).1 (o i) U))
       rw [basis_agrees C (s i) N p h (ht i), show ((↑((P).eval (Lattice.pull (Z' i).1 (o i) U)):ℂ))= _ from vac_pull (Z) N p N h.wilson le_rfl (Z' i).1 (o i) U, Motion.scalar_mul,show Motion.scalar _ (liftVac Z N p N U) = liftVac Z N p N U from Motion.scalar_real (Z' i) _]; rfl
    have hg : Garnish s₀ o φ r s₀.supportExponent t:= cloth hF hy (fun i=>(hp i).le)
    refine ⟨?_,fun i=> (hf i|>.1),unveiled R r hp P f hP'.good.labels φ hg ho hu le_rfl hH h1 h2 (fun U=>Tour.bright Z h.wilson N p N le_rfl U|>.ne') zero_le_one (fun i=>(hf i|>.1.normK)) (fun i=>(hU i).symm) hh⟩
    have hc(i:V) : Continuous (B₀ i):=by
       have hv : Continuous (entrance C (s i) N p (X i) 0 (Θ i)):=by
          change Continuous (fun U=> entrance C (s i) N p (X i) 0 (Θ i) U); unfold entrance; simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ (fun j _=> ((((C.localSection _).continuous_places _ _).const_smul _).const_smul _))
       unfold stepUp Motion.scalar;dsimp only; split; exact ((hv.comp (continuous_pull ..)).star); exact hv.comp (continuous_pull ..)
    exact ((hatCont C N p B₀ hc (show Continuous (P|>.eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) R).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
end YM.RG05Readout.Many
