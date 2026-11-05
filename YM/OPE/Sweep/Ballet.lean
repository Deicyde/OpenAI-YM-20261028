import YM.OPE.Sweep.Winter
import YM.OPE.Replicas.Flank
/-!
# Across compact windows estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Station Corona Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
variable {Z V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable (C:Family G)(N p m j d:ℕ)
    {W:Bid.Worth}{u ψ φ δ σ χ x:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H" => C.path
local notation "Y" => C.path.levels
local notation "P'" => C.path.levels.budget
local notation "R" => C.path.rep N p
variable (E:∀ i:ℕ,V→Site (C.side i p))(o:∀ i:ℕ,V×I→Site (C.side i p))(P:V→ Motion)(v:V)(B:V→Equiv.Perm V)
    (i₀:I) (J':V→ℝ)(t:I→ℕ) (s: (i:I)→ C.label (t i)) (q:I→Motion)(a:I→ℝ) (F:V×I→ Config G (C.side N p)→ℂ) {α z:ℝ}{l:ℕ}(hm:m+1≤j)(hj:j<N)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm hj.le)
local notation "F!"=> (birth (Names V I) (R N) F)
local notation "X"=> (fun i:I=>δ j*(φ j*a i))
local notation "Y'"=> ((Y).budget (m+1))
def initial (H':History G)(δ φ : ℕ→ℝ)(m j : ℕ)(α a:ℝ) (t : ℕ) := α^t * compensation H' t (m+1) j 0 α ((δ j*φ j/8)^t*a)
local notation "T'"=> (Labels.frames G).level d
local notation "U" => Next.Foundations.localSection G d
local notation "Z'"=> (C.S.a (m+1)^d*(x m*(4*(1/z))))
variable (h:C.Makes)(hh:Scrim C W u ψ φ δ ζ r D)(hP: C.ref d ≤ m)(he: SwornClusterCuts C (μ:=D) (δ:=δ) (r:=r) (C.ref d) d χ δ x)
include h hh hP he hm hj
set_option maxHeartbeats 500000 in
lemma Ballet
    (ht:∀ i,C.ref (t i) ≤ j)(hM:∀ i,a i*Next.Rank.Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)
    (hr:Migrating H m p N E)(hv:P v=(1,false))(hf:E m v=0)(h₀:∀ i,o (m+1) (i,i₀)=E (m+1) i)(hx:∀ i,i≠v→B i v=i)
    (hA:∀ k:ℕ,m+1 ≤ k→ k ≤ N→ Collar (o k) v (E k) P)
    (hE:Migrating H j p N o)(hc:∀ k:ℕ,m+1 ≤ k→ k<j→(C.path.levels.clock.op k p).ratio.parent ∘ o (k+1)=o k)
    (hI: ∀ k:ℕ,m+1 ≤ k→ k≤j→ Cross (P' k).B (o k)) (hK: Edition.Spaced (P' j).B (o j))
    (hS:∀ i,i≠v→∀ b:I,F (i,b)=stepUp (P i) (E N i) (F (v,b))) (hY:∀ i,F (v,i)=MergeProof.item C (t i) N p (s i) (fun m'=>o m' (v,i)) (q i))
    (hX: Integrable (F!) (prior G _))
    (hω:Occupancy (E m) (r m))(hω':Occupancy (E (m+1)) (r m)) (ha:0<α)(hb:α≤1)
    (hR:∀ k:ℕ,m+1 ≤ k→ k<j→ α ≤ license H δ (Fintype.card I) (carpet H k) (k+1))
    (hΨ:α ≤ license H δ (Fintype.card I) l (m+1))
    (hΩ:∀ i:V×I, coverNumber (P' (m+1)).B ({o (m+1) (i.1,i₀),o (m+1) i}:Support _) ≤ l)
    (hz:0<z)(hy:z ≤ initial H δ φ m j α (∏ i,a i) (Fintype.card I))
    (hJ: ∀ i,0<J' i)(hε:∀ i,J' i ≤ δ m*(z/(16*x m))) :
    ∃ Q₀: Coefficient T' (C.S.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m) ∧ Q₀.remBound 0 (R m) (kappa H m) Z' ∧ (T').coeffSize Q₀.x ≤ Z' ∧
       Served (R m) (fun i=> radiant (alto H m d) (P i) (E m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (P i) (E m i) (alto H m d)) (gust H N p N (birth (Bud V) (R N) (fun y c=>∏ i,F (y,i) c)) m (h!).le) (E m) J' (P' m).supportExponent 1 :=by
    obtain ⟨σ,hq⟩:=he.city; let r':= C.ref d; let A:= Fintype.card I; have hZ:= hP.trans m.le_succ; have hZU:= hZ.trans hm; have hZ': 0 < A:= Fintype.card_pos_iff.mpr ⟨i₀⟩
    have hB : ∀ k≥r', ClusterPars H δ χ r k := fun k hk=>⟨he.crisp k hk, he.funs k hk,he.bars k hk⟩
    have hF' : Brine C.path (C.ref d) δ φ:=⟨fun i _=> hh.costs.stay.water _ (Nat.zero_le i),fun i _=> hh.costs.stay.mint _ (Nat.zero_le i),fun i _=> hh.costs.stay.split _ (Nat.zero_le i),fun i _=> hh.costs.stay.support _ (Nat.zero_le i)⟩
    obtain ⟨-,hL,-⟩:= (hh.costs.heights d (C.ref d) N p le_rfl (hZU.trans hj.le)).choose_spec
    obtain ⟨f,g,K,hg,hL',hD⟩:= upper C t N j p W u ψ φ δ ζ r D s o q a v E P B F σ χ hh.costs h hq hZU ht hj (fun i=>(Occupancy.of_injective (Edition.injected _ _ (P' j|>.B_pos) hK) i).trans (hh.back _)) hE ⟨fun _ _ i _ j _=> hK i j⟩ hM hw ⟨fun i hi=>hr.mare i (by omega)⟩ hx (fun i hi hp=>hA i (hm.trans hi) hp) hS hY hX
    let w(i:I):= δ j*(φ j*a i)/8; have hU(i):0<w i:= div_pos (mul_pos (he.funs j hZU|>.1) (mul_pos (hF'.water j hZU|>.1) (hw i))) (by norm_num)
    have hA':Arsenal (R j):=by
       cases j with
       | zero=> omega
       | succ j=> exact (hq.moon N p j (by omega) (by omega)).1.contact
    let Q:= gust H N p N (F!); have H0 : Live H N p E o P v B Q δ χ j hj.le w f:= Under.solved h.wilson hq hZU hj.le hU (he.crisp j hZU) hA' (W:=X) hD hg hL' (fun i=> (show 8*(δ j*(φ j*a i)/8) = _ from (by ring)).le)
    obtain ⟨J,xI,xV,L,X',c,hJ',hY',hV',hL'⟩:= inductionLive h.wilson hq hF' hZ hj.le (fun i _ hi=> gust_step H _ _ _ _ (hi.trans hj)) (fun i _ hi=> gust_live H _ _ _ _ hX _) (fun k hk _=> hB k (hZ.trans hk)) (fun i hi _=>hL.level i (hZ.trans hi)) (fun i _ _=> hh.back i) ⟨fun i hi hp=>hr.mare i (by omega) (hp.trans hj)⟩ hc (fun i hi hp=> he.brings i (hZ.trans hi) N p _|>.1) (fun i hi hp=>hA _ hi (hp.trans hj.le)) hI ha hb hR rfl hK i₀ H0 le_rfl hm
    rw [gust_step _ _ _ _ _ h!,ripe i₀ (by omega) hX] -- m:= remove
    let Q' x (hx:x≤N) U':= Fibers.reap (partialGroup V L) (Q x hx U'); have hσ:(fun U'=> Fibers.reap (finishGroup V i₀) (Q (m+1) h! U')) = (fun U'=> Fibers.reap (finishGroup V (L.bunch i₀)) (Q' (m+1) h! U')):= funext fun U'=> ((Fibers.comp_reap (partialGroup V L) (finishGroup V _) (Q (m+1) h! U')).trans (Fibers.similar_reap rfl (Q (m+1) h! U'))).symm
    rw [hσ]
    let a':= L.twig ∘ L.bunch; let y:= (fun i=>o i ∘ (partialGroup V L).twig); have hy'(i:V) : y (m+1) (i,L.bunch i₀)=o (m+1) (i,i₀):= by unfold y; change o (m+1) (i,L.twig (L.bunch i₀))=_; rw [hJ']
    have hu':Fintype.card J≤ A:= Fintype.card_le_of_surjective L.bunch L.sectioned.surjective
    refine Live.winter h.wilson hq (L.bunch i₀) h! hV' hP hf (hr.mare m le_rfl h!|>.symm) (fun i=>(hy' i).trans (h₀ i)) hv hω hω' (fun i=>(Occupancy.of_injective (Edition.injected _ _ (P' (m+1)|>.B_pos) hY') i).trans (hh.back _)) ((hA (m+1) le_rfl h!).shrunk L) hZ' hu' (hB (m+1) hZ) (reap_live h! (gust_live H _ _ _ _ hX h!) L) (l:=l) ?_ (he.brings m hP N p h!|>.2) (he.dollars m hP) hJ hε hz ?_
    · intro a; change coverNumber _ ({y _ _,y _ a}:Support _) ≤ _; rw [hy' a.1]; exact hΩ ((partialGroup V L).twig a)
    rw [cashIn_a]; apply hy.trans; unfold initial; rw [show (δ j * φ j/8)^A*(∏ x,a x)=∏ i,w i from ?_]; swap
    · rw [show w=fun i=> (δ j*φ j/8)*a i from funext (fun i=>by unfold w; ring), prod_mul_distrib,prod_const]; rfl
    have hk:0 < ∏ i,w i:= Finset.prod_pos fun i _=>hU i; let Y₀ (s):= compensation H A (m+1) j s α (∏ i,w i)
    have hu:0 < Y₀ 0 := comp_pos ha hk
    suffices hv' : Y₀ 0 ≤ ∏ i,X' i from mul_le_mul ((pow_le_pow_of_le_one ha.le hb hu').trans (pow_le_pow_left₀ ha.le hΨ _)) hv' hu.le (pow_pos (ha.trans_le hΨ) _|>.le) -- shadow
    refine le_trans ?_ hL'; unfold Y₀ compensation; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _|>.le)) hk.le; exact pow_le_pow_of_le_one (by positivity) (by linarith only [hb]) (Nat.mul_le_mul_left A (by change A - _ ≤ A-0; omega))
end YM.MergeProof.Ribbons.ManyCopies
