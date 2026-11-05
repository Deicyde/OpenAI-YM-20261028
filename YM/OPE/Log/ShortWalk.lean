import YM.OPE.Log.Brake
import YM.OPE.Sweep.Induct
/-! # Log-aware short walk through moderated spacings. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Station Corona
open scoped Topology BigOperators Classical
variable {Z V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable {A:History G}{N p k m i j:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E:∀ i:ℕ, V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:∀ i:ℕ,V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "Γ" => A.levels.clock.op i p
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
local notation "L'" => (fun i=> ((A.S.block i).val:ℝ))
variable {Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}{H l : ℕ}{L:Fibers I J}
open OPE.Log
variable {a w : ℝ}
lemma throttled_joint {α:ℕ}{K:Fibers I J} (h: Fintype.card I ≤ H)(ht:Fintype.card J<Fintype.card I)(ha:0<a)(hx:a≤1)(hw:0<w)
    (hr:a ≤ license A δ H α i * δ i) (hd:0<δ i)(hW:compensation A H i j (Fintype.card I) a w ≤ ∏ x,W x):
    compensation A H i j (Fintype.card J) a w ≤ ∏ x,grouped A δ H α i (fun x=>δ i * W x) K x/8:=by
    let y b:= compensation A H i j b a w; let p:= Fintype.card I; let q:= Fintype.card J; let t:= a/8
    have hy b: 0< y b:=comp_pos ha hw; have hF:0<t:=div_pos ha (by norm_num); have hG:t ≤ 1:= by unfold t; linarith only [hx];
    have hV: 0 < license A δ H α i:=pos_of_mul_pos_left (ha.trans_le hr) hd.le
    have hg: a^H ≤ a^p:= pow_le_pow_of_le_one ha.le hx h
    have hp: (8:ℝ)^q ≤ 8^H:= pow_le_pow_right₀ (by norm_num) (ht.le.trans h)
    have hU: y q ≤ y p*t^H:=by
       have hz:H*(H-p)+H ≤ H*(H-q):=by calc _ = H*(H-p+1):= by ring
                                                                                     _ ≤ _:= Nat.mul_le_mul_left H (by omega)
       have he:=pow_le_pow_of_le_one hF.le hG hz
       unfold y compensation; change _ * t ^ _ * _ ≤ _ * t^_ *_* t^H
       rw [mul_right_comm _ w, mul_assoc _ _ (t^H), ← pow_add]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_pos (div_pos (A.S.a_pos _) (A.S.a_pos _)) _|>.le)) hw.le; exact he
    rw [prod_div_distrib,groupCash,cashIn_a, prod_const,card_univ,le_div_iff₀ (by positivity)]; refine le_trans (mul_le_mul_of_nonneg_left hp (hy q|>.le)) ?_
    calc y q*(8:ℝ)^H ≤ (y p*t^H)*8^H := mul_le_mul_of_nonneg_right hU (by positivity)
         _ = a^H * y p := by unfold t; rw [mul_assoc,← mul_pow,div_mul_cancel₀ _ (by norm_num),mul_comm]
         _ ≤ (license A δ H α i*δ i)^p* (∏ x,W x) := mul_le_mul (hg.trans (pow_le_pow_left₀ ha.le hr _)) hW (hy p|>.le) (pow_pos (mul_pos hV hd) _|>.le)
         _ = _ := by dsimp only [p]; rw [mul_pow, prod_mul_distrib, prod_const, card_univ, mul_assoc]
variable (h:A.Selected)(ht:Thor A δ r D σ χ k)(hF:Brine A k δ φ)
variable (hm:k ≤ m) (hj:j ≤ N)
    (hΔ:∀ i:ℕ, m ≤ i→∀ hi:i<j,Q i (hi.le.trans hj)=(A.levels.clock.op i p).push (A.rep N p (i+1)).beta (Q (i+1) (hi.trans_le hj)))
    (hI:∀ i:ℕ,m ≤ i→∀ hi:i ≤ j, Integrable (Q i (hi.trans hj)) (prior G _))
    (he:∀ i:ℕ,m  ≤  i→∀ hi:i ≤ j, ClusterPars A δ χ r i)
    (hG:∀ i:ℕ,m ≤ i→i ≤ j→H ≤ r i) (hp:Migrating A m p j E)
    (hE:∀ i,m ≤ i→i<j→(A.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i)
    (hD:∀ (i:ℕ),m  ≤  i→∀ hi:i<j,MergeProof.Float.Runs (D N p i (hi.trans_le hj)) (A.levels.clock.op i p) (6*((A.S.block i).val:ℝ)))
    (hΩ:∀ i,m ≤ i→i ≤ j→ Collar (o i) v (E i) P)
    (hB:∀ i,m ≤ i→i ≤ j→ Cross (A.levels.budget i).B (o i))
    (ha:0<a)(hb:a ≤ 1){z:ℕ→ℕ} (hS:∀ i,m ≤ i→i < j→ a ≤ license A δ H (z i + 2) i * δ i ∧ 8 ≤ z i ∧ z i ≤ (A.levels.budget i).B ∧ 1 ≤ δ i* mintK (z i))
    (hδ:∀ i,m ≤ i→i ≤ j→ Arsenal (A.rep N p i))
include h ht hm hj hΔ hI hG hp hE hD hΩ hB
lemma Under.take_L {W':J→ℝ}{c':V×J→ℂ} (hi:m ≤ i)(hh:i<j)(hc:Under A N p E (fun x=>o x ∘ (partialGroup V L).twig) P v B (fun x hx U=> Fibers.reap (partialGroup V L) (Q x hx U)) (i+1) (hh.trans_le hj) W' c') {b:ℝ} (hb:0<b)(hb':b ≤ 1)(hN:Fintype.card J ≤ H) (hpeg:Repegs (o i ∘ (partialGroup V L).twig) (Y' i).B (fun j=>δ i*W' j.2) (fun j=>b*(W' j.2 / (L' i)^4)) (1/2) 1 (Names V J)) : Live A N p E (fun x=>o x ∘ (partialGroup V L).twig) P v B (fun x hx U=> Fibers.reap (partialGroup V L) (Q x hx U)) δ χ i (hh.le.trans hj) (fun j=>b*(W' j/(L' i)^4)) c':=by
    let G:=(partialGroup V L).twig; have hr:(Γ).ratio.parent ∘ o (i+1) ∘ G=o i ∘ G:=by rw [← hE i hi hh]; rfl
    have hφ:0<L' i:=lt_of_lt_of_le zero_lt_two (size_enough A i)
    refine Under.passes h ht (hm.trans hi) (hh.trans_le hj) hc (hp.mare i hi hh|>.symm) ((hΩ _ (hi.trans i.le_succ) hh).shrunk L) (repush _ (hΔ i hi hh) (hI _ (hi.trans i.le_succ) hh) L) (reap_live _ (hI _ (hi.trans i.le_succ) hh) L) hr ((hB _ (hi.trans i.le_succ) hh).shrunk L|>.counts (hN.trans (hG _ hi hh.le)) (Y' _|>.B_pos)) ((hB i hi hh.le).shrunk L|>.counts (hN.trans (hG _ hi hh.le)) (Y' _|>.B_pos)) (hD i hi hh) (by linarith only [size_enough A i]) hpeg (fun v=>?_ ) (fun b=> mul_pos hb (div_pos (hc.width b) (by positivity)))
    apply (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ((div_pos (hc.width v) (show 0 < (L' i)^4 by positivity)).le) hb') (show 0 ≤ 6*L' i by positivity)).trans
    rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2
    rw [pow_succ, mul_comm (6*L' i)]; apply mul_le_mul_of_nonneg_left _ (hc.width v|>.le); refine mul_le_mul_of_nonneg_right ?_ hφ.le; calc _  ≤  (2:ℝ)^3:=by norm_num
                                                                                                                                                _  ≤  _:=pow_le_pow_left₀ zero_le_two (size_enough A i) _

variable (hH:Fintype.card I=H) (hT:Edition.Spaced (A.levels.budget j).B (o j)) (i₀:I) (hY:Live A N p E o P v B Q δ χ j hj W c)
include hH hY ha hb hS he hB hδ
local notation "Q*" => Q -- composition
lemma coastUnder (hi:m ≤ i)(hJ:i ≤ j) :
    ∃ (J:Type)(_ : Fintype J)(_ : DecidableEq J)(F:Fibers I J)(X:J→ℝ)(s:V×J→ℂ), F.twig (F.bunch i₀)=i₀ ∧ Under A N p E (fun i=>o i ∘ (partialGroup V F).twig) P v B (fun x hx U=>Fibers.reap (partialGroup V F) (Q x hx U)) i (hJ.trans hj) X s ∧ compensation A H i j (Fintype.card J) a (∏ x,W x)  ≤  ∏ x,X x:=by
    have hW:0<∏ x,W x:= Finset.prod_pos fun i _=> hY.width i
    induction hJ using Nat.decreasingInduction with
    | self=> refine ⟨I,inferInstance,inferInstance,Fibers.same I,W,c,rfl,?_,?_⟩
             · rw [show (fun (x:ℕ)(hx:x ≤ N)(U: Config G (A.S.side x p))=>Fibers.reap (partialGroup V (Fibers.same I)) (Q x hx U)) =Q from funext fun x=> funext fun hx=> funext fun U=> Fibers.same_reap _]; exact hY.toUnder
             unfold compensation; rw [← hH, Nat.sub_self,mul_zero,div_self (A.S.a_pos j).ne',pow_zero,one_pow,mul_one,one_mul]
    | of_succ i hJ IH=>
       obtain ⟨T,cX,cY,L,W',c',hZ,hU,hL⟩:=IH (hi.trans i.le_succ)
       have hu: Fintype.card T  ≤  H:= (Fintype.card_le_of_surjective L.bunch L.sectioned.surjective).trans hH.le
       have hζ:0<H:= by rw [← hH]; exact Fintype.card_pos_iff.mpr ⟨i₀⟩
       let V₀ b:= W' b/(L' i)^4
       let o' x:=o x ∘ (partialGroup V L).twig;
       have h_T : 2 ≤ L' i := size_enough A i
       have h_t : 0 < L' i := zero_lt_two.trans_le h_T
       have hpos (b):=div_pos (hU.width b) (pow_pos h_t 4)
       have hpool (b): V₀ b ≤ W' b:= div_le_self (hU.width b|>.le) (one_le_pow₀ (one_le_two.trans h_T))
       by_cases hA:Moderate (o' i) (Y' i).B (z i)
       · have hz:= hA.pegs (W':=fun j=> (1:ℝ)*V₀ j.2) (K:=Names V T) (W:=fun j=> δ i*W' j.2) (fun j=> ?_ ) (fun j=> mul_pos one_pos (hpos _)) (fun j=>mul_pos (he i hi hJ.le|>.funs.1) (hU.width _)) (Y' i|>.B_pos) ((hS i hi hJ).2.1)
         refine ⟨T,cX,cY,L,V₀,c',hZ,?_,compensated p hu ha hW hL⟩
         have hy:= Under.take_L h ht hm hj hΔ hI hG hp hE hD hΩ hB hi hJ hU (b:=1) one_pos le_rfl hu hz
         simp only [one_mul] at hy; exact hy.toUnder
         rw [one_mul]; exact (hpool _).trans ((le_mul_of_one_le_right (hU.width _|>.le) (hS i hi hJ|>.2.2.2)).trans_eq (by ring))
       have hϕ := he i hi hJ.le
       obtain ⟨J,cH,cK,S,hJ',hU',-,hΨ⟩:= Collar.cozy (L.bunch i₀) (Y' i|>.B_pos) ((hΩ i hi hJ.le).shrunk L) ((hB i hi hJ.le).shrunk L)  (zero_lt_one.trans_le (Nat.le_trans (by decide:1 ≤ 8) (hS i hi hJ).2.1)) (hS i hi hJ).2.2.1 hA
       have hc:= Under.take_L h ht hm hj hΔ hI hG hp hE hD hΩ hB hi hJ hU (b:=δ i) hϕ.funs.1 hϕ.funs.2 hu (fun b hh X h=>?_ )
       let F:= L.comp S
       have hσ:=hc.gathers _ (z i+2) S h (hJ.le.trans hj) hϕ (hδ i hi hJ.le) hζ hu ((hB i hi hJ.le).shrunk L |>.counts (hu.trans (hG _ hi hJ.le)) (Y' i|>.B_pos)) ((hΩ _ hi hJ.le).shrunk L) hΨ
       have hℓ:F.twig (F.bunch i₀)=i₀:= by unfold F Fibers.comp; dsimp only [comp_apply]; rw [hJ',hZ]
       let q' x (hx:x ≤ N) U:= Fibers.reap (partialGroup V F) (Q x hx U)
       have hχ:q' = (fun x hx U=> Fibers.reap (partialGroup V S) (Fibers.reap (partialGroup V L) (Q x hx U))):= funext fun x=> funext fun hx=> funext fun U=> (Fibers.comp_reap (partialGroup V L) (partialGroup V S) (Q x hx U)).symm
       refine ⟨J,cH,cK,F,_,0,hℓ,hχ.symm ▸ (show Under _ _ _ E (fun x=>o x ∘ (partialGroup V F).twig) _ _ _ _ _ _ _ _ from hσ), throttled_joint hu hU' ha hb hW (hS i hi hJ).1 hϕ.funs.1 (compensated p hu ha hW hL)⟩
       rw [one_mul]; have h1:Poly.toll (fun j: V×T=> δ i*(W' j.2/(L' i)^4)) b ≤ Poly.toll (fun j: V×T=> δ i*W' j.2) b:= Finset.prod_le_prod (fun j _=>mul_nonneg hϕ.funs.1.le (hpos j.2|>.le)) (fun j _=> mul_le_mul_of_nonneg_left (hpool _) hϕ.funs.1.le)
       exact h1.trans (le_mul_of_one_le_right (prod_nonneg (fun j _=>mul_nonneg hϕ.funs.1.le (hU.width j.2|>.le))) (Real.one_le_exp (by positivity)))
end YM.MergeProof.Ribbons.ManyCopies
