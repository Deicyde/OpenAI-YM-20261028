import YM.OPE.Sweep.Net

/-!
# Across intermediate scales, compensated progress

Unlike propagating a single capture halo across a layer of scales that
are subpower comparable, can instead propagate unprojected trees of
markers and pay for each partial capture independently. This buys a
price for product discrepancy with just one subpower penalty for any
fixed arity. (No dependence on the number of tiling cells.)
-/
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
lemma repush (hn:i<N)(hq: Q i hn.le=(Γ).push (R (i+1)).beta (Q (i+1) hn))
    (hI:Integrable (Q (i+1) hn) (prior G _)) (L:Fibers I J) :
    (fun U=> Fibers.reap (partialGroup V L) (Q i hn.le U))=(Γ).push (R (i+1)).beta (fun U=>Fibers.reap (partialGroup V L) (Q (i+1) hn U)):=by
    rw [hq]; funext U; unfold StepData.push; let M:= (Fibers.reap (partialGroup V L)).restrictScalars ℝ; have he:= M.integral_comp_comm (StepData.push_slice (A.levels.transition_mass i p (A.β N p (i+1))) U _ hI); simp_rw [M.map_smul] at he; exact he.symm
lemma reap_live (hn:i≤N) (hp:Integrable (Q i hn) (prior G _))(L:Fibers I J): Integrable (fun U=>Fibers.reap (partialGroup V L) (Q i hn U)) (prior G _):=
    ((Fibers.reap (partialGroup V L)).restrictScalars ℝ).integrable_comp hp

lemma size_enough (A:History G)(i:ℕ): (2:ℝ)≤ ((A.S.block i).val:ℝ):=by exact_mod_cast (le_trans (by norm_num) (A.S.block_large i) : 2 ≤ (A.S.block i).val)
def compensation (A:History G)(H i j s:ℕ) (a w:ℝ):= (A.S.a j/A.S.a i)^(4*H)*(a/8)^(H*(H-s))*w
variable {a w:ℝ} {s:ℕ}
lemma comp_pos (ha:0 < a)(hw:0<w): 0< compensation A H i j s a w := mul_pos (mul_pos (pow_pos (div_pos (A.S.a_pos _) (A.S.a_pos _)) _) (pow_pos (by positivity) _)) hw
lemma compensated (p:ℕ)(hf:Fintype.card I ≤ H)(ha:0 < a)(hw:0<w)(hW:compensation A H (i+1) j s a w ≤ ∏ x,W x):
    compensation A H i j s a w ≤ ∏ x,W x/(L' i)^4:=by
    have ht : A.S.a i=A.S.a (i+1)*L' i:=(A.S.embeds_scale (A.S.oneStep i p)).symm
    let S:= L' i; let y b:= compensation A H b j s a w
    have hy b: 0< y b:=comp_pos ha hw; have hp:2 ≤ S:= size_enough A i
    have hZ: 0<S:=by linarith only [hp]
    have hz:y i*S^(4*H)=y (i+1):=by unfold y compensation; rw [ht,← div_div]; simp only [div_pow]; field_simp <;> ring
    rw [prod_div_distrib,prod_const,card_univ,← pow_mul,le_div_iff₀ (by change 0<S^(4*Fintype.card I); positivity)]; refine le_trans ?_ hW; change y i*S^(4*Fintype.card I) ≤ y (i+1); rw [← hz]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_two.trans hp) (Nat.mul_le_mul_left 4 hf)) (hy i|>.le)
lemma compensated_joint {α:ℕ}{K:Fibers I J} (h: Fintype.card I ≤ H)(ht:Fintype.card J<Fintype.card I)(ha:0<a)(hx:a≤1)(hw:0<w)
    (hr:a ≤ license A δ H α i) (hW:compensation A H i j (Fintype.card I) a w ≤ ∏ x,W x):
    compensation A H i j (Fintype.card J) a w ≤ ∏ x,grouped A δ H α i W K x/8:=by
    let y b:= compensation A H i j b a w; let p:= Fintype.card I; let q:= Fintype.card J; let t:= a/8
    have hy b: 0< y b:=comp_pos ha hw; have hF:0<t:=div_pos ha (by norm_num); have hG:t ≤ 1:= by unfold t; linarith only [hx];
    have hV: 0 < license A δ H α i:=ha.trans_le hr
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
         _ ≤ _ := mul_le_mul (hg.trans (pow_le_pow_left₀ ha.le hr _)) hW (hy p|>.le) (pow_pos hV _|>.le)
variable (h:A.Selected)(ht:Thor A δ r D σ χ k)(hF:Brine A k δ φ)
variable (hm:k ≤ m) (hj:j ≤ N)
    (hΔ:∀ i:ℕ, m ≤ i→∀ hi:i<j,Q i (hi.le.trans hj)=(A.levels.clock.op i p).push (A.rep N p (i+1)).beta (Q (i+1) (hi.trans_le hj)))
    (hI:∀ i:ℕ,m ≤ i→∀ hi:i ≤ j, Integrable (Q i (hi.trans hj)) (prior G _))
    (he:∀ i:ℕ,m  ≤  i→∀ hi:i ≤ j, ClusterPars A δ χ r i) (hx:∀ i:ℕ,m ≤ i→i<j→φ i ≤ 1)
    (hG:∀ i:ℕ,m ≤ i→i ≤ j→0<r i) (hp:Migrating A m p j E)
    (hE:∀ i,m ≤ i→i<j→(A.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i)
    (hD:∀ (i:ℕ),m  ≤  i→∀ hi:i<j,MergeProof.Float.Runs (D N p i (hi.trans_le hj)) (A.levels.clock.op i p) (6*((A.S.block i).val:ℝ)))
    (hΩ:∀ i,m ≤ i→i ≤ j→ Collar (o i) v (E i) P)
    (hB:∀ i,m ≤ i→i ≤ j→ Cross (A.levels.budget i).B (o i))
    (ha:0<a)(hb:a ≤ 1)(hS:∀(i:ℕ),m ≤ i→ i<j→ a  ≤  license A δ H (carpet A i) (i+1))
include h ht hm hj hΔ hI hx hG hp hE hD hΩ hF
lemma Under.pass_L {W':J→ℝ}{c':V×J→ℂ} (hi:m ≤ i)(hh:i<j)(hc:Under A N p E (fun x=>o x ∘ (partialGroup V L).twig) P v B (fun x hx U=> Fibers.reap (partialGroup V L) (Q x hx U)) (i+1) (hh.trans_le hj) W' c') (hZ:Edition.Spaced (Y' i).B (o i ∘ (partialGroup V L).twig)) : Live A N p E (fun x=>o x ∘ (partialGroup V L).twig) P v B (fun x hx U=> Fibers.reap (partialGroup V L) (Q x hx U)) δ χ i (hh.le.trans hj) (fun j=>W' j/(L' i)^4) c':=by
    let G:=(partialGroup V L).twig; have hr:(Γ).ratio.parent ∘ o (i+1) ∘ G=o i ∘ G:=by rw [← hE i hi hh]; rfl
    have hz:Injective (o i ∘ G):=Edition.injected _ _ (Y' i|>.B_pos) hZ; have hX:Injective (o (i+1) ∘ G):= Injective.of_comp (f:=(Γ).ratio.parent) (hr.symm ▸ hz)
    have hφ:0<L' i:=lt_of_lt_of_le zero_lt_two (size_enough A i)
    refine Under.evens h ht (hm.trans hi) (hh.trans_le hj) hc (hp.mare i hi hh|>.symm) ((hΩ _ (hi.trans i.le_succ) hh).shrunk L) (repush _ (hΔ i hi hh) (hI _ (hi.trans i.le_succ) hh) L) (reap_live _ (hI _ (hi.trans i.le_succ) hh) L) hr (fun y=> (Occupancy.of_injective hX y).trans (hG i hi hh.le)) (fun y=>(Occupancy.of_injective hz y).trans (hG i hi hh.le)) (hD i hi hh) (by linarith only [size_enough A i]) ⟨fun _ _ i _ j _=>hZ i j⟩ hF (hx i hi hh) (fun b=>?_ ) (fun b=> div_pos (hc.width b) (by positivity))
    rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2
    rw [pow_succ, mul_comm (6*L' i)]; apply mul_le_mul_of_nonneg_left _ (hc.width b|>.le); refine mul_le_mul_of_nonneg_right ?_ hφ.le; calc _  ≤  (2:ℝ)^3:=by norm_num
                                                                                                                                                _  ≤  _:=pow_le_pow_left₀ zero_le_two (size_enough A i) _

variable (hH:Fintype.card I=H) (hT:Edition.Spaced (A.levels.budget j).B (o j)) (i₀:I) (hY:Live A N p E o P v B Q δ χ j hj W c)
include hH hT hY ha hb hS he hB
local notation "Q*" => Q -- composition
lemma inductionLive (hi:m ≤ i)(hJ:i ≤ j) :
    ∃ (J:Type)(_ : Fintype J)(_ : DecidableEq J)(F:Fibers I J)(X:J→ℝ)(s:V×J→ℂ), F.twig (F.bunch i₀)=i₀ ∧ Edition.Spaced (Y' i).B (o i ∘ (partialGroup V F).twig) ∧
      Live A N p E (fun i=>o i ∘ (partialGroup V F).twig) P v B (fun x hx U=>Fibers.reap (partialGroup V F) (Q x hx U)) δ χ i (hJ.trans hj) X s ∧ compensation A H i j (Fintype.card J) a (∏ x,W x)  ≤  ∏ x,X x:=by
    have hW:0<∏ x,W x:= Finset.prod_pos fun i _=> hY.width i
    induction hJ using Nat.decreasingInduction with
    | self=> refine ⟨I,inferInstance,inferInstance,Fibers.same I,W,c,rfl,?_,?_,?_⟩
             · exact hT
             · rw [show (fun (x:ℕ)(hx:x ≤ N)(U: Config G (A.S.side x p))=>Fibers.reap (partialGroup V (Fibers.same I)) (Q x hx U)) =Q from funext fun x=> funext fun hx=> funext fun U=> Fibers.same_reap _]; exact hY
             unfold compensation; rw [← hH, Nat.sub_self,mul_zero,div_self (A.S.a_pos j).ne',pow_zero,one_pow,mul_one,one_mul]
    | of_succ i hJ IH=>
       obtain ⟨T,cX,cY,L,W',c',hZ,hP,hU,hL⟩:=IH (hi.trans i.le_succ)
       have hu: Fintype.card T  ≤  H:= (Fintype.card_le_of_surjective L.bunch L.sectioned.surjective).trans hH.le
       have hζ:0<H:= by rw [← hH]; exact Fintype.card_pos_iff.mpr ⟨i₀⟩
       by_cases hA:Edition.Spaced (Y' i).B (o i ∘ (partialGroup V L).twig)
       · exact ⟨T,cX,cY,L,_,c',hZ,hA,Under.pass_L h ht hF hm hj hΔ hI hx hG hp hE hD hΩ hi hJ hU.toUnder hA,compensated p hu ha hW hL⟩
       let o' x:=o x ∘ (partialGroup V L).twig; have hh:(A.levels.clock.op i p).ratio.parent ∘ o' (i+1)=o' i:=by unfold o'; rw [← hE i hi hJ]; rfl
       obtain ⟨J,cH,cK,S,hJ',hU',hq,hΨ⟩:= selectIf (L.bunch i₀) A (E i) P v (o' i) (o' (i+1)) ((hΩ i hi hJ.le).shrunk L) ((hB i hi hJ.le).shrunk L) hh hA
       let l:= carpet A i; let F:= L.comp S
       have hσ:=hi.trans i.le_succ
       have hA':= hU.gathers _ l S h (hJ.trans_le hj) (he _ hσ hJ) (ht.moon N p i (hm.trans hi) (hJ.trans_le hj)).1.contact hζ hu (fun y=>(Occupancy.of_injective (Edition.injected _ _ (Y' _|>.B_pos) hP) y).trans (hG _ hσ hJ)) ((hΩ _ hσ hJ).shrunk L) hΨ
       have hℓ:F.twig (F.bunch i₀)=i₀:= by unfold F Fibers.comp; dsimp only [comp_apply]; rw [hJ',hZ]
       let q' x (hx:x ≤ N) U:= Fibers.reap (partialGroup V F) (Q x hx U)
       have hχ:q' = (fun x hx U=> Fibers.reap (partialGroup V S) (Fibers.reap (partialGroup V L) (Q x hx U))):= funext fun x=> funext fun hx=> funext fun U=> (Fibers.comp_reap (partialGroup V L) (partialGroup V S) (Q x hx U)).symm
       refine ⟨J,cH,cK,F,_,0,hℓ,hq,Under.pass_L h ht hF hm hj hΔ hI hx hG hp hE hD hΩ hi hJ ((hχ.symm ▸ hA'):Under A N p E (fun x=>o x ∘ (partialGroup V F).twig) P v B q' _ _ _ _) hq,?_⟩
       exact compensated p (hU'.le.trans hu) ha hW (compensated_joint hu hU' ha hb hW (hS i hi hJ) hL)
end YM.MergeProof.Ribbons.ManyCopies
