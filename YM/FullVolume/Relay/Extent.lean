import YM.FullVolume.Relay.Calder
import YM.FullVolume.Relay.Raw
/- At the integrating stop, all support costs are allowed fixed-period
 combinatorial constants. Do not charge any UV volume here. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac GridApprox.Nil
open PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam MeasureTheory
variable {G:Gauge}{n:Side}{V X I:Type}[DecidableEq V][Fintype V][Fintype I]
variable {B:Marker.Census V}{w: V→ℝ}(hw:∀ i,0<w i){F:sun→ X→Poly B}{u v z:ℝ}
namespace LeafPaid
lemma mark (p:B.Mode)(f:sun→ X→ℂ) (h:Feel f v): LeafPaid w (fun s x=>Poly.send p (f s x)) (Poly.toll w p*v):=by
    let y(i:B.Mode):= if i=p then v else 0; refine ⟨y,fun i=>?_,?_,fun j=>?_⟩
    · unfold y; split; exact h.positives; rfl
    · simp [wordsPrice,y,mul_ite]
    simp_rw [Poly.part_send]; unfold y; split; exact h; exact Feel.staticC (fun _=>0) le_rfl (fun _=> norm_zero.le)
lemma higher (h:LeafPaid w F u)(ha:u≤v): LeafPaid w F v:=by obtain ⟨z,hp,h,H⟩:=h; exact ⟨z,hp,h.trans ha,H⟩
lemma twin {G:sun→X→Poly B}(h:LeafPaid w F u)(hp:LeafPaid w G v): LeafPaid w (fun s x=> F s x+G s x) (u+v):=by
    obtain ⟨f,hf,h,hX⟩:=h; obtain ⟨g,hg,hQ,hY⟩:=hp
    refine ⟨f+g,add_nonneg hf hg,?_,fun i=>?_⟩
    · unfold wordsPrice; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add h hQ
    simp_rw [Poly.part_plus]; exact Feel.united (hX i) (hY i)
include hw
lemma resume (h:LeafPaid w F u)(k:ℕ): LeafPaid w (fun s x=> F s x^k) (u^k):=by
    induction k with
    | zero=> simp only [pow_zero]; simpa using! LeafPaid.solo (B:=B) (X:=X) (w:=w) 1
    | succ k ih=> simp_rw [pow_succ]; exact ih.mixP hw h
lemma school (h:LeafPaid w F u){f:sun→ X→ℂ}(ht:Feel f v): LeafPaid w (fun s x=> f s x • F s x) (v*u):=by
    have hV : LeafPaid w (fun s x=> Poly.bead B (f s x)) v:= by
       have h':= LeafPaid.mark B.quiet f ht (w:=w); rw [Poly.quiet_toll, one_mul] at h'; exact h'
    simp_rw [← Poly.product_bead]; exact hV.mixP hw h
lemma pass (h:LeafPaid w F u):LeafPaid w (fun s x=> Poly.pass (F s x)) (Real.exp u):=by
    unfold Poly.pass
    have hh : HasSum (fun i:ℕ=>u^i/i.factorial) (Real.exp u):=by rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp u
    have ht := hh.summable.sum_le_tsum (Finset.range (Fintype.card V+1)) (fun i _=> div_nonneg (pow_nonneg (LeafPaid.pricesN hw h) _) (Nat.cast_nonneg _))
    apply LeafPaid.higher _ (ht.trans hh.tsum_eq.le)
    apply LeafPaid.daisy (w:=w) (F:=fun (i:ℕ) s x=> (i.factorial:ℂ)⁻¹ • F s x ^i) (s:=range (Fintype.card V+1)); intro i _; let P:ℂ:=(i.factorial:ℂ)⁻¹
    have he : Feel (fun (_:sun) (_:X)=>P) ‖P‖:=Feel.staticC _ (norm_nonneg _) (fun _=> le_rfl)
    convert! LeafPaid.school hw (LeafPaid.resume hw h i) he using 1; simp [P, div_eq_mul_inv, mul_comm]

lemma used (h:LeafPaid w F u)(t:B.Mode): Feel (fun s x=> (F s x).part t) (u / Poly.toll w t):=by
    obtain ⟨f,hf,hv,h⟩:=h
    apply Feel.earns (h _); rw [le_div_iff₀ (Poly.worth hw t),mul_comm]; exact (single_le_sum (fun i _=>mul_nonneg (Poly.worth hw i).le (hf i)) (mem_univ _)).trans hv
end LeafPaid
variable (F₀:sun→ Box n→ Config G n→Poly B)
variable {x: V → Site n}{a c d p:ℝ}{k:ℕ}(hp:0≤p)(ha:0≤a)
abbrev allpriceG (n:Side)(v:ℝ):ℝ:=∑ s:Finset (Box n), v^s.card
include hw ha hp
lemma globalK (h:∀ s i,Flow x i (F₀ s i) c) (ht:Polaris w Prod.fst F₀ k p a): LeafPaid w (fun s U=> field (fun i=> F₀ s i U) (flags c U)) (allpriceG n a):=by
    unfold field
    apply LeafPaid.daisy (s:=Finset.univ) (F:=fun i s (U:Config G n)=> grid (fun i=> F₀ s i U) (flags c U) i)
    obtain ⟨z,hz,hV,hB⟩:= ht
    have hK i: LeafPaid w (fun s=> F₀ s i) a:=by
       cases i with| mk i y=>
        by_cases hr:i.Nonempty
        · obtain ⟨v,ht⟩:=hr; apply LeafPaid.higher (hB _)
          have he(v₀:Box n):0 ≤ z v₀:= LeafPaid.pricesN hw (hB _)
          apply le_trans (b:= z (i,y)*Real.exp (p*coverNumber k i)) (le_mul_of_one_le_right (he _) (Real.one_le_exp (mul_nonneg hp (by positivity))))
          have hh:= budget_single (hV v) (i,y); rw [if_pos (show _ from ht)] at hh; exact hh
        have hX(s U): F₀ s (i,y) U=0:=of_not_not (fun hh=> hr (let h:= (h ..|>.permits _ hh).2; h.1.mono h.2))
        rw [show (fun s=>F₀ s (i,y))=0 from funext fun s=> funext fun U=> hX s U]; exact LeafPaid.higher LeafPaid.silence ha
    intro i _
    let S : Set (Config G n):= {u | Pattern (flags c u) i}
    have he(s:sun) U: grid (fun i=> F₀ s i U) (flags c U) i= S.indicator (fun U=> ∏ j∈i,F₀ s j U) U:=by
         unfold grid; split; next h=> exact (indicator_of_mem (show U∈S from h) (fun U=> ∏ j∈ i,F₀ s j U)).symm
         next h=> exact (indicator_of_notMem (show U∉ S from h) (fun U=>∏ j∈i,F₀ s j U)).symm
    change LeafPaid _ (fun s:sun=> fun U=> _) _; simp_rw [he]
    have ht:= LeafPaid.cutoff S (LeafPaid.bags hw i (fun j s=> F₀ s j) (fun _=>a) (fun j _=> hK j)); rw [prod_const] at ht; exact ht
-- total over E-hot & Singles weighted.
variable {F': sun→ I→ Config G n→Poly B}{S:I→ Support n}
omit ha
lemma globalHot (hf:Pact w S F' (multiple B) k p u) : LeafPaid w (fun s U=>∑ i:I,G1 F' s i U) u:=by
    obtain ⟨z,hz,h⟩:= hf.coins
    let f(i:I)(s:sun)(x):= G1 F' s i x
    let b(i:I)(j:B.Mode):= if ht:j∈ multiple B then z (i,⟨j,ht⟩) else 0
    have H(i j): Feel (fun s x=>(f i s x).part j) (b i j):=by
         unfold b; split
         next hi=> unfold f G1; simp_rw [Accent.crest _ _ ((multiplicity _).1 hi)]; exact h (i,⟨j,hi⟩)
         next hi=> unfold f G1; simp_rw [Accent.starlet _ _ (lt_of_not_ge (fun h=> hi ((multiplicity _).2 h)))]; exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
    have ht i : LeafPaid w (f i) (wordsPrice w (b i)):= ⟨b i,fun j=> (H i j).positives,le_rfl,H i⟩
    refine LeafPaid.higher (LeafPaid.daisy f Finset.univ (fun i=> wordsPrice w (b i)) (fun i _=> ht _)) ?_
    rw [Fintype.sum_prod_type] at hz; apply le_trans _ hz; apply sum_le_sum; intro i _; unfold wordsPrice
    rw [← sum_subset (f:=fun j=> Poly.toll w j * b i j) (subset_univ (multiple B)) (fun j _ hj=> by unfold b;rw [dif_neg hj,mul_zero]),← sum_coe_sort]; apply sum_le_sum; intro j _; unfold b; rw [dif_pos j.property]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (Poly.worth hw _|>.le) (Real.one_le_exp (mul_nonneg hp (by positivity)))) (h _|>.positives)
lemma globalSingle {j' : B.Mode}(ht : Treasure (fun i=> Real.exp (p*coverNumber k (S i))) (receive F' j') v) : Feel (fun s (x:Config G n)=> ∑ i, (F' s i x).part j') v:=by
    obtain ⟨b,hb,hQ⟩:=ht.coins; apply Feel.earns (Feel.stacks _ (fun i s x=>(F' s i x).part j') b (fun i _=>hQ i)); exact le_trans (Finset.sum_le_sum (fun i _=> le_mul_of_one_le_left (hQ i|>.positives) (Real.one_le_exp (mul_nonneg hp (by positivity))))) hb
end YM.FullVolume.Nectar
