import YM.RG08.Run.Weather
/-! # Back trajectory and scan exposure post (only strict).
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {I E : Type}{α β : I→Type}{r s D τ n i k t e : ℕ}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
variable {y ρ δ η w v b : I→ℝ}
section
variable [∀ i,Fintype (α i)] [∀ i,Fintype (β i)] {V U: ∀ i,Rooted E (α i) r} {K:Fin r→∀ i, Row (α i) (β i)}{P Q:∀ i,Row (α i) (β i)}
lemma marks_cost (h:Card k y ρ V v)(hv:0 ≤ v)(hx:v ≤ 1)(hw:∀ i,0<w i)(hp:Weighed y (fun i=> (Fintype.card (β i):ℝ)))(he:Weighed y (fun i=>utter k (w i))){δ: Fin r→ I→ℝ}(hδ:∀ i,0 ≤ δ i)(hk:∀ i,SafeRow y (δ i) (K i) w) : Card k y (fun i=>(∏ j,δ j i)*ρ i) (fun i=>rhyme (V i) (fun j=> K j i)) v := by
   choose C hC H using hk; obtain ⟨B,hB,Hz⟩:=h.money
   refine ⟨_,(((hp.powers r).times (he.powers r)).times (Weighed.prod univ fun i _=>hC i)).times hB,fun i=> Ink.raise (stage_l (Hz i) (hv i) (hx i) (hw i) (fun j=>H j i) (fun j=>mul_nonneg ((hC j).positive i) (hδ j i))) (le_of_eq ?_)⟩
   simp only [Pi.mul_apply,prod_mul_distrib]; ring
lemma marks_buy (h:Card k y ρ V v)(hv:0 ≤ v)(hx:v ≤ 1)(hw:∀ i,0<w i)(hp:Weighed y (fun i=> (Fintype.card (β i):ℝ)))(he:Weighed y (fun i=>utter k (w i)))(hk:SafeRow y 1 Q w) : Card k y ρ (fun i=>rhyme (V i) (fun j=> Q i)) v := by simpa only [Pi.one_apply,prod_const_one,one_mul] using marks_cost h hv hx hw hp he (fun _ _=> show _≤_ from zero_le_one) (K:=fun _=>Q) (fun _=>hk)
lemma marks_pair (h:Drum k y δ ρ V U v)(hv:0 ≤ v)(hx:v ≤ 1)(hw:∀ i,0<w i)(hp:Weighed y (fun i=> (Fintype.card (β i):ℝ)))(he:Weighed y (fun i=>utter k (w i)))(hz:Audience y)(hk:RowBoth y δ P Q w)(hδ:0 ≤ δ) : Drum k y δ ρ (fun i=>spring (V i) (P i)) (fun i=>spring (U i) (Q i)) v:= by
   have h1:=hk.fresh.status hw; have h2:=hk.again.status hw
   suffices he:Drum k y δ ρ (fun i=>rhyme (V i) (fun _=>P i)) (fun i=> rhyme (U i) (fun _=>Q i)) v from he.sewn hv
   refine ⟨marks_buy h.first hv hx hw hp he hk.fresh,marks_buy h.second hv hx hw hp he hk.again,?_⟩
   let M (s:Finset (Fin r)) (j: Fin r) := if j∈s then Q else P
   let W (s:Finset (Fin r)) i:= rhyme (U i) (fun j=> M s j i)
   have hM(s:Finset (Fin r))(j): SafeRow y 1 (M s j) w := by unfold M; split; exact hk.again; exact hk.fresh
   have hh (s:Finset (Fin r)): Card k y (δ*ρ) (W ∅- W s) v := by
    induction s using Finset.induction_on with
    | empty=> rw [sub_self]; exact Card.zero
    | insert j s hj ih=>
      let b : Fin r→I→ℝ:= fun i=>if i=j then δ else 1
      let A a:= if a=j then P-Q else M s a
      let R i:= rhyme (U i) (fun j=> A j i); have hu i: SafeRow y (b i) (A i) w:= by unfold A b; split; exact hk.moves; exact hM s i
      have ht:= marks_cost h.second hv hx hw hp he (fun i=> (show 0≤b i by unfold b; split; exact hδ; exact fun _=>zero_le_one)) hu
      have he : Card k y (δ*ρ) R v:= ht.raise (fun i=>le_of_eq (by change (∏ j,b j i)*ρ i=δ i*ρ i; rw [prod_eq_single j]; simp [b]; intro k _ hk; simp [b,hk]; simp))
      have hb i: R i=W s i-W (insert j s) i:= by
        unfold R W; let a : Fin r→Row (α i) (β i):=fun k=> M s k i; let B := fun k=> M (insert j s) k i
        rw [show (fun j=> A j i)= update a j (a j-B j) from funext fun k=> by by_cases hp:k=j <;> simp [M,hp,B,a,hj,A]] -- U not let
        exact rhyme_variation (h.second.even hv i) (fun p=> (hM s p).status hw i) (fun p=> (hM _ p).status hw i) j (fun k hk=> by simp [M,hk])
      convert ih.more he hv hz using 1; funext i; rw [Pi.add_apply,hb]; exact (sub_add_sub_cancel ..).symm
   let A i:= rhyme ((V-U) i) (fun _=> P i)
   rw [show _-_ = A+(W ∅-W univ) from funext fun i=>?_]; · exact (marks_buy h.funds hv hx hw hp he hk.fresh).more (hh univ) hv hz
   simp only [A,W,M,Pi.sub_apply,Pi.add_apply,rhyme_sub (h.first.even hv i) (h.second.even hv i) (fun _=>h1 i),mem_univ,notMem_empty,↓reduceIte,sub_add_sub_cancel]
end
section growth
variable {R C θ σ A :ℝ}{L: Side}{G:Gauge}{U : BoardU D R G}
lemma plank_r (z:Site L)(h: cis k θ (U e r) A)(hx:1/2≤R)(hz:Odd L.val)(hp:0≤σ)(ht:σ≤1)(he:σ/L.val≤θ): cis k σ (raysF z (U e r)) (((Fintype.card (Park G L):ℝ)^r*(utter k 1)^r)*((1+4*(r:ℝ))^k*A)) := by
  let X i:= readdress (U e r i) z
  have hθ:0≤θ:= (div_nonneg hp (by positivity)).trans he
  have hX : cis k θ X A:= budget_mono h (fun i=>mul_nonneg (zero_le_one.trans (tailp hθ i)) (norm_nonneg _)) fun i=> mul_le_mul_of_nonneg_left (read_scores hz hx z _).1 (zero_le_one.trans (tailp hθ i))
  have ht:= stage_l (plank_m z hX hp ht he) hp ht one_pos (Q:=fun _=>skylight (Co L (Loc G 1)) (Loc G 1)) (fun _=> skylight_price) (fun _=> zero_le_one)
  simpa only [prod_const_one,mul_one] using! sew_cis ht hp
lemma cream_cis (h: cis k θ (U e r) A)(hx:1/2≤R)(hz:Odd L.val)(hp:0≤σ)(ht:σ≤1)(he:σ/L.val≤θ) (t): cis k σ (cream t U L e r) (((L.val:ℝ)^t)*((Fintype.card (Park G L):ℝ)^r*(utter k 1)^r)*((1+4*(r:ℝ))^k*A)) := by
   unfold cream reelF; apply Ink.raise (Ink.additions (fun i _=>Ink.scale (plank_r i h hx hz hp ht he) _) (zero_le_one.trans (tailp hp))); rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]; apply le_of_eq; field_simp
variable {F H:I→ BoardU D R G}{L:I→Side}
lemma wing_cis (h:Card k y ρ (fun i=> F i e r) η)(hx:1/2≤R)(hz:∀ i,Odd (L i).val)(hw:0 ≤ w)(hp:w ≤ 1)(he:∀ i,w i/(L i).val≤η i)(hv:Audience y)(hl: Weighed y (fun i=> ((L i).val:ℝ))) : Card k y ρ (fun i=>cream t (F i) (L i) e r) w := by
    obtain ⟨A,hA,H⟩:=h.money
    have hP:0 ≤ utter k 1:=utter_pos one_pos
    refine ⟨_, ((hl.powers t).times (((fiscal_lot (G:=G) hl hv).powers r).times (Weighed.constant y (show 0≤(utter k 1)^r by positivity)))).times ((Weighed.constant y (show 0≤(1+4*(r:ℝ))^k by positivity)).times hA),fun i=> Ink.raise (cream_cis (U:=F i) (H i) hx (hz i) (hw i) (hp i) (he i) t) (le_of_eq ?_)⟩ -- H
    simp only [Pi.mul_apply,mul_assoc]
lemma wing_drum (h:Drum k y δ ρ (fun i=>F i e r) (fun i=>H i e r) η)(hx:1/2≤R)(hz:∀ i,Odd (L i).val)(hw:0 ≤ w)(hp:w ≤ 1)(he:∀ i,w i/(L i).val≤η i)(hv:Audience y)(hl:Weighed y (fun i=> ((L i).val:ℝ))) : Drum k y δ ρ (fun i=>cream t (F i) (L i) e r) (fun i=>cream t (H i) (L i) e r) w:= by
    have ht:0≤η:=fun i=> le_trans (div_nonneg (hw i) (by positivity)) (he i)
    constructor
    · exact wing_cis h.first hx hz hw hp he hv hl
    · exact wing_cis h.second hx hz hw hp he hv hl
    rw [show _-_ =(fun i=>cream t (F i-H i) (L i) e r) from funext fun i=>?_]; exact wing_cis h.funds hx hz hw hp he hv hl
    rw [Pi.sub_apply]; unfold cream reelF; simp_rw [Pi.sub_apply, rays_sub (h.first.even ht i) (h.second.even ht i) hx (hz _),smul_sub,sum_sub_distrib]
end growth
end YM.RG08.Run
