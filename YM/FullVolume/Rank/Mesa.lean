import YM.FullVolume.Panel.Spokes
import YM.FullVolume.Rank.Pairs
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι κ:Type}
namespace Credit
lemma funding [Fintype ι] {f g:ℕ→ι→ Config G n→ℂ}(h:∀ i,Credit (fun n (_:Unit)=>f n i) (fun n (_:Unit)=> g n i)): Credit f g:=by
   have hf {f:ℕ→ι→ Config G n→ℂ}(h:∀ i,Bill (fun n (_:Unit)=> f n i)): Bill f:= by
      choose v hv hp using fun i=> (h i).use; choose u hu using fun i=> (hv i).bound; exact ⟨_,Sparse.constant (hasSum_fintype u).summable (fun i=> Push.AbsoluteSums.budget_nonneg (hu i 0)),fun n i V=> (hp i n () V).trans (Push.AbsoluteSums.budget_single (hu i n) ())⟩
   exact ⟨hf (fun i=> (h i).left),hf (fun i=>(h i).right),fun i=> (h i).polls ()⟩
lemma logs {f g:ℕ→ι→ Config G n→ℂ}(h:Credit f g):Credit (fun i (_:Unit) U=>∑' j,f i j U) (fun i (_:Unit) U=>∑' j,g i j U):=by
    have hf {f:ℕ→ι→ Config G n→ℂ}(h:Bill f): Bill (fun i (_:Unit) U=>∑' j,f i j U):=by
       obtain ⟨v,hv,hX⟩:= h.use; obtain ⟨b,hb⟩:= hv.bound; refine ⟨_,Sparse.constant (show Summable fun _: Unit=>b from Summable.of_finite) (fun _=> Push.AbsoluteSums.budget_nonneg (hb 0)),fun n i U=>?_⟩; have hf:Summable fun j=> ‖f n j U‖:= Summable.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> hX ..) ((hb n).2.1)
       exact (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum (fun _=> hX ..) (hb n).2.1).trans (hb n).2.2)
    exact ⟨hf h.left,hf h.right,fun _=> h.elementary⟩
lemma hoop {f g:ℕ→ι→κ→ Config G n→ℂ}(h:∀ i,Credit (f · i) (g · i))[Fintype ι]: Credit (fun i=>∑ j,f i j) (fun i=>∑ j,g i j):=by -- works any κ
    suffices hf : ∀ s:Finset ι,Credit (fun i=> ∑ j∈s,f i j) (fun i=> ∑ j∈s,g i j) from hf _
    intro s; induction s using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact by have hp:Bill (fun (_:ℕ) (_:κ) (_:Config G n)=>0):= ⟨_,Sparse.constant (f:=fun _ : κ=> (0:ℝ)) (by simp) (fun _=>le_rfl),by simp⟩; exact ⟨hp,hp,fun i V=>by simp⟩ -- edit
    | insert i s hi ih=>simp_rw [Finset.sum_insert hi]; exact (h i).sum ih
lemma extendK {f g:ℕ→ι→ Config G n→ℂ}(h:Credit f g)(s:ι↪κ):Credit (fun n=> Function.extend s (f n) 0) (fun n=>extend s (g n) 0):=by
    have hx {f:ℕ→ι→ Config G n→ℂ}(h:Bill f):Bill fun n=>Function.extend s (f n) 0:=by
       obtain ⟨v,hv,H⟩:=h.use; refine ⟨_,Ledgers.hopper hv s,fun n i U=>?_⟩; by_cases he:i∈ Set.range s
       · obtain ⟨x,rfl⟩:=he; rw [s.injective.extend_apply,Progress.DirectedRecipe.stuffed]; exact H ..
       rw [extend_apply' _ _ _ he,Progress.DirectedRecipe.blank _ _ he]; simp
    refine ⟨hx h.left, hx h.right,fun i V=>?_⟩; by_cases ht:i∈ Set.range s
    · obtain ⟨x,rfl⟩:=ht; simp_rw [s.injective.extend_apply]; exact h.polls ..
    simp_rw [extend_apply' _ _ _ ht];simp
end Credit
-- Read atlas.Typed norm.Coeff.M. static Layout. each orientation actual output dealt.Spends.
namespace Col
variable {B:SectionData F}{R R':ℕ→ Rep G n}(h:∀ n, Along S.orient (R n))(hp:∀ n,Along S.orient (R' n))
variable {U:ℕ→Support n} {V W: ℕ→ Local.Raw F n} {v k κ l σ C a b:ℝ}
set_option quotPrecheck false
local notation "P'"=> S.orient.p
open Neptune
variable (ht:Readable A B S.orient.p n v)(he:SeatE (fun n=> (V n).bulk) (fun n=> (W n).bulk) S.orient.p U)(hv: Credit (fun n=>(V n).forced) (fun n=>(W n).forced))(hg: Angel (fun n=>(R n).activities.K) (fun n=>(R' n).activities.K))(hf:∀ n, (R n).Lawful σ C b a k)(hf':∀ n,(R' n).Lawful σ C b a k)
   (K: ∀ n,Keeper (R n).p (R n).activities)(K':∀ n,Keeper (R' n).p (R' n).activities) (H:∀ n,Have (R n) (V n) U B A v k S.k)(H':∀ n,Have (R' n) (W n) U B A v k S.k)
local notation "p₀"=> fun n=> Matric.gala (K n) B A (V n) U
local notation "p₁"=> fun n=> Matric.gala (K' n) B A (W n) U
private lemma subtr (X:Support n) {B:BudgetPoint}{f g: Config G n→ℂ}(hf:B.Regular X f)(hp:B.Regular X g)(w:ℝ)(he:d ≤ B.order) : weighted A F 0 X w (f-g) = weighted A F 0 X w f-weighted A F 0 X w g:=by
    unfold weighted; rw [ Local.project_eq (reads_sub (project_reads _ 0 hf he) (project_reads _ 0 hp he)),map_sub,map_sub]
include K K' h hp ht he
lemma minted (ha:Tendsto (fun n=> (V n).seed- (W n).seed) atTop (𝓝 0)): Tendsto (fun n=> (p₀ n).1-(p₁ n).1) atTop (𝓝 0):=by
    let f n:= (V n).row 0 U A (P').threshold; let g n:=(W n).row 0 U A (P').threshold
    have hV n:(p₀ n).1=(V n).seed+∑' i,f n i:=by unfold f; rw [show (P').threshold= _ from congr_arg BudgetPoint.threshold (h n).price]; rfl
    have hV' n:(p₁ n).1=(W n).seed+∑' i,g n i:=by unfold g; rw [show (P').threshold= _ from congr_arg BudgetPoint.threshold (hp n).price];rfl
    let A':=readPrice A F; have hx:0<A':=zero_lt_one.trans_le (readPrice_pos ..)
    have hL {X:ℕ→Local.Raw F n}(h:SumE (fun n=>(X n).bulk) (P') U): Sparse (fun n i=> ‖(X n).row 0 U A (P').threshold i‖):=by
        obtain ⟨v,hv,V⟩:=h.pay; exact (hv.climb hx.le).smaller (fun i _=> norm_nonneg _) (fun i n=> (Local.norm_le_size ..).trans (weighted_bound A F 0 (h.reg ..) ht.order ht.power (V ..)))
    simp_rw [hV,hV',add_sub_add_comm]; convert (ha.add (fisher (f:=f) (g:=g) (hL he.vista) (hL he.vests) ?_)) using 1; rw [add_zero]
    intro j; refine Metric.tendsto_nhds.mpr fun ε H=>?_ ; let v:= ε/2; have hx':0 < v/A':= div_pos (half_pos H) hx
    filter_upwards [he.cost j _ hx'] with n hn
    have hf:f n j-g n j= _:= (subtr (U j) (A:=A) (F:=F) (he.vista.reg n j) (he.vests.reg n j) ((P').threshold) ht.order).symm
    rw [dist_zero_right,hf]; exact lt_of_le_of_lt ((Local.norm_le_size ..).trans ((weighted_bound A F 0 (regular_sub (he.vista.reg ..) (he.vests.reg ..)) ht.order ht.power hn).trans_eq (by change A'*(v/A')=v; field_simp))) (half_lt_self H)
-- upgrades through uniform projection price.Read.Also forcible rebate.Term.Domain. Dist.New.S path.
local notation "J"=> fun i=> joint B 0 (U i)
local notation "R₀"=>fun n=> mint ((K n).supply J) (V n) A
local notation "R₁"=> fun n=> mint ((K' n).supply J) (W n) A
local notation "α"=>S.orient.p.threshold
local notation "Q₀"=>fun n i=> Push.Local.residual A B 0 (U i) α ((V n).bulk i)
local notation "Q₁"=>fun n i=> Push.Local.residual A B 0 (U i) α ((W n).bulk i)
local notation "q₀"=> fun n i=> rebate A B 0 (U i) α ((V n).bulk i)
local notation "q₁"=>fun n i=> rebate A B 0 (U i) α ((W n).bulk i)
omit K K' hp h
lemma rebukes : SeatE Q₀ Q₁ P' J ∧ Credit q₀ q₁:=by
   let x:= atomPrice A F v; have hx:0<x:=zero_lt_one.trans_le (atomPrice_ge_one _ _ ht.nonneg)
   have hv {V :ℕ→Local.Raw F n}(hv:SumE (fun i=> (V i).bulk) P' U) : SumE (fun n i=> Push.Local.residual A B 0 (U i) α ((V n).bulk i)) P' J ∧ Bill (fun n i=> rebate A B 0 (U i) α ((V n).bulk i)):=by
       obtain ⟨w,hw,hW⟩:= hv.pay; have hp n i:=charge_atom 0 ht (hv.reg n i) (hW n i); exact ⟨⟨fun n i=> (convert_atom 0 ht (hv.reg ..)).1,_,hw.climb hx.le,fun n i=> (hp n i).1⟩,⟨_,hw.climb hx.le, fun n i=>(hp n i).2⟩⟩
   obtain ⟨hf,hf'⟩:=hv he.vista;obtain ⟨hg,hg'⟩:=hv he.vests
   let f n i:=(V n).bulk i; let g n i:=(W n).bulk i; have hR n i: residual A B 0 (U i) α (f n i-g n i)=(Q₀ n i)-(Q₁ n i) :=by unfold Push.Local.residual; rw [subtr _ (he.vista.reg n i) (he.vests.reg n i) _ ht.order,map_sub];exact sub_sub_sub_comm ..
   have hψ n i: rebate A B 0 (U i) α (f n i-g n i)=(q₀ n i)-(q₁ n i):=by
       unfold rebate; rw [show residual A B 0 (U i) α (f n i-g n i)=_ from hR n i, subtr _ (he.vista.reg n i) (he.vests.reg n i) _ ht.order,map_sub, show masked α (U i) (f n i-g n i)=_ from (map_sub (maskLinear α (U i)) (f n i) (g n i)), show masked α (J i) (Q₀ n i-Q₁ n i)=_ from (map_sub (maskLinear α (J i)) (Q₀ n i) (Q₁ n i))];unfold f g; simp only [Local.maskLinear, LinearMap.coe_mk, AddHom.coe_mk]; abel
   refine ⟨⟨hf,hg,fun i b hb=> ?_⟩,⟨hf',hg',fun i V=> Metric.tendsto_nhds.mpr fun ε hε=>?_⟩⟩
   · filter_upwards [he.cost i _ (div_pos hb hx)] with n hn; rw [← hR];exact bound_weaken ((charge_atom 0 ht (regular_sub (he.vista.reg ..) (he.vests.reg ..)) hn).1) (by change x*(b/x)≤b; field_simp;norm_num)
   filter_upwards [he.cost i _ (div_pos (half_pos hε) hx)] with n hn; rw [dist_zero_right, show q₀ n i (V n)- q₁ n i (V n) = _ from congr_fun (hψ n i).symm (V n)] -- V collision.M macro V.
   refine lt_of_le_of_lt (((charge_atom 0 ht (regular_sub (he.vista.reg ..) (he.vests.reg ..)) hn).2 _).trans ?_) (half_lt_self hε); change x*(ε/2/x)≤ _; field_simp; norm_num
include h K H hf hp K' H' hf'
lemma collected : SeatE (fun n=> (p₀ n).2.1) (fun n=> (p₁ n).2.1) P' (mapSeat (n:=n)):=by
   let X:= tongue J; have hx i: mapSeat (X i)=J i:= leased (R₀ 0) (usage _ (H 0).format (hf 0) ((h 0).price ▸ ht)) i -- P.Pre should `(H 0).format`. ok
   have hu(n): (p₀ n).2.1= Progress.DirectedRecipe.stuff X (Q₀ n):=by
      let u(i):= Push.Local.residual A B 0 (U i) (R n).p.threshold ((V n).bulk i); have ht:(p₀ n).2.1= Progress.DirectedRecipe.stuff X u:= rfl; rw [ht]; unfold u; rw [←(h n).price]
   have hu'(n): (p₁ n).2.1= Progress.DirectedRecipe.stuff X (Q₁ n):=by
      let u(i):= Push.Local.residual A B 0 (U i) (R' n).p.threshold ((W n).bulk i); have ht:(p₁ n).2.1= Progress.DirectedRecipe.stuff X u:= rfl; rw [ht]; unfold u; rw [←(hp n).price]
   simp_rw [hu,hu']; exact ((rebukes ht he).1).extendsE _ X hx -- function eq syntax
local notation "C"=> MergeProof.cram
include hv hg
lemma hexT: Credit (fun n=> profile (R n).activities (R₀ n).forced) (fun n=> profile (R' n).activities (R₁ n).forced):=by
    let p n:=profile (R n).activities (V n).forced; let q n:=profile (R' n).activities (W n).forced; let r n:= clipSum J (q₀ n); let r' n:= clipSum J (q₁ n)
    have hfK n : profile (R n).activities (R₀ n).forced= p n+ hook (R n).activities α (r n):=by
       obtain ⟨a,b,c,hc⟩:= (H n).wage; unfold r; rw [(h n).price]; exact budgetProfile ((K n).supply _) hc (H n).format ((h n).price ▸ ht) (hf n) S.sane
    have hfL n : profile (R' n).activities (R₁ n).forced= q n+ hook (R' n).activities α (r' n):=by
       obtain ⟨a,b,c,hc⟩:= (H' n).wage;unfold r'; rw [(hp n).price]; exact budgetProfile ((K' n).supply _) hc (H' n).format ((hp n).price ▸ ht) (hf' n) S.sane
    simp_rw [hfK,hfL]
    have hu:Credit p q:=by
        let K:=S.orient.activities
        have hv₁ n: barcode (R n).activities=barcode K:=by unfold barcode K; rw [←(h n).force]
        have hv₂ n: barcode (R' n).activities=barcode K:=by unfold barcode K; rw [←(hp n).force]
        unfold p q profile; simp_rw [hv₁,hv₂]; exact hv.sumT _
    apply Credit.sum hu; have ht :Credit r r':= ((rebukes ht he).2).sumT _
    let f p z (i:Box n) V:= r z p V*portion (R z).activities α p i V; let g p z(i:Box n) V:= r' z p V*portion (R' z).activities α p i V
    have hX (p) : Credit (f p) (g p):= Credit.funding fun k=> ((ht.pull ⟨fun _:Unit=> p,fun _ _ _=> Subsingleton.elim ..⟩).paired ((Base.flagsK h hg p k hp).logs))
    have hv:=Credit.hoop (f:=fun i j=> f j i) (g:=fun i j=>g j i) hX
    have hh n : ∑ j, f j n=hook (R n).activities α (r n):=by funext i U; simp only [Finset.sum_apply];rfl
    have hy n : ∑ j, g j n=hook (R' n).activities α (r' n):=by funext i U; simp only [Finset.sum_apply]; rfl
    simp_rw [hh,hy] at hv; exact hv
lemma carried {Z:Extra.Histories.StockTag n↪ℕ} (hZ:∀ n,cart (R:=R n) (K n)=Z)(hZ':∀ n, cart (R:=R' n) (K' n)=Z): Credit (fun n=>(p₀ n).2.2) (fun n=>(p₁ n).2.2) :=by
    let X(n):= profile (R n).activities (R₀ n).forced; let Y(n):= profile (R' n).activities (R₁ n).forced
    change Credit (fun n=> Function.extend _ (X n ∘ Subtype.val) 0) (fun n=>Function.extend _ (Y n ∘ Subtype.val) 0); simp_rw [hZ,hZ']; exact ((hexT h hp ht he hv hg hf hf' K K' H H').pull (Embedding.subtype _)).extendK Z
end Col
end YM.FullVolume.Paint
